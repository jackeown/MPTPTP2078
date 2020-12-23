%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:43 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  215 ( 486 expanded)
%              Number of leaves         :   42 ( 180 expanded)
%              Depth                    :   17
%              Number of atoms          : 1100 (3310 expanded)
%              Number of equality atoms :   39 ( 196 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f865,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f116,f121,f126,f131,f136,f141,f151,f161,f166,f193,f197,f295,f311,f318,f344,f364,f376,f396,f459,f473,f702,f711,f725,f827,f855,f864])).

fof(f864,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | spl6_7
    | ~ spl6_10
    | ~ spl6_78 ),
    inference(avatar_contradiction_clause,[],[f863])).

fof(f863,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_2
    | spl6_7
    | ~ spl6_10
    | ~ spl6_78 ),
    inference(subsumption_resolution,[],[f862,f115])).

fof(f115,plain,
    ( v2_pre_topc(sK0)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl6_1
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f862,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ spl6_2
    | spl6_7
    | ~ spl6_10
    | ~ spl6_78 ),
    inference(subsumption_resolution,[],[f861,f120])).

fof(f120,plain,
    ( l1_pre_topc(sK0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl6_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f861,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | spl6_7
    | ~ spl6_10
    | ~ spl6_78 ),
    inference(subsumption_resolution,[],[f860,f160])).

fof(f160,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f158])).

fof(f158,plain,
    ( spl6_10
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f860,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | spl6_7
    | ~ spl6_78 ),
    inference(subsumption_resolution,[],[f857,f145])).

fof(f145,plain,
    ( ~ v1_borsuk_1(sK1,sK0)
    | spl6_7 ),
    inference(avatar_component_clause,[],[f144])).

fof(f144,plain,
    ( spl6_7
  <=> v1_borsuk_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f857,plain,
    ( v1_borsuk_1(sK1,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl6_78 ),
    inference(resolution,[],[f854,f236])).

fof(f236,plain,(
    ! [X0,X1] :
      ( ~ v4_pre_topc(u1_struct_0(X1),X0)
      | v1_borsuk_1(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f107,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f107,plain,(
    ! [X0,X1] :
      ( v1_borsuk_1(X1,X0)
      | ~ v4_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( v1_borsuk_1(X1,X0)
      | ~ v4_pre_topc(X2,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
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
    inference(flattening,[],[f45])).

fof(f45,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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

fof(f854,plain,
    ( v4_pre_topc(u1_struct_0(sK1),sK0)
    | ~ spl6_78 ),
    inference(avatar_component_clause,[],[f852])).

fof(f852,plain,
    ( spl6_78
  <=> v4_pre_topc(u1_struct_0(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_78])])).

fof(f855,plain,
    ( spl6_78
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_60 ),
    inference(avatar_split_clause,[],[f846,f709,f153,f148,f118,f113,f852])).

fof(f148,plain,
    ( spl6_8
  <=> v1_borsuk_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f153,plain,
    ( spl6_9
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f709,plain,
    ( spl6_60
  <=> ! [X7] :
        ( v4_pre_topc(u1_struct_0(sK1),X7)
        | ~ m1_pre_topc(sK2,X7)
        | ~ v1_borsuk_1(sK2,X7)
        | ~ l1_pre_topc(X7)
        | ~ v2_pre_topc(X7) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_60])])).

fof(f846,plain,
    ( v4_pre_topc(u1_struct_0(sK1),sK0)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_60 ),
    inference(subsumption_resolution,[],[f845,f115])).

fof(f845,plain,
    ( v4_pre_topc(u1_struct_0(sK1),sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl6_2
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_60 ),
    inference(subsumption_resolution,[],[f844,f120])).

fof(f844,plain,
    ( v4_pre_topc(u1_struct_0(sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_60 ),
    inference(subsumption_resolution,[],[f843,f150])).

fof(f150,plain,
    ( v1_borsuk_1(sK2,sK0)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f148])).

fof(f843,plain,
    ( v4_pre_topc(u1_struct_0(sK1),sK0)
    | ~ v1_borsuk_1(sK2,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl6_9
    | ~ spl6_60 ),
    inference(resolution,[],[f710,f155])).

fof(f155,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f153])).

fof(f710,plain,
    ( ! [X7] :
        ( ~ m1_pre_topc(sK2,X7)
        | v4_pre_topc(u1_struct_0(sK1),X7)
        | ~ v1_borsuk_1(sK2,X7)
        | ~ l1_pre_topc(X7)
        | ~ v2_pre_topc(X7) )
    | ~ spl6_60 ),
    inference(avatar_component_clause,[],[f709])).

fof(f827,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | ~ spl6_7
    | spl6_8
    | ~ spl6_9
    | ~ spl6_61 ),
    inference(avatar_contradiction_clause,[],[f826])).

fof(f826,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_7
    | spl6_8
    | ~ spl6_9
    | ~ spl6_61 ),
    inference(subsumption_resolution,[],[f825,f146])).

fof(f146,plain,
    ( v1_borsuk_1(sK1,sK0)
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f144])).

fof(f825,plain,
    ( ~ v1_borsuk_1(sK1,sK0)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_8
    | ~ spl6_9
    | ~ spl6_61 ),
    inference(subsumption_resolution,[],[f824,f115])).

fof(f824,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ v1_borsuk_1(sK1,sK0)
    | ~ spl6_2
    | spl6_8
    | ~ spl6_9
    | ~ spl6_61 ),
    inference(subsumption_resolution,[],[f823,f120])).

fof(f823,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ v1_borsuk_1(sK1,sK0)
    | spl6_8
    | ~ spl6_9
    | ~ spl6_61 ),
    inference(subsumption_resolution,[],[f821,f155])).

fof(f821,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ v1_borsuk_1(sK1,sK0)
    | spl6_8
    | ~ spl6_61 ),
    inference(resolution,[],[f724,f149])).

fof(f149,plain,
    ( ~ v1_borsuk_1(sK2,sK0)
    | spl6_8 ),
    inference(avatar_component_clause,[],[f148])).

fof(f724,plain,
    ( ! [X0] :
        ( v1_borsuk_1(sK2,X0)
        | ~ m1_pre_topc(sK2,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | ~ v1_borsuk_1(sK1,X0) )
    | ~ spl6_61 ),
    inference(avatar_component_clause,[],[f723])).

fof(f723,plain,
    ( spl6_61
  <=> ! [X0] :
        ( v1_borsuk_1(sK2,X0)
        | ~ m1_pre_topc(sK2,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | ~ v1_borsuk_1(sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_61])])).

fof(f725,plain,
    ( spl6_61
    | ~ spl6_26
    | ~ spl6_58 ),
    inference(avatar_split_clause,[],[f715,f700,f362,f723])).

fof(f362,plain,
    ( spl6_26
  <=> ! [X0] :
        ( ~ m1_pre_topc(sK2,X0)
        | m1_pre_topc(sK1,X0)
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f700,plain,
    ( spl6_58
  <=> ! [X6] :
        ( ~ v4_pre_topc(u1_struct_0(sK1),X6)
        | v1_borsuk_1(sK2,X6)
        | ~ m1_pre_topc(sK2,X6)
        | ~ l1_pre_topc(X6)
        | ~ v2_pre_topc(X6) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_58])])).

fof(f715,plain,
    ( ! [X0] :
        ( v1_borsuk_1(sK2,X0)
        | ~ m1_pre_topc(sK2,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | ~ v1_borsuk_1(sK1,X0) )
    | ~ spl6_26
    | ~ spl6_58 ),
    inference(subsumption_resolution,[],[f714,f363])).

fof(f363,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK2,X0)
        | m1_pre_topc(sK1,X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl6_26 ),
    inference(avatar_component_clause,[],[f362])).

fof(f714,plain,
    ( ! [X0] :
        ( v1_borsuk_1(sK2,X0)
        | ~ m1_pre_topc(sK2,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | ~ m1_pre_topc(sK1,X0)
        | ~ v1_borsuk_1(sK1,X0) )
    | ~ spl6_58 ),
    inference(duplicate_literal_removal,[],[f713])).

fof(f713,plain,
    ( ! [X0] :
        ( v1_borsuk_1(sK2,X0)
        | ~ m1_pre_topc(sK2,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | ~ m1_pre_topc(sK1,X0)
        | ~ v1_borsuk_1(sK1,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl6_58 ),
    inference(resolution,[],[f701,f247])).

fof(f247,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_borsuk_1(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f111,f85])).

fof(f111,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_borsuk_1(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f108])).

fof(f108,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_borsuk_1(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( v4_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_borsuk_1(X1,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f701,plain,
    ( ! [X6] :
        ( ~ v4_pre_topc(u1_struct_0(sK1),X6)
        | v1_borsuk_1(sK2,X6)
        | ~ m1_pre_topc(sK2,X6)
        | ~ l1_pre_topc(X6)
        | ~ v2_pre_topc(X6) )
    | ~ spl6_58 ),
    inference(avatar_component_clause,[],[f700])).

fof(f711,plain,
    ( spl6_60
    | ~ spl6_22 ),
    inference(avatar_split_clause,[],[f511,f337,f709])).

fof(f337,plain,
    ( spl6_22
  <=> u1_struct_0(sK1) = u1_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f511,plain,
    ( ! [X7] :
        ( v4_pre_topc(u1_struct_0(sK1),X7)
        | ~ m1_pre_topc(sK2,X7)
        | ~ v1_borsuk_1(sK2,X7)
        | ~ l1_pre_topc(X7)
        | ~ v2_pre_topc(X7) )
    | ~ spl6_22 ),
    inference(superposition,[],[f247,f339])).

fof(f339,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK2)
    | ~ spl6_22 ),
    inference(avatar_component_clause,[],[f337])).

fof(f702,plain,
    ( spl6_58
    | ~ spl6_22 ),
    inference(avatar_split_clause,[],[f510,f337,f700])).

fof(f510,plain,
    ( ! [X6] :
        ( ~ v4_pre_topc(u1_struct_0(sK1),X6)
        | v1_borsuk_1(sK2,X6)
        | ~ m1_pre_topc(sK2,X6)
        | ~ l1_pre_topc(X6)
        | ~ v2_pre_topc(X6) )
    | ~ spl6_22 ),
    inference(superposition,[],[f236,f339])).

fof(f473,plain,
    ( spl6_23
    | ~ spl6_33 ),
    inference(avatar_split_clause,[],[f465,f456,f341])).

fof(f341,plain,
    ( spl6_23
  <=> r1_tarski(u1_struct_0(sK2),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f456,plain,
    ( spl6_33
  <=> m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).

fof(f465,plain,
    ( r1_tarski(u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ spl6_33 ),
    inference(resolution,[],[f458,f102])).

fof(f102,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f458,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl6_33 ),
    inference(avatar_component_clause,[],[f456])).

fof(f459,plain,
    ( spl6_33
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_27 ),
    inference(avatar_split_clause,[],[f406,f394,f138,f133,f456])).

fof(f133,plain,
    ( spl6_5
  <=> v2_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f138,plain,
    ( spl6_6
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f394,plain,
    ( spl6_27
  <=> ! [X1] :
        ( ~ v3_pre_topc(X1,sK2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
        | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f406,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_27 ),
    inference(subsumption_resolution,[],[f405,f135])).

fof(f135,plain,
    ( v2_pre_topc(sK2)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f133])).

fof(f405,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_pre_topc(sK2)
    | ~ spl6_6
    | ~ spl6_27 ),
    inference(subsumption_resolution,[],[f404,f140])).

fof(f140,plain,
    ( l1_pre_topc(sK2)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f138])).

fof(f404,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ spl6_27 ),
    inference(subsumption_resolution,[],[f402,f142])).

fof(f142,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f65,f64])).

fof(f64,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f65,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

% (17481)Refutation not found, incomplete strategy% (17481)------------------------------
% (17481)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f3,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

% (17481)Termination reason: Refutation not found, incomplete strategy

% (17481)Memory used [KB]: 1791
fof(f402,plain,
    ( ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ spl6_27 ),
    inference(resolution,[],[f395,f206])).

% (17481)Time elapsed: 0.094 s
% (17481)------------------------------
% (17481)------------------------------
fof(f206,plain,(
    ! [X0] :
      ( v3_pre_topc(u1_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f205,f142])).

fof(f205,plain,(
    ! [X0] :
      ( v3_pre_topc(u1_struct_0(X0),X0)
      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f204])).

fof(f204,plain,(
    ! [X0] :
      ( v3_pre_topc(u1_struct_0(X0),X0)
      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f89,f66])).

fof(f66,plain,(
    ! [X0] :
      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ( ( v2_pre_topc(X0)
          | ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),sK3(X0),sK4(X0)),u1_pre_topc(X0))
            & r2_hidden(sK4(X0),u1_pre_topc(X0))
            & r2_hidden(sK3(X0),u1_pre_topc(X0))
            & m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0)))
            & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))) )
          | ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK5(X0)),u1_pre_topc(X0))
            & r1_tarski(sK5(X0),u1_pre_topc(X0))
            & m1_subset_1(sK5(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        & ( ( ! [X4] :
                ( ! [X5] :
                    ( r2_hidden(k9_subset_1(u1_struct_0(X0),X4,X5),u1_pre_topc(X0))
                    | ~ r2_hidden(X5,u1_pre_topc(X0))
                    | ~ r2_hidden(X4,u1_pre_topc(X0))
                    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
            & ! [X6] :
                ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X6),u1_pre_topc(X0))
                | ~ r1_tarski(X6,u1_pre_topc(X0))
                | ~ m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
          | ~ v2_pre_topc(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f38,f41,f40,f39])).

fof(f39,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
              & r2_hidden(X2,u1_pre_topc(X0))
              & r2_hidden(X1,u1_pre_topc(X0))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),sK3(X0),X2),u1_pre_topc(X0))
            & r2_hidden(X2,u1_pre_topc(X0))
            & r2_hidden(sK3(X0),u1_pre_topc(X0))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0] :
      ( ? [X2] :
          ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),sK3(X0),X2),u1_pre_topc(X0))
          & r2_hidden(X2,u1_pre_topc(X0))
          & r2_hidden(sK3(X0),u1_pre_topc(X0))
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),sK3(X0),sK4(X0)),u1_pre_topc(X0))
        & r2_hidden(sK4(X0),u1_pre_topc(X0))
        & r2_hidden(sK3(X0),u1_pre_topc(X0))
        & m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0] :
      ( ? [X3] :
          ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
          & r1_tarski(X3,u1_pre_topc(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK5(X0)),u1_pre_topc(X0))
        & r1_tarski(sK5(X0),u1_pre_topc(X0))
        & m1_subset_1(sK5(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ( ( v2_pre_topc(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                  & r2_hidden(X2,u1_pre_topc(X0))
                  & r2_hidden(X1,u1_pre_topc(X0))
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          | ? [X3] :
              ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              & r1_tarski(X3,u1_pre_topc(X0))
              & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        & ( ( ! [X4] :
                ( ! [X5] :
                    ( r2_hidden(k9_subset_1(u1_struct_0(X0),X4,X5),u1_pre_topc(X0))
                    | ~ r2_hidden(X5,u1_pre_topc(X0))
                    | ~ r2_hidden(X4,u1_pre_topc(X0))
                    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
            & ! [X6] :
                ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X6),u1_pre_topc(X0))
                | ~ r1_tarski(X6,u1_pre_topc(X0))
                | ~ m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
          | ~ v2_pre_topc(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( ( v2_pre_topc(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                  & r2_hidden(X2,u1_pre_topc(X0))
                  & r2_hidden(X1,u1_pre_topc(X0))
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          | ? [X3] :
              ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              & r1_tarski(X3,u1_pre_topc(X0))
              & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        & ( ( ! [X1] :
                ( ! [X2] :
                    ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                    | ~ r2_hidden(X2,u1_pre_topc(X0))
                    | ~ r2_hidden(X1,u1_pre_topc(X0))
                    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
            & ! [X3] :
                ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
                | ~ r1_tarski(X3,u1_pre_topc(X0))
                | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
          | ~ v2_pre_topc(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ( ( v2_pre_topc(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                  & r2_hidden(X2,u1_pre_topc(X0))
                  & r2_hidden(X1,u1_pre_topc(X0))
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          | ? [X3] :
              ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              & r1_tarski(X3,u1_pre_topc(X0))
              & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        & ( ( ! [X1] :
                ( ! [X2] :
                    ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                    | ~ r2_hidden(X2,u1_pre_topc(X0))
                    | ~ r2_hidden(X1,u1_pre_topc(X0))
                    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
            & ! [X3] :
                ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
                | ~ r1_tarski(X3,u1_pre_topc(X0))
                | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
          | ~ v2_pre_topc(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( ! [X2] :
                  ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                  | ~ r2_hidden(X2,u1_pre_topc(X0))
                  | ~ r2_hidden(X1,u1_pre_topc(X0))
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( ! [X2] :
                  ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                  | ~ r2_hidden(X2,u1_pre_topc(X0))
                  | ~ r2_hidden(X1,u1_pre_topc(X0))
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r2_hidden(X2,u1_pre_topc(X0))
                      & r2_hidden(X1,u1_pre_topc(X0)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) ) ) )
          & ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( r1_tarski(X3,u1_pre_topc(X0))
               => r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) ) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) ) ) ),
    inference(rectify,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r2_hidden(X2,u1_pre_topc(X0))
                      & r2_hidden(X1,u1_pre_topc(X0)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) ) ) )
          & ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( r1_tarski(X1,u1_pre_topc(X0))
               => r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) ) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_pre_topc)).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,u1_pre_topc(X0))
      | v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) )
            & ( r2_hidden(X1,u1_pre_topc(X0))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).

fof(f395,plain,
    ( ! [X1] :
        ( ~ v3_pre_topc(X1,sK2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
        | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) )
    | ~ spl6_27 ),
    inference(avatar_component_clause,[],[f394])).

fof(f396,plain,
    ( spl6_27
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f334,f163,f128,f123,f394])).

fof(f123,plain,
    ( spl6_3
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f128,plain,
    ( spl6_4
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f163,plain,
    ( spl6_11
  <=> g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

% (17493)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% (17477)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% (17485)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
fof(f334,plain,
    ( ! [X1] :
        ( ~ v3_pre_topc(X1,sK2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
        | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) )
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_11 ),
    inference(forward_demodulation,[],[f333,f165])).

fof(f165,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = sK2
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f163])).

fof(f333,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ v3_pre_topc(X1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) )
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_11 ),
    inference(forward_demodulation,[],[f332,f165])).

fof(f332,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
        | ~ v3_pre_topc(X1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) )
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f329,f130])).

fof(f130,plain,
    ( l1_pre_topc(sK1)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f128])).

fof(f329,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
        | ~ v3_pre_topc(X1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ l1_pre_topc(sK1)
        | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) )
    | ~ spl6_3 ),
    inference(resolution,[],[f98,f125])).

fof(f125,plain,
    ( v2_pre_topc(sK1)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f123])).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
      | ~ v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v3_pre_topc(X1,X0) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            | ~ v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v3_pre_topc(X1,X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v3_pre_topc(X1,X0) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            | ~ v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v3_pre_topc(X1,X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v3_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v3_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v3_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_pre_topc)).

fof(f376,plain,
    ( ~ spl6_2
    | ~ spl6_9
    | spl6_10
    | ~ spl6_26 ),
    inference(avatar_contradiction_clause,[],[f375])).

fof(f375,plain,
    ( $false
    | ~ spl6_2
    | ~ spl6_9
    | spl6_10
    | ~ spl6_26 ),
    inference(subsumption_resolution,[],[f374,f120])).

fof(f374,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl6_9
    | spl6_10
    | ~ spl6_26 ),
    inference(subsumption_resolution,[],[f372,f159])).

fof(f159,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | spl6_10 ),
    inference(avatar_component_clause,[],[f158])).

fof(f372,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl6_9
    | ~ spl6_26 ),
    inference(resolution,[],[f363,f155])).

fof(f364,plain,
    ( spl6_26
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f360,f163,f133,f128,f123,f362])).

fof(f360,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK2,X0)
        | m1_pre_topc(sK1,X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_11 ),
    inference(subsumption_resolution,[],[f359,f125])).

fof(f359,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK2,X0)
        | ~ v2_pre_topc(sK1)
        | m1_pre_topc(sK1,X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_11 ),
    inference(subsumption_resolution,[],[f358,f130])).

fof(f358,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK2,X0)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | m1_pre_topc(sK1,X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl6_5
    | ~ spl6_11 ),
    inference(subsumption_resolution,[],[f357,f135])).

fof(f357,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(sK2)
        | ~ m1_pre_topc(sK2,X0)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | m1_pre_topc(sK1,X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl6_11 ),
    inference(superposition,[],[f352,f165])).

fof(f352,plain,(
    ! [X2,X0] :
      ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X0)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f105,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f105,plain,(
    ! [X2,X0] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X0)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  | ~ m1_pre_topc(X2,X0) )
                & ( m1_pre_topc(X2,X0)
                  | ~ m1_pre_topc(X1,X0) ) )
              | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(X1,X0)
              <=> m1_pre_topc(X2,X0) )
              | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(X1,X0)
              <=> m1_pre_topc(X2,X0) )
              | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( l1_pre_topc(X2)
                & v2_pre_topc(X2) )
             => ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X1
               => ( m1_pre_topc(X1,X0)
                <=> m1_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_tmap_1)).

fof(f344,plain,
    ( spl6_22
    | ~ spl6_23
    | ~ spl6_20 ),
    inference(avatar_split_clause,[],[f327,f283,f341,f337])).

fof(f283,plain,
    ( spl6_20
  <=> r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f327,plain,
    ( ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(sK1))
    | u1_struct_0(sK1) = u1_struct_0(sK2)
    | ~ spl6_20 ),
    inference(resolution,[],[f284,f101])).

fof(f101,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
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

fof(f284,plain,
    ( r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f283])).

fof(f318,plain,
    ( ~ spl6_17
    | spl6_20 ),
    inference(avatar_contradiction_clause,[],[f317])).

fof(f317,plain,
    ( $false
    | ~ spl6_17
    | spl6_20 ),
    inference(subsumption_resolution,[],[f315,f285])).

fof(f285,plain,
    ( ~ r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2))
    | spl6_20 ),
    inference(avatar_component_clause,[],[f283])).

fof(f315,plain,
    ( r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ spl6_17 ),
    inference(resolution,[],[f257,f102])).

fof(f257,plain,
    ( m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f256])).

fof(f256,plain,
    ( spl6_17
  <=> m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f311,plain,
    ( spl6_17
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_21 ),
    inference(avatar_split_clause,[],[f305,f293,f128,f123,f256])).

fof(f293,plain,
    ( spl6_21
  <=> ! [X0] :
        ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ v3_pre_topc(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f305,plain,
    ( m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_21 ),
    inference(subsumption_resolution,[],[f304,f125])).

fof(f304,plain,
    ( m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_pre_topc(sK1)
    | ~ spl6_4
    | ~ spl6_21 ),
    inference(subsumption_resolution,[],[f299,f130])).

fof(f299,plain,
    ( m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl6_21 ),
    inference(subsumption_resolution,[],[f298,f142])).

fof(f298,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl6_21 ),
    inference(resolution,[],[f294,f206])).

fof(f294,plain,
    ( ! [X0] :
        ( ~ v3_pre_topc(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) )
    | ~ spl6_21 ),
    inference(avatar_component_clause,[],[f293])).

fof(f295,plain,
    ( spl6_21
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f281,f163,f128,f123,f293])).

fof(f281,plain,
    ( ! [X0] :
        ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ v3_pre_topc(X0,sK1) )
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_11 ),
    inference(subsumption_resolution,[],[f280,f125])).

fof(f280,plain,
    ( ! [X0] :
        ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ v3_pre_topc(X0,sK1)
        | ~ v2_pre_topc(sK1) )
    | ~ spl6_4
    | ~ spl6_11 ),
    inference(subsumption_resolution,[],[f279,f130])).

fof(f279,plain,
    ( ! [X0] :
        ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ v3_pre_topc(X0,sK1)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1) )
    | ~ spl6_11 ),
    inference(superposition,[],[f96,f165])).

fof(f96,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f197,plain,
    ( ~ spl6_9
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f196,f158,f148,f144,f153])).

fof(f196,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f195,f146])).

fof(f195,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | ~ v1_borsuk_1(sK1,sK0)
    | ~ spl6_8
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f194,f160])).

fof(f194,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ v1_borsuk_1(sK1,sK0)
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f63,f150])).

fof(f63,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | ~ v1_borsuk_1(sK2,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ v1_borsuk_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( ( ~ m1_pre_topc(sK2,sK0)
      | ~ v1_borsuk_1(sK2,sK0)
      | ~ m1_pre_topc(sK1,sK0)
      | ~ v1_borsuk_1(sK1,sK0) )
    & ( ( m1_pre_topc(sK2,sK0)
        & v1_borsuk_1(sK2,sK0) )
      | ( m1_pre_topc(sK1,sK0)
        & v1_borsuk_1(sK1,sK0) ) )
    & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = sK2
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f31,f34,f33,f32])).

fof(f32,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ m1_pre_topc(X2,X0)
                  | ~ v1_borsuk_1(X2,X0)
                  | ~ m1_pre_topc(X1,X0)
                  | ~ v1_borsuk_1(X1,X0) )
                & ( ( m1_pre_topc(X2,X0)
                    & v1_borsuk_1(X2,X0) )
                  | ( m1_pre_topc(X1,X0)
                    & v1_borsuk_1(X1,X0) ) )
                & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
                & l1_pre_topc(X2)
                & v2_pre_topc(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_pre_topc(X2,sK0)
                | ~ v1_borsuk_1(X2,sK0)
                | ~ m1_pre_topc(X1,sK0)
                | ~ v1_borsuk_1(X1,sK0) )
              & ( ( m1_pre_topc(X2,sK0)
                  & v1_borsuk_1(X2,sK0) )
                | ( m1_pre_topc(X1,sK0)
                  & v1_borsuk_1(X1,sK0) ) )
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
              & l1_pre_topc(X2)
              & v2_pre_topc(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ~ m1_pre_topc(X2,sK0)
              | ~ v1_borsuk_1(X2,sK0)
              | ~ m1_pre_topc(X1,sK0)
              | ~ v1_borsuk_1(X1,sK0) )
            & ( ( m1_pre_topc(X2,sK0)
                & v1_borsuk_1(X2,sK0) )
              | ( m1_pre_topc(X1,sK0)
                & v1_borsuk_1(X1,sK0) ) )
            & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
            & l1_pre_topc(X2)
            & v2_pre_topc(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1) )
   => ( ? [X2] :
          ( ( ~ m1_pre_topc(X2,sK0)
            | ~ v1_borsuk_1(X2,sK0)
            | ~ m1_pre_topc(sK1,sK0)
            | ~ v1_borsuk_1(sK1,sK0) )
          & ( ( m1_pre_topc(X2,sK0)
              & v1_borsuk_1(X2,sK0) )
            | ( m1_pre_topc(sK1,sK0)
              & v1_borsuk_1(sK1,sK0) ) )
          & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = X2
          & l1_pre_topc(X2)
          & v2_pre_topc(X2) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X2] :
        ( ( ~ m1_pre_topc(X2,sK0)
          | ~ v1_borsuk_1(X2,sK0)
          | ~ m1_pre_topc(sK1,sK0)
          | ~ v1_borsuk_1(sK1,sK0) )
        & ( ( m1_pre_topc(X2,sK0)
            & v1_borsuk_1(X2,sK0) )
          | ( m1_pre_topc(sK1,sK0)
            & v1_borsuk_1(sK1,sK0) ) )
        & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = X2
        & l1_pre_topc(X2)
        & v2_pre_topc(X2) )
   => ( ( ~ m1_pre_topc(sK2,sK0)
        | ~ v1_borsuk_1(sK2,sK0)
        | ~ m1_pre_topc(sK1,sK0)
        | ~ v1_borsuk_1(sK1,sK0) )
      & ( ( m1_pre_topc(sK2,sK0)
          & v1_borsuk_1(sK2,sK0) )
        | ( m1_pre_topc(sK1,sK0)
          & v1_borsuk_1(sK1,sK0) ) )
      & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = sK2
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_pre_topc(X2,X0)
                | ~ v1_borsuk_1(X2,X0)
                | ~ m1_pre_topc(X1,X0)
                | ~ v1_borsuk_1(X1,X0) )
              & ( ( m1_pre_topc(X2,X0)
                  & v1_borsuk_1(X2,X0) )
                | ( m1_pre_topc(X1,X0)
                  & v1_borsuk_1(X1,X0) ) )
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
              & l1_pre_topc(X2)
              & v2_pre_topc(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_pre_topc(X2,X0)
                | ~ v1_borsuk_1(X2,X0)
                | ~ m1_pre_topc(X1,X0)
                | ~ v1_borsuk_1(X1,X0) )
              & ( ( m1_pre_topc(X2,X0)
                  & v1_borsuk_1(X2,X0) )
                | ( m1_pre_topc(X1,X0)
                  & v1_borsuk_1(X1,X0) ) )
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
              & l1_pre_topc(X2)
              & v2_pre_topc(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_borsuk_1(X1,X0) )
              <~> ( m1_pre_topc(X2,X0)
                  & v1_borsuk_1(X2,X0) ) )
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
              & l1_pre_topc(X2)
              & v2_pre_topc(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_borsuk_1(X1,X0) )
              <~> ( m1_pre_topc(X2,X0)
                  & v1_borsuk_1(X2,X0) ) )
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
              & l1_pre_topc(X2)
              & v2_pre_topc(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1) )
           => ! [X2] :
                ( ( l1_pre_topc(X2)
                  & v2_pre_topc(X2) )
               => ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
                 => ( ( m1_pre_topc(X1,X0)
                      & v1_borsuk_1(X1,X0) )
                  <=> ( m1_pre_topc(X2,X0)
                      & v1_borsuk_1(X2,X0) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( l1_pre_topc(X2)
                & v2_pre_topc(X2) )
             => ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
               => ( ( m1_pre_topc(X1,X0)
                    & v1_borsuk_1(X1,X0) )
                <=> ( m1_pre_topc(X2,X0)
                    & v1_borsuk_1(X2,X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_tmap_1)).

fof(f193,plain,
    ( ~ spl6_2
    | spl6_9
    | ~ spl6_10
    | ~ spl6_11 ),
    inference(avatar_contradiction_clause,[],[f192])).

fof(f192,plain,
    ( $false
    | ~ spl6_2
    | spl6_9
    | ~ spl6_10
    | ~ spl6_11 ),
    inference(subsumption_resolution,[],[f191,f154])).

% (17485)Refutation not found, incomplete strategy% (17485)------------------------------
% (17485)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (17485)Termination reason: Refutation not found, incomplete strategy

% (17485)Memory used [KB]: 10618
% (17485)Time elapsed: 0.109 s
% (17485)------------------------------
% (17485)------------------------------
fof(f154,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | spl6_9 ),
    inference(avatar_component_clause,[],[f153])).

fof(f191,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl6_2
    | ~ spl6_10
    | ~ spl6_11 ),
    inference(forward_demodulation,[],[f190,f165])).

fof(f190,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK0)
    | ~ spl6_2
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f189,f120])).

fof(f189,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl6_10 ),
    inference(resolution,[],[f87,f160])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
            & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
            & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_tmap_1)).

fof(f166,plain,(
    spl6_11 ),
    inference(avatar_split_clause,[],[f58,f163])).

fof(f58,plain,(
    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = sK2 ),
    inference(cnf_transformation,[],[f35])).

fof(f161,plain,
    ( spl6_10
    | spl6_9 ),
    inference(avatar_split_clause,[],[f62,f153,f158])).

fof(f62,plain,
    ( m1_pre_topc(sK2,sK0)
    | m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f151,plain,
    ( spl6_7
    | spl6_8 ),
    inference(avatar_split_clause,[],[f59,f148,f144])).

fof(f59,plain,
    ( v1_borsuk_1(sK2,sK0)
    | v1_borsuk_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f141,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f57,f138])).

fof(f57,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f136,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f56,f133])).

fof(f56,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f131,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f55,f128])).

fof(f55,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f126,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f54,f123])).

fof(f54,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f121,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f53,f118])).

fof(f53,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f116,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f52,f113])).

fof(f52,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:10:34 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.48  % (17475)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.49  % (17484)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.50  % (17480)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.50  % (17487)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.50  % (17487)Refutation not found, incomplete strategy% (17487)------------------------------
% 0.20/0.50  % (17487)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (17495)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.50  % (17481)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.50  % (17487)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (17487)Memory used [KB]: 6140
% 0.20/0.50  % (17487)Time elapsed: 0.065 s
% 0.20/0.50  % (17487)------------------------------
% 0.20/0.50  % (17487)------------------------------
% 0.20/0.51  % (17475)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f865,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(avatar_sat_refutation,[],[f116,f121,f126,f131,f136,f141,f151,f161,f166,f193,f197,f295,f311,f318,f344,f364,f376,f396,f459,f473,f702,f711,f725,f827,f855,f864])).
% 0.20/0.51  fof(f864,plain,(
% 0.20/0.51    ~spl6_1 | ~spl6_2 | spl6_7 | ~spl6_10 | ~spl6_78),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f863])).
% 0.20/0.51  fof(f863,plain,(
% 0.20/0.51    $false | (~spl6_1 | ~spl6_2 | spl6_7 | ~spl6_10 | ~spl6_78)),
% 0.20/0.51    inference(subsumption_resolution,[],[f862,f115])).
% 0.20/0.51  fof(f115,plain,(
% 0.20/0.51    v2_pre_topc(sK0) | ~spl6_1),
% 0.20/0.51    inference(avatar_component_clause,[],[f113])).
% 0.20/0.51  fof(f113,plain,(
% 0.20/0.51    spl6_1 <=> v2_pre_topc(sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.20/0.51  fof(f862,plain,(
% 0.20/0.51    ~v2_pre_topc(sK0) | (~spl6_2 | spl6_7 | ~spl6_10 | ~spl6_78)),
% 0.20/0.51    inference(subsumption_resolution,[],[f861,f120])).
% 0.20/0.51  fof(f120,plain,(
% 0.20/0.51    l1_pre_topc(sK0) | ~spl6_2),
% 0.20/0.51    inference(avatar_component_clause,[],[f118])).
% 0.20/0.51  fof(f118,plain,(
% 0.20/0.51    spl6_2 <=> l1_pre_topc(sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.20/0.51  fof(f861,plain,(
% 0.20/0.51    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (spl6_7 | ~spl6_10 | ~spl6_78)),
% 0.20/0.51    inference(subsumption_resolution,[],[f860,f160])).
% 0.20/0.51  fof(f160,plain,(
% 0.20/0.51    m1_pre_topc(sK1,sK0) | ~spl6_10),
% 0.20/0.51    inference(avatar_component_clause,[],[f158])).
% 0.20/0.51  fof(f158,plain,(
% 0.20/0.51    spl6_10 <=> m1_pre_topc(sK1,sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.20/0.51  fof(f860,plain,(
% 0.20/0.51    ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (spl6_7 | ~spl6_78)),
% 0.20/0.51    inference(subsumption_resolution,[],[f857,f145])).
% 0.20/0.51  fof(f145,plain,(
% 0.20/0.51    ~v1_borsuk_1(sK1,sK0) | spl6_7),
% 0.20/0.51    inference(avatar_component_clause,[],[f144])).
% 0.20/0.51  fof(f144,plain,(
% 0.20/0.51    spl6_7 <=> v1_borsuk_1(sK1,sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.20/0.51  fof(f857,plain,(
% 0.20/0.51    v1_borsuk_1(sK1,sK0) | ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~spl6_78),
% 0.20/0.51    inference(resolution,[],[f854,f236])).
% 0.20/0.51  fof(f236,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~v4_pre_topc(u1_struct_0(X1),X0) | v1_borsuk_1(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f107,f85])).
% 0.20/0.51  fof(f85,plain,(
% 0.20/0.51    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f21])).
% 0.20/0.51  fof(f21,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f12])).
% 0.20/0.51  fof(f12,axiom,(
% 0.20/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.20/0.51  fof(f107,plain,(
% 0.20/0.51    ( ! [X0,X1] : (v1_borsuk_1(X1,X0) | ~v4_pre_topc(u1_struct_0(X1),X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.51    inference(equality_resolution,[],[f93])).
% 0.20/0.51  fof(f93,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (v1_borsuk_1(X1,X0) | ~v4_pre_topc(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f46])).
% 0.20/0.51  fof(f46,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) | ~v4_pre_topc(X2,X0)) & (v4_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.51    inference(flattening,[],[f45])).
% 0.20/0.51  fof(f45,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) | ~v4_pre_topc(X2,X0)) & (v4_pre_topc(X2,X0) | (~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0)))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.51    inference(nnf_transformation,[],[f27])).
% 0.20/0.51  fof(f27,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) <=> v4_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.51    inference(flattening,[],[f26])).
% 0.20/0.51  fof(f26,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) <=> v4_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f10])).
% 0.20/0.51  fof(f10,axiom,(
% 0.20/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) <=> v4_pre_topc(X2,X0))))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_tsep_1)).
% 0.20/0.51  fof(f854,plain,(
% 0.20/0.51    v4_pre_topc(u1_struct_0(sK1),sK0) | ~spl6_78),
% 0.20/0.51    inference(avatar_component_clause,[],[f852])).
% 0.20/0.51  fof(f852,plain,(
% 0.20/0.51    spl6_78 <=> v4_pre_topc(u1_struct_0(sK1),sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_78])])).
% 0.20/0.51  fof(f855,plain,(
% 0.20/0.51    spl6_78 | ~spl6_1 | ~spl6_2 | ~spl6_8 | ~spl6_9 | ~spl6_60),
% 0.20/0.51    inference(avatar_split_clause,[],[f846,f709,f153,f148,f118,f113,f852])).
% 0.20/0.51  fof(f148,plain,(
% 0.20/0.51    spl6_8 <=> v1_borsuk_1(sK2,sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.20/0.51  fof(f153,plain,(
% 0.20/0.51    spl6_9 <=> m1_pre_topc(sK2,sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.20/0.51  fof(f709,plain,(
% 0.20/0.51    spl6_60 <=> ! [X7] : (v4_pre_topc(u1_struct_0(sK1),X7) | ~m1_pre_topc(sK2,X7) | ~v1_borsuk_1(sK2,X7) | ~l1_pre_topc(X7) | ~v2_pre_topc(X7))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_60])])).
% 0.20/0.51  fof(f846,plain,(
% 0.20/0.51    v4_pre_topc(u1_struct_0(sK1),sK0) | (~spl6_1 | ~spl6_2 | ~spl6_8 | ~spl6_9 | ~spl6_60)),
% 0.20/0.51    inference(subsumption_resolution,[],[f845,f115])).
% 0.20/0.51  fof(f845,plain,(
% 0.20/0.51    v4_pre_topc(u1_struct_0(sK1),sK0) | ~v2_pre_topc(sK0) | (~spl6_2 | ~spl6_8 | ~spl6_9 | ~spl6_60)),
% 0.20/0.51    inference(subsumption_resolution,[],[f844,f120])).
% 0.20/0.51  fof(f844,plain,(
% 0.20/0.51    v4_pre_topc(u1_struct_0(sK1),sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl6_8 | ~spl6_9 | ~spl6_60)),
% 0.20/0.51    inference(subsumption_resolution,[],[f843,f150])).
% 0.20/0.51  fof(f150,plain,(
% 0.20/0.51    v1_borsuk_1(sK2,sK0) | ~spl6_8),
% 0.20/0.51    inference(avatar_component_clause,[],[f148])).
% 0.20/0.51  fof(f843,plain,(
% 0.20/0.51    v4_pre_topc(u1_struct_0(sK1),sK0) | ~v1_borsuk_1(sK2,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl6_9 | ~spl6_60)),
% 0.20/0.51    inference(resolution,[],[f710,f155])).
% 0.20/0.51  fof(f155,plain,(
% 0.20/0.51    m1_pre_topc(sK2,sK0) | ~spl6_9),
% 0.20/0.51    inference(avatar_component_clause,[],[f153])).
% 0.20/0.51  fof(f710,plain,(
% 0.20/0.51    ( ! [X7] : (~m1_pre_topc(sK2,X7) | v4_pre_topc(u1_struct_0(sK1),X7) | ~v1_borsuk_1(sK2,X7) | ~l1_pre_topc(X7) | ~v2_pre_topc(X7)) ) | ~spl6_60),
% 0.20/0.51    inference(avatar_component_clause,[],[f709])).
% 0.20/0.51  fof(f827,plain,(
% 0.20/0.51    ~spl6_1 | ~spl6_2 | ~spl6_7 | spl6_8 | ~spl6_9 | ~spl6_61),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f826])).
% 0.20/0.51  fof(f826,plain,(
% 0.20/0.51    $false | (~spl6_1 | ~spl6_2 | ~spl6_7 | spl6_8 | ~spl6_9 | ~spl6_61)),
% 0.20/0.51    inference(subsumption_resolution,[],[f825,f146])).
% 0.20/0.51  fof(f146,plain,(
% 0.20/0.51    v1_borsuk_1(sK1,sK0) | ~spl6_7),
% 0.20/0.51    inference(avatar_component_clause,[],[f144])).
% 0.20/0.51  fof(f825,plain,(
% 0.20/0.51    ~v1_borsuk_1(sK1,sK0) | (~spl6_1 | ~spl6_2 | spl6_8 | ~spl6_9 | ~spl6_61)),
% 0.20/0.51    inference(subsumption_resolution,[],[f824,f115])).
% 0.20/0.51  fof(f824,plain,(
% 0.20/0.51    ~v2_pre_topc(sK0) | ~v1_borsuk_1(sK1,sK0) | (~spl6_2 | spl6_8 | ~spl6_9 | ~spl6_61)),
% 0.20/0.51    inference(subsumption_resolution,[],[f823,f120])).
% 0.20/0.51  fof(f823,plain,(
% 0.20/0.51    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~v1_borsuk_1(sK1,sK0) | (spl6_8 | ~spl6_9 | ~spl6_61)),
% 0.20/0.51    inference(subsumption_resolution,[],[f821,f155])).
% 0.20/0.51  fof(f821,plain,(
% 0.20/0.51    ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~v1_borsuk_1(sK1,sK0) | (spl6_8 | ~spl6_61)),
% 0.20/0.51    inference(resolution,[],[f724,f149])).
% 0.20/0.51  fof(f149,plain,(
% 0.20/0.51    ~v1_borsuk_1(sK2,sK0) | spl6_8),
% 0.20/0.51    inference(avatar_component_clause,[],[f148])).
% 0.20/0.51  fof(f724,plain,(
% 0.20/0.51    ( ! [X0] : (v1_borsuk_1(sK2,X0) | ~m1_pre_topc(sK2,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~v1_borsuk_1(sK1,X0)) ) | ~spl6_61),
% 0.20/0.51    inference(avatar_component_clause,[],[f723])).
% 0.20/0.51  fof(f723,plain,(
% 0.20/0.51    spl6_61 <=> ! [X0] : (v1_borsuk_1(sK2,X0) | ~m1_pre_topc(sK2,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~v1_borsuk_1(sK1,X0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_61])])).
% 0.20/0.51  fof(f725,plain,(
% 0.20/0.51    spl6_61 | ~spl6_26 | ~spl6_58),
% 0.20/0.51    inference(avatar_split_clause,[],[f715,f700,f362,f723])).
% 0.20/0.51  fof(f362,plain,(
% 0.20/0.51    spl6_26 <=> ! [X0] : (~m1_pre_topc(sK2,X0) | m1_pre_topc(sK1,X0) | ~l1_pre_topc(X0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).
% 0.20/0.51  fof(f700,plain,(
% 0.20/0.51    spl6_58 <=> ! [X6] : (~v4_pre_topc(u1_struct_0(sK1),X6) | v1_borsuk_1(sK2,X6) | ~m1_pre_topc(sK2,X6) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_58])])).
% 0.20/0.51  fof(f715,plain,(
% 0.20/0.51    ( ! [X0] : (v1_borsuk_1(sK2,X0) | ~m1_pre_topc(sK2,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~v1_borsuk_1(sK1,X0)) ) | (~spl6_26 | ~spl6_58)),
% 0.20/0.51    inference(subsumption_resolution,[],[f714,f363])).
% 0.20/0.51  fof(f363,plain,(
% 0.20/0.51    ( ! [X0] : (~m1_pre_topc(sK2,X0) | m1_pre_topc(sK1,X0) | ~l1_pre_topc(X0)) ) | ~spl6_26),
% 0.20/0.51    inference(avatar_component_clause,[],[f362])).
% 0.20/0.51  fof(f714,plain,(
% 0.20/0.51    ( ! [X0] : (v1_borsuk_1(sK2,X0) | ~m1_pre_topc(sK2,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~m1_pre_topc(sK1,X0) | ~v1_borsuk_1(sK1,X0)) ) | ~spl6_58),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f713])).
% 0.20/0.51  fof(f713,plain,(
% 0.20/0.51    ( ! [X0] : (v1_borsuk_1(sK2,X0) | ~m1_pre_topc(sK2,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~m1_pre_topc(sK1,X0) | ~v1_borsuk_1(sK1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | ~spl6_58),
% 0.20/0.51    inference(resolution,[],[f701,f247])).
% 0.20/0.51  fof(f247,plain,(
% 0.20/0.51    ( ! [X0,X1] : (v4_pre_topc(u1_struct_0(X1),X0) | ~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f111,f85])).
% 0.20/0.51  fof(f111,plain,(
% 0.20/0.51    ( ! [X0,X1] : (v4_pre_topc(u1_struct_0(X1),X0) | ~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f108])).
% 0.20/0.51  fof(f108,plain,(
% 0.20/0.51    ( ! [X0,X1] : (v4_pre_topc(u1_struct_0(X1),X0) | ~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.51    inference(equality_resolution,[],[f92])).
% 0.20/0.51  fof(f92,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (v4_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f46])).
% 0.20/0.51  fof(f701,plain,(
% 0.20/0.51    ( ! [X6] : (~v4_pre_topc(u1_struct_0(sK1),X6) | v1_borsuk_1(sK2,X6) | ~m1_pre_topc(sK2,X6) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6)) ) | ~spl6_58),
% 0.20/0.51    inference(avatar_component_clause,[],[f700])).
% 0.20/0.51  fof(f711,plain,(
% 0.20/0.51    spl6_60 | ~spl6_22),
% 0.20/0.51    inference(avatar_split_clause,[],[f511,f337,f709])).
% 0.20/0.51  fof(f337,plain,(
% 0.20/0.51    spl6_22 <=> u1_struct_0(sK1) = u1_struct_0(sK2)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).
% 0.20/0.51  fof(f511,plain,(
% 0.20/0.51    ( ! [X7] : (v4_pre_topc(u1_struct_0(sK1),X7) | ~m1_pre_topc(sK2,X7) | ~v1_borsuk_1(sK2,X7) | ~l1_pre_topc(X7) | ~v2_pre_topc(X7)) ) | ~spl6_22),
% 0.20/0.51    inference(superposition,[],[f247,f339])).
% 0.20/0.51  fof(f339,plain,(
% 0.20/0.51    u1_struct_0(sK1) = u1_struct_0(sK2) | ~spl6_22),
% 0.20/0.51    inference(avatar_component_clause,[],[f337])).
% 0.20/0.51  fof(f702,plain,(
% 0.20/0.51    spl6_58 | ~spl6_22),
% 0.20/0.51    inference(avatar_split_clause,[],[f510,f337,f700])).
% 0.20/0.51  fof(f510,plain,(
% 0.20/0.51    ( ! [X6] : (~v4_pre_topc(u1_struct_0(sK1),X6) | v1_borsuk_1(sK2,X6) | ~m1_pre_topc(sK2,X6) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6)) ) | ~spl6_22),
% 0.20/0.51    inference(superposition,[],[f236,f339])).
% 0.20/0.51  fof(f473,plain,(
% 0.20/0.51    spl6_23 | ~spl6_33),
% 0.20/0.51    inference(avatar_split_clause,[],[f465,f456,f341])).
% 0.20/0.51  fof(f341,plain,(
% 0.20/0.51    spl6_23 <=> r1_tarski(u1_struct_0(sK2),u1_struct_0(sK1))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).
% 0.20/0.51  fof(f456,plain,(
% 0.20/0.51    spl6_33 <=> m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).
% 0.20/0.51  fof(f465,plain,(
% 0.20/0.51    r1_tarski(u1_struct_0(sK2),u1_struct_0(sK1)) | ~spl6_33),
% 0.20/0.51    inference(resolution,[],[f458,f102])).
% 0.20/0.51  fof(f102,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f51])).
% 0.20/0.51  fof(f51,plain,(
% 0.20/0.51    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.20/0.51    inference(nnf_transformation,[],[f4])).
% 0.20/0.51  fof(f4,axiom,(
% 0.20/0.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.51  fof(f458,plain,(
% 0.20/0.51    m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) | ~spl6_33),
% 0.20/0.51    inference(avatar_component_clause,[],[f456])).
% 0.20/0.51  fof(f459,plain,(
% 0.20/0.51    spl6_33 | ~spl6_5 | ~spl6_6 | ~spl6_27),
% 0.20/0.51    inference(avatar_split_clause,[],[f406,f394,f138,f133,f456])).
% 0.20/0.51  fof(f133,plain,(
% 0.20/0.51    spl6_5 <=> v2_pre_topc(sK2)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.20/0.51  fof(f138,plain,(
% 0.20/0.51    spl6_6 <=> l1_pre_topc(sK2)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.20/0.51  fof(f394,plain,(
% 0.20/0.51    spl6_27 <=> ! [X1] : (~v3_pre_topc(X1,sK2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).
% 0.20/0.51  fof(f406,plain,(
% 0.20/0.51    m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) | (~spl6_5 | ~spl6_6 | ~spl6_27)),
% 0.20/0.51    inference(subsumption_resolution,[],[f405,f135])).
% 0.20/0.51  fof(f135,plain,(
% 0.20/0.51    v2_pre_topc(sK2) | ~spl6_5),
% 0.20/0.51    inference(avatar_component_clause,[],[f133])).
% 0.20/0.51  fof(f405,plain,(
% 0.20/0.51    m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) | ~v2_pre_topc(sK2) | (~spl6_6 | ~spl6_27)),
% 0.20/0.51    inference(subsumption_resolution,[],[f404,f140])).
% 0.20/0.51  fof(f140,plain,(
% 0.20/0.51    l1_pre_topc(sK2) | ~spl6_6),
% 0.20/0.51    inference(avatar_component_clause,[],[f138])).
% 0.20/0.51  fof(f404,plain,(
% 0.20/0.51    m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | ~spl6_27),
% 0.20/0.51    inference(subsumption_resolution,[],[f402,f142])).
% 0.20/0.51  fof(f142,plain,(
% 0.20/0.51    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.20/0.51    inference(forward_demodulation,[],[f65,f64])).
% 0.20/0.51  fof(f64,plain,(
% 0.20/0.51    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.20/0.51    inference(cnf_transformation,[],[f2])).
% 0.20/0.51  fof(f2,axiom,(
% 0.20/0.51    ! [X0] : k2_subset_1(X0) = X0),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 0.20/0.51  fof(f65,plain,(
% 0.20/0.51    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f3])).
% 0.20/0.51  % (17481)Refutation not found, incomplete strategy% (17481)------------------------------
% 0.20/0.51  % (17481)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  fof(f3,axiom,(
% 0.20/0.51    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.20/0.51  % (17481)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (17481)Memory used [KB]: 1791
% 0.20/0.51  fof(f402,plain,(
% 0.20/0.51    ~m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | ~spl6_27),
% 0.20/0.51    inference(resolution,[],[f395,f206])).
% 0.20/0.51  % (17481)Time elapsed: 0.094 s
% 0.20/0.51  % (17481)------------------------------
% 0.20/0.51  % (17481)------------------------------
% 0.20/0.51  fof(f206,plain,(
% 0.20/0.51    ( ! [X0] : (v3_pre_topc(u1_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f205,f142])).
% 0.20/0.51  fof(f205,plain,(
% 0.20/0.51    ( ! [X0] : (v3_pre_topc(u1_struct_0(X0),X0) | ~m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f204])).
% 0.20/0.51  fof(f204,plain,(
% 0.20/0.51    ( ! [X0] : (v3_pre_topc(u1_struct_0(X0),X0) | ~m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.51    inference(resolution,[],[f89,f66])).
% 0.20/0.51  fof(f66,plain,(
% 0.20/0.51    ( ! [X0] : (r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f42])).
% 0.20/0.51  fof(f42,plain,(
% 0.20/0.51    ! [X0] : (((v2_pre_topc(X0) | ((~r2_hidden(k9_subset_1(u1_struct_0(X0),sK3(X0),sK4(X0)),u1_pre_topc(X0)) & r2_hidden(sK4(X0),u1_pre_topc(X0)) & r2_hidden(sK3(X0),u1_pre_topc(X0)) & m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))) | (~r2_hidden(k5_setfam_1(u1_struct_0(X0),sK5(X0)),u1_pre_topc(X0)) & r1_tarski(sK5(X0),u1_pre_topc(X0)) & m1_subset_1(sK5(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((! [X4] : (! [X5] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X4,X5),u1_pre_topc(X0)) | ~r2_hidden(X5,u1_pre_topc(X0)) | ~r2_hidden(X4,u1_pre_topc(X0)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X6] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X6),u1_pre_topc(X0)) | ~r1_tarski(X6,u1_pre_topc(X0)) | ~m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f38,f41,f40,f39])).
% 0.20/0.51  fof(f39,plain,(
% 0.20/0.51    ! [X0] : (? [X1] : (? [X2] : (~r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) & r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (~r2_hidden(k9_subset_1(u1_struct_0(X0),sK3(X0),X2),u1_pre_topc(X0)) & r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(sK3(X0),u1_pre_topc(X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f40,plain,(
% 0.20/0.51    ! [X0] : (? [X2] : (~r2_hidden(k9_subset_1(u1_struct_0(X0),sK3(X0),X2),u1_pre_topc(X0)) & r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(sK3(X0),u1_pre_topc(X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~r2_hidden(k9_subset_1(u1_struct_0(X0),sK3(X0),sK4(X0)),u1_pre_topc(X0)) & r2_hidden(sK4(X0),u1_pre_topc(X0)) & r2_hidden(sK3(X0),u1_pre_topc(X0)) & m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f41,plain,(
% 0.20/0.51    ! [X0] : (? [X3] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) & r1_tarski(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (~r2_hidden(k5_setfam_1(u1_struct_0(X0),sK5(X0)),u1_pre_topc(X0)) & r1_tarski(sK5(X0),u1_pre_topc(X0)) & m1_subset_1(sK5(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f38,plain,(
% 0.20/0.51    ! [X0] : (((v2_pre_topc(X0) | ? [X1] : (? [X2] : (~r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) & r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ? [X3] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) & r1_tarski(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((! [X4] : (! [X5] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X4,X5),u1_pre_topc(X0)) | ~r2_hidden(X5,u1_pre_topc(X0)) | ~r2_hidden(X4,u1_pre_topc(X0)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X6] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X6),u1_pre_topc(X0)) | ~r1_tarski(X6,u1_pre_topc(X0)) | ~m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 0.20/0.51    inference(rectify,[],[f37])).
% 0.20/0.51  fof(f37,plain,(
% 0.20/0.51    ! [X0] : (((v2_pre_topc(X0) | ? [X1] : (? [X2] : (~r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) & r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ? [X3] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) & r1_tarski(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 0.20/0.51    inference(flattening,[],[f36])).
% 0.20/0.51  fof(f36,plain,(
% 0.20/0.51    ! [X0] : (((v2_pre_topc(X0) | (? [X1] : (? [X2] : (~r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) & r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ? [X3] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) & r1_tarski(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) & ((! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 0.20/0.51    inference(nnf_transformation,[],[f19])).
% 0.20/0.51  fof(f19,plain,(
% 0.20/0.51    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.51    inference(flattening,[],[f18])).
% 0.20/0.51  fof(f18,plain,(
% 0.20/0.51    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : ((r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | (~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : ((r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f15])).
% 0.20/0.51  fof(f15,plain,(
% 0.20/0.51    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X3,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 0.20/0.51    inference(rectify,[],[f5])).
% 0.20/0.51  fof(f5,axiom,(
% 0.20/0.51    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X1,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_pre_topc)).
% 0.20/0.51  fof(f89,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r2_hidden(X1,u1_pre_topc(X0)) | v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f43])).
% 0.20/0.51  fof(f43,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0))) & (r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.51    inference(nnf_transformation,[],[f23])).
% 0.20/0.51  fof(f23,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f6])).
% 0.20/0.51  fof(f6,axiom,(
% 0.20/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0)))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).
% 0.20/0.51  fof(f395,plain,(
% 0.20/0.51    ( ! [X1] : (~v3_pre_topc(X1,sK2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))) ) | ~spl6_27),
% 0.20/0.51    inference(avatar_component_clause,[],[f394])).
% 0.20/0.51  fof(f396,plain,(
% 0.20/0.51    spl6_27 | ~spl6_3 | ~spl6_4 | ~spl6_11),
% 0.20/0.51    inference(avatar_split_clause,[],[f334,f163,f128,f123,f394])).
% 0.20/0.51  fof(f123,plain,(
% 0.20/0.51    spl6_3 <=> v2_pre_topc(sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.20/0.51  fof(f128,plain,(
% 0.20/0.51    spl6_4 <=> l1_pre_topc(sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.20/0.51  fof(f163,plain,(
% 0.20/0.51    spl6_11 <=> g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = sK2),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.20/0.51  % (17493)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.51  % (17477)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.52  % (17485)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.52  fof(f334,plain,(
% 0.20/0.52    ( ! [X1] : (~v3_pre_topc(X1,sK2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))) ) | (~spl6_3 | ~spl6_4 | ~spl6_11)),
% 0.20/0.52    inference(forward_demodulation,[],[f333,f165])).
% 0.20/0.52  fof(f165,plain,(
% 0.20/0.52    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = sK2 | ~spl6_11),
% 0.20/0.52    inference(avatar_component_clause,[],[f163])).
% 0.20/0.52  fof(f333,plain,(
% 0.20/0.52    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) | ~v3_pre_topc(X1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))) ) | (~spl6_3 | ~spl6_4 | ~spl6_11)),
% 0.20/0.52    inference(forward_demodulation,[],[f332,f165])).
% 0.20/0.52  fof(f332,plain,(
% 0.20/0.52    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) | ~v3_pre_topc(X1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))) ) | (~spl6_3 | ~spl6_4)),
% 0.20/0.52    inference(subsumption_resolution,[],[f329,f130])).
% 0.20/0.52  fof(f130,plain,(
% 0.20/0.52    l1_pre_topc(sK1) | ~spl6_4),
% 0.20/0.52    inference(avatar_component_clause,[],[f128])).
% 0.20/0.52  fof(f329,plain,(
% 0.20/0.52    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) | ~v3_pre_topc(X1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK1) | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))) ) | ~spl6_3),
% 0.20/0.52    inference(resolution,[],[f98,f125])).
% 0.20/0.52  fof(f125,plain,(
% 0.20/0.52    v2_pre_topc(sK1) | ~spl6_3),
% 0.20/0.52    inference(avatar_component_clause,[],[f123])).
% 0.20/0.52  fof(f98,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f48])).
% 0.20/0.52  fof(f48,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.52    inference(flattening,[],[f47])).
% 0.20/0.52  fof(f47,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.52    inference(nnf_transformation,[],[f29])).
% 0.20/0.52  fof(f29,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.52    inference(flattening,[],[f28])).
% 0.20/0.52  fof(f28,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f8])).
% 0.20/0.52  fof(f8,axiom,(
% 0.20/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_pre_topc)).
% 0.20/0.52  fof(f376,plain,(
% 0.20/0.52    ~spl6_2 | ~spl6_9 | spl6_10 | ~spl6_26),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f375])).
% 0.20/0.52  fof(f375,plain,(
% 0.20/0.52    $false | (~spl6_2 | ~spl6_9 | spl6_10 | ~spl6_26)),
% 0.20/0.52    inference(subsumption_resolution,[],[f374,f120])).
% 0.20/0.52  fof(f374,plain,(
% 0.20/0.52    ~l1_pre_topc(sK0) | (~spl6_9 | spl6_10 | ~spl6_26)),
% 0.20/0.52    inference(subsumption_resolution,[],[f372,f159])).
% 0.20/0.52  fof(f159,plain,(
% 0.20/0.52    ~m1_pre_topc(sK1,sK0) | spl6_10),
% 0.20/0.52    inference(avatar_component_clause,[],[f158])).
% 0.20/0.52  fof(f372,plain,(
% 0.20/0.52    m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | (~spl6_9 | ~spl6_26)),
% 0.20/0.52    inference(resolution,[],[f363,f155])).
% 0.20/0.52  fof(f364,plain,(
% 0.20/0.52    spl6_26 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_11),
% 0.20/0.52    inference(avatar_split_clause,[],[f360,f163,f133,f128,f123,f362])).
% 0.20/0.52  fof(f360,plain,(
% 0.20/0.52    ( ! [X0] : (~m1_pre_topc(sK2,X0) | m1_pre_topc(sK1,X0) | ~l1_pre_topc(X0)) ) | (~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_11)),
% 0.20/0.52    inference(subsumption_resolution,[],[f359,f125])).
% 0.20/0.52  fof(f359,plain,(
% 0.20/0.52    ( ! [X0] : (~m1_pre_topc(sK2,X0) | ~v2_pre_topc(sK1) | m1_pre_topc(sK1,X0) | ~l1_pre_topc(X0)) ) | (~spl6_4 | ~spl6_5 | ~spl6_11)),
% 0.20/0.52    inference(subsumption_resolution,[],[f358,f130])).
% 0.20/0.52  fof(f358,plain,(
% 0.20/0.52    ( ! [X0] : (~m1_pre_topc(sK2,X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | m1_pre_topc(sK1,X0) | ~l1_pre_topc(X0)) ) | (~spl6_5 | ~spl6_11)),
% 0.20/0.52    inference(subsumption_resolution,[],[f357,f135])).
% 0.20/0.52  fof(f357,plain,(
% 0.20/0.52    ( ! [X0] : (~v2_pre_topc(sK2) | ~m1_pre_topc(sK2,X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | m1_pre_topc(sK1,X0) | ~l1_pre_topc(X0)) ) | ~spl6_11),
% 0.20/0.52    inference(superposition,[],[f352,f165])).
% 0.20/0.52  fof(f352,plain,(
% 0.20/0.52    ( ! [X2,X0] : (~v2_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | ~m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X0) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | m1_pre_topc(X2,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f105,f84])).
% 0.20/0.52  fof(f84,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f20])).
% 0.20/0.52  fof(f20,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f7])).
% 0.20/0.52  fof(f7,axiom,(
% 0.20/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.20/0.52  fof(f105,plain,(
% 0.20/0.52    ( ! [X2,X0] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X0) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | ~l1_pre_topc(X0)) )),
% 0.20/0.52    inference(equality_resolution,[],[f90])).
% 0.20/0.52  fof(f90,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f44])).
% 0.20/0.52  fof(f44,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0)) & (m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0))) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.20/0.52    inference(nnf_transformation,[],[f25])).
% 0.20/0.52  fof(f25,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (! [X2] : ((m1_pre_topc(X1,X0) <=> m1_pre_topc(X2,X0)) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.20/0.52    inference(flattening,[],[f24])).
% 0.20/0.52  fof(f24,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) <=> m1_pre_topc(X2,X0)) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1) | (~l1_pre_topc(X2) | ~v2_pre_topc(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | ~l1_pre_topc(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f11])).
% 0.20/0.52  fof(f11,axiom,(
% 0.20/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X1 => (m1_pre_topc(X1,X0) <=> m1_pre_topc(X2,X0))))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_tmap_1)).
% 0.20/0.52  fof(f344,plain,(
% 0.20/0.52    spl6_22 | ~spl6_23 | ~spl6_20),
% 0.20/0.52    inference(avatar_split_clause,[],[f327,f283,f341,f337])).
% 0.20/0.52  fof(f283,plain,(
% 0.20/0.52    spl6_20 <=> r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).
% 0.20/0.52  fof(f327,plain,(
% 0.20/0.52    ~r1_tarski(u1_struct_0(sK2),u1_struct_0(sK1)) | u1_struct_0(sK1) = u1_struct_0(sK2) | ~spl6_20),
% 0.20/0.52    inference(resolution,[],[f284,f101])).
% 0.20/0.52  fof(f101,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.20/0.52    inference(cnf_transformation,[],[f50])).
% 0.20/0.52  fof(f50,plain,(
% 0.20/0.52    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.52    inference(flattening,[],[f49])).
% 0.20/0.52  fof(f49,plain,(
% 0.20/0.52    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.52    inference(nnf_transformation,[],[f1])).
% 0.20/0.52  fof(f1,axiom,(
% 0.20/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.52  fof(f284,plain,(
% 0.20/0.52    r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2)) | ~spl6_20),
% 0.20/0.52    inference(avatar_component_clause,[],[f283])).
% 0.20/0.52  fof(f318,plain,(
% 0.20/0.52    ~spl6_17 | spl6_20),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f317])).
% 0.20/0.52  fof(f317,plain,(
% 0.20/0.52    $false | (~spl6_17 | spl6_20)),
% 0.20/0.52    inference(subsumption_resolution,[],[f315,f285])).
% 0.20/0.52  fof(f285,plain,(
% 0.20/0.52    ~r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2)) | spl6_20),
% 0.20/0.52    inference(avatar_component_clause,[],[f283])).
% 0.20/0.52  fof(f315,plain,(
% 0.20/0.52    r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2)) | ~spl6_17),
% 0.20/0.52    inference(resolution,[],[f257,f102])).
% 0.20/0.52  fof(f257,plain,(
% 0.20/0.52    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK2))) | ~spl6_17),
% 0.20/0.52    inference(avatar_component_clause,[],[f256])).
% 0.20/0.52  fof(f256,plain,(
% 0.20/0.52    spl6_17 <=> m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 0.20/0.52  fof(f311,plain,(
% 0.20/0.52    spl6_17 | ~spl6_3 | ~spl6_4 | ~spl6_21),
% 0.20/0.52    inference(avatar_split_clause,[],[f305,f293,f128,f123,f256])).
% 0.20/0.52  fof(f293,plain,(
% 0.20/0.52    spl6_21 <=> ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~v3_pre_topc(X0,sK1))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).
% 0.20/0.52  fof(f305,plain,(
% 0.20/0.52    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK2))) | (~spl6_3 | ~spl6_4 | ~spl6_21)),
% 0.20/0.52    inference(subsumption_resolution,[],[f304,f125])).
% 0.20/0.52  fof(f304,plain,(
% 0.20/0.52    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK2))) | ~v2_pre_topc(sK1) | (~spl6_4 | ~spl6_21)),
% 0.20/0.52    inference(subsumption_resolution,[],[f299,f130])).
% 0.20/0.52  fof(f299,plain,(
% 0.20/0.52    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~spl6_21),
% 0.20/0.52    inference(subsumption_resolution,[],[f298,f142])).
% 0.20/0.52  fof(f298,plain,(
% 0.20/0.52    ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~spl6_21),
% 0.20/0.52    inference(resolution,[],[f294,f206])).
% 0.20/0.52  fof(f294,plain,(
% 0.20/0.52    ( ! [X0] : (~v3_pre_topc(X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))) ) | ~spl6_21),
% 0.20/0.52    inference(avatar_component_clause,[],[f293])).
% 0.20/0.52  fof(f295,plain,(
% 0.20/0.52    spl6_21 | ~spl6_3 | ~spl6_4 | ~spl6_11),
% 0.20/0.52    inference(avatar_split_clause,[],[f281,f163,f128,f123,f293])).
% 0.20/0.52  fof(f281,plain,(
% 0.20/0.52    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~v3_pre_topc(X0,sK1)) ) | (~spl6_3 | ~spl6_4 | ~spl6_11)),
% 0.20/0.52    inference(subsumption_resolution,[],[f280,f125])).
% 0.20/0.52  fof(f280,plain,(
% 0.20/0.52    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~v3_pre_topc(X0,sK1) | ~v2_pre_topc(sK1)) ) | (~spl6_4 | ~spl6_11)),
% 0.20/0.52    inference(subsumption_resolution,[],[f279,f130])).
% 0.20/0.52  fof(f279,plain,(
% 0.20/0.52    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~v3_pre_topc(X0,sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1)) ) | ~spl6_11),
% 0.20/0.52    inference(superposition,[],[f96,f165])).
% 0.20/0.52  fof(f96,plain,(
% 0.20/0.52    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f48])).
% 0.20/0.52  fof(f197,plain,(
% 0.20/0.52    ~spl6_9 | ~spl6_7 | ~spl6_8 | ~spl6_10),
% 0.20/0.52    inference(avatar_split_clause,[],[f196,f158,f148,f144,f153])).
% 0.20/0.52  fof(f196,plain,(
% 0.20/0.52    ~m1_pre_topc(sK2,sK0) | (~spl6_7 | ~spl6_8 | ~spl6_10)),
% 0.20/0.52    inference(subsumption_resolution,[],[f195,f146])).
% 0.20/0.52  fof(f195,plain,(
% 0.20/0.52    ~m1_pre_topc(sK2,sK0) | ~v1_borsuk_1(sK1,sK0) | (~spl6_8 | ~spl6_10)),
% 0.20/0.52    inference(subsumption_resolution,[],[f194,f160])).
% 0.20/0.52  fof(f194,plain,(
% 0.20/0.52    ~m1_pre_topc(sK2,sK0) | ~m1_pre_topc(sK1,sK0) | ~v1_borsuk_1(sK1,sK0) | ~spl6_8),
% 0.20/0.52    inference(subsumption_resolution,[],[f63,f150])).
% 0.20/0.52  fof(f63,plain,(
% 0.20/0.52    ~m1_pre_topc(sK2,sK0) | ~v1_borsuk_1(sK2,sK0) | ~m1_pre_topc(sK1,sK0) | ~v1_borsuk_1(sK1,sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f35])).
% 0.20/0.52  fof(f35,plain,(
% 0.20/0.52    (((~m1_pre_topc(sK2,sK0) | ~v1_borsuk_1(sK2,sK0) | ~m1_pre_topc(sK1,sK0) | ~v1_borsuk_1(sK1,sK0)) & ((m1_pre_topc(sK2,sK0) & v1_borsuk_1(sK2,sK0)) | (m1_pre_topc(sK1,sK0) & v1_borsuk_1(sK1,sK0))) & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = sK2 & l1_pre_topc(sK2) & v2_pre_topc(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f31,f34,f33,f32])).
% 0.20/0.52  fof(f32,plain,(
% 0.20/0.52    ? [X0] : (? [X1] : (? [X2] : ((~m1_pre_topc(X2,X0) | ~v1_borsuk_1(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0)) & ((m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0)) | (m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : ((~m1_pre_topc(X2,sK0) | ~v1_borsuk_1(X2,sK0) | ~m1_pre_topc(X1,sK0) | ~v1_borsuk_1(X1,sK0)) & ((m1_pre_topc(X2,sK0) & v1_borsuk_1(X2,sK0)) | (m1_pre_topc(X1,sK0) & v1_borsuk_1(X1,sK0))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f33,plain,(
% 0.20/0.52    ? [X1] : (? [X2] : ((~m1_pre_topc(X2,sK0) | ~v1_borsuk_1(X2,sK0) | ~m1_pre_topc(X1,sK0) | ~v1_borsuk_1(X1,sK0)) & ((m1_pre_topc(X2,sK0) & v1_borsuk_1(X2,sK0)) | (m1_pre_topc(X1,sK0) & v1_borsuk_1(X1,sK0))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) => (? [X2] : ((~m1_pre_topc(X2,sK0) | ~v1_borsuk_1(X2,sK0) | ~m1_pre_topc(sK1,sK0) | ~v1_borsuk_1(sK1,sK0)) & ((m1_pre_topc(X2,sK0) & v1_borsuk_1(X2,sK0)) | (m1_pre_topc(sK1,sK0) & v1_borsuk_1(sK1,sK0))) & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f34,plain,(
% 0.20/0.52    ? [X2] : ((~m1_pre_topc(X2,sK0) | ~v1_borsuk_1(X2,sK0) | ~m1_pre_topc(sK1,sK0) | ~v1_borsuk_1(sK1,sK0)) & ((m1_pre_topc(X2,sK0) & v1_borsuk_1(X2,sK0)) | (m1_pre_topc(sK1,sK0) & v1_borsuk_1(sK1,sK0))) & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) => ((~m1_pre_topc(sK2,sK0) | ~v1_borsuk_1(sK2,sK0) | ~m1_pre_topc(sK1,sK0) | ~v1_borsuk_1(sK1,sK0)) & ((m1_pre_topc(sK2,sK0) & v1_borsuk_1(sK2,sK0)) | (m1_pre_topc(sK1,sK0) & v1_borsuk_1(sK1,sK0))) & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = sK2 & l1_pre_topc(sK2) & v2_pre_topc(sK2))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f31,plain,(
% 0.20/0.52    ? [X0] : (? [X1] : (? [X2] : ((~m1_pre_topc(X2,X0) | ~v1_borsuk_1(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0)) & ((m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0)) | (m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.20/0.52    inference(flattening,[],[f30])).
% 0.20/0.52  fof(f30,plain,(
% 0.20/0.52    ? [X0] : (? [X1] : (? [X2] : ((((~m1_pre_topc(X2,X0) | ~v1_borsuk_1(X2,X0)) | (~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0))) & ((m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0)) | (m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.20/0.52    inference(nnf_transformation,[],[f17])).
% 0.20/0.52  fof(f17,plain,(
% 0.20/0.52    ? [X0] : (? [X1] : (? [X2] : (((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) <~> (m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.20/0.52    inference(flattening,[],[f16])).
% 0.20/0.52  fof(f16,plain,(
% 0.20/0.52    ? [X0] : (? [X1] : (? [X2] : ((((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) <~> (m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2) & (l1_pre_topc(X2) & v2_pre_topc(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f14])).
% 0.20/0.52  fof(f14,negated_conjecture,(
% 0.20/0.52    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2)) => (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 => ((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) <=> (m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0)))))))),
% 0.20/0.52    inference(negated_conjecture,[],[f13])).
% 0.20/0.52  fof(f13,conjecture,(
% 0.20/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2)) => (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 => ((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) <=> (m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0)))))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_tmap_1)).
% 0.20/0.52  fof(f193,plain,(
% 0.20/0.52    ~spl6_2 | spl6_9 | ~spl6_10 | ~spl6_11),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f192])).
% 0.20/0.52  fof(f192,plain,(
% 0.20/0.52    $false | (~spl6_2 | spl6_9 | ~spl6_10 | ~spl6_11)),
% 0.20/0.52    inference(subsumption_resolution,[],[f191,f154])).
% 0.20/0.52  % (17485)Refutation not found, incomplete strategy% (17485)------------------------------
% 0.20/0.52  % (17485)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (17485)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (17485)Memory used [KB]: 10618
% 0.20/0.52  % (17485)Time elapsed: 0.109 s
% 0.20/0.52  % (17485)------------------------------
% 0.20/0.52  % (17485)------------------------------
% 0.20/0.52  fof(f154,plain,(
% 0.20/0.52    ~m1_pre_topc(sK2,sK0) | spl6_9),
% 0.20/0.52    inference(avatar_component_clause,[],[f153])).
% 0.20/0.52  fof(f191,plain,(
% 0.20/0.52    m1_pre_topc(sK2,sK0) | (~spl6_2 | ~spl6_10 | ~spl6_11)),
% 0.20/0.52    inference(forward_demodulation,[],[f190,f165])).
% 0.20/0.52  fof(f190,plain,(
% 0.20/0.52    m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK0) | (~spl6_2 | ~spl6_10)),
% 0.20/0.52    inference(subsumption_resolution,[],[f189,f120])).
% 0.20/0.52  fof(f189,plain,(
% 0.20/0.52    m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK0) | ~l1_pre_topc(sK0) | ~spl6_10),
% 0.20/0.52    inference(resolution,[],[f87,f160])).
% 0.20/0.52  fof(f87,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f22])).
% 0.20/0.52  fof(f22,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : ((m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f9])).
% 0.20/0.52  fof(f9,axiom,(
% 0.20/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_tmap_1)).
% 0.20/0.52  fof(f166,plain,(
% 0.20/0.52    spl6_11),
% 0.20/0.52    inference(avatar_split_clause,[],[f58,f163])).
% 0.20/0.52  fof(f58,plain,(
% 0.20/0.52    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = sK2),
% 0.20/0.52    inference(cnf_transformation,[],[f35])).
% 0.20/0.52  fof(f161,plain,(
% 0.20/0.52    spl6_10 | spl6_9),
% 0.20/0.52    inference(avatar_split_clause,[],[f62,f153,f158])).
% 0.20/0.52  fof(f62,plain,(
% 0.20/0.52    m1_pre_topc(sK2,sK0) | m1_pre_topc(sK1,sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f35])).
% 0.20/0.52  fof(f151,plain,(
% 0.20/0.52    spl6_7 | spl6_8),
% 0.20/0.52    inference(avatar_split_clause,[],[f59,f148,f144])).
% 0.20/0.52  fof(f59,plain,(
% 0.20/0.52    v1_borsuk_1(sK2,sK0) | v1_borsuk_1(sK1,sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f35])).
% 0.20/0.52  fof(f141,plain,(
% 0.20/0.52    spl6_6),
% 0.20/0.52    inference(avatar_split_clause,[],[f57,f138])).
% 0.20/0.52  fof(f57,plain,(
% 0.20/0.52    l1_pre_topc(sK2)),
% 0.20/0.52    inference(cnf_transformation,[],[f35])).
% 0.20/0.52  fof(f136,plain,(
% 0.20/0.52    spl6_5),
% 0.20/0.52    inference(avatar_split_clause,[],[f56,f133])).
% 0.20/0.52  fof(f56,plain,(
% 0.20/0.52    v2_pre_topc(sK2)),
% 0.20/0.52    inference(cnf_transformation,[],[f35])).
% 0.20/0.52  fof(f131,plain,(
% 0.20/0.52    spl6_4),
% 0.20/0.52    inference(avatar_split_clause,[],[f55,f128])).
% 0.20/0.52  fof(f55,plain,(
% 0.20/0.52    l1_pre_topc(sK1)),
% 0.20/0.52    inference(cnf_transformation,[],[f35])).
% 0.20/0.52  fof(f126,plain,(
% 0.20/0.52    spl6_3),
% 0.20/0.52    inference(avatar_split_clause,[],[f54,f123])).
% 0.20/0.52  fof(f54,plain,(
% 0.20/0.52    v2_pre_topc(sK1)),
% 0.20/0.52    inference(cnf_transformation,[],[f35])).
% 0.20/0.52  fof(f121,plain,(
% 0.20/0.52    spl6_2),
% 0.20/0.52    inference(avatar_split_clause,[],[f53,f118])).
% 0.20/0.52  fof(f53,plain,(
% 0.20/0.52    l1_pre_topc(sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f35])).
% 0.20/0.52  fof(f116,plain,(
% 0.20/0.52    spl6_1),
% 0.20/0.52    inference(avatar_split_clause,[],[f52,f113])).
% 0.20/0.52  fof(f52,plain,(
% 0.20/0.52    v2_pre_topc(sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f35])).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (17475)------------------------------
% 0.20/0.52  % (17475)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (17475)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (17475)Memory used [KB]: 6780
% 0.20/0.52  % (17475)Time elapsed: 0.079 s
% 0.20/0.52  % (17475)------------------------------
% 0.20/0.52  % (17475)------------------------------
% 0.20/0.52  % (17473)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.52  % (17468)Success in time 0.159 s
%------------------------------------------------------------------------------
