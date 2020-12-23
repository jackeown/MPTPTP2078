%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:43 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  208 ( 394 expanded)
%              Number of leaves         :   43 ( 155 expanded)
%              Depth                    :   13
%              Number of atoms          :  822 (1494 expanded)
%              Number of equality atoms :   66 ( 118 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f721,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f58,f63,f68,f73,f78,f83,f92,f97,f102,f153,f187,f204,f233,f292,f303,f334,f377,f403,f410,f421,f465,f467,f468,f513,f549,f618,f634,f670,f718,f719,f720])).

fof(f720,plain,
    ( k1_xboole_0 != sK1
    | v1_compts_1(k1_pre_topc(sK0,sK1))
    | ~ v1_compts_1(k1_pre_topc(sK0,k1_xboole_0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f719,plain,
    ( k1_xboole_0 != sK1
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f718,plain,
    ( ~ spl3_2
    | ~ spl3_50
    | spl3_55
    | ~ spl3_58 ),
    inference(avatar_contradiction_clause,[],[f717])).

fof(f717,plain,
    ( $false
    | ~ spl3_2
    | ~ spl3_50
    | spl3_55
    | ~ spl3_58 ),
    inference(subsumption_resolution,[],[f716,f464])).

fof(f464,plain,
    ( v2_compts_1(k1_xboole_0,sK0)
    | ~ spl3_50 ),
    inference(avatar_component_clause,[],[f462])).

fof(f462,plain,
    ( spl3_50
  <=> v2_compts_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_50])])).

fof(f716,plain,
    ( ~ v2_compts_1(k1_xboole_0,sK0)
    | ~ spl3_2
    | spl3_55
    | ~ spl3_58 ),
    inference(subsumption_resolution,[],[f715,f62])).

fof(f62,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl3_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f715,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_compts_1(k1_xboole_0,sK0)
    | spl3_55
    | ~ spl3_58 ),
    inference(subsumption_resolution,[],[f713,f548])).

fof(f548,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_58 ),
    inference(avatar_component_clause,[],[f546])).

fof(f546,plain,
    ( spl3_58
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_58])])).

fof(f713,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_compts_1(k1_xboole_0,sK0)
    | spl3_55 ),
    inference(resolution,[],[f530,f50])).

fof(f50,plain,(
    ! [X0] :
      ( v1_compts_1(k1_pre_topc(X0,k1_xboole_0))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_compts_1(k1_xboole_0,X0) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_xboole_0 != X1
      | v1_compts_1(k1_pre_topc(X0,X1))
      | ~ v2_compts_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( ( v2_compts_1(X1,X0)
              <=> v1_compts_1(k1_pre_topc(X0,X1)) )
              | k1_xboole_0 = X1
              | ~ v2_pre_topc(X0) )
            & ( ( v2_compts_1(X1,X0)
              <=> v1_compts_1(k1_pre_topc(X0,X1)) )
              | k1_xboole_0 != X1 ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( ( v2_compts_1(X1,X0)
              <=> v1_compts_1(k1_pre_topc(X0,X1)) )
              | k1_xboole_0 = X1
              | ~ v2_pre_topc(X0) )
            & ( ( v2_compts_1(X1,X0)
              <=> v1_compts_1(k1_pre_topc(X0,X1)) )
              | k1_xboole_0 != X1 ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v2_pre_topc(X0)
             => ( ( v2_compts_1(X1,X0)
                <=> v1_compts_1(k1_pre_topc(X0,X1)) )
                | k1_xboole_0 = X1 ) )
            & ( k1_xboole_0 = X1
             => ( v2_compts_1(X1,X0)
              <=> v1_compts_1(k1_pre_topc(X0,X1)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_compts_1)).

fof(f530,plain,
    ( ~ v1_compts_1(k1_pre_topc(sK0,k1_xboole_0))
    | spl3_55 ),
    inference(avatar_component_clause,[],[f528])).

fof(f528,plain,
    ( spl3_55
  <=> v1_compts_1(k1_pre_topc(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_55])])).

fof(f670,plain,
    ( ~ spl3_2
    | spl3_50
    | ~ spl3_55
    | ~ spl3_58 ),
    inference(avatar_contradiction_clause,[],[f669])).

fof(f669,plain,
    ( $false
    | ~ spl3_2
    | spl3_50
    | ~ spl3_55
    | ~ spl3_58 ),
    inference(subsumption_resolution,[],[f651,f529])).

fof(f529,plain,
    ( v1_compts_1(k1_pre_topc(sK0,k1_xboole_0))
    | ~ spl3_55 ),
    inference(avatar_component_clause,[],[f528])).

fof(f651,plain,
    ( ~ v1_compts_1(k1_pre_topc(sK0,k1_xboole_0))
    | ~ spl3_2
    | spl3_50
    | ~ spl3_58 ),
    inference(subsumption_resolution,[],[f650,f463])).

fof(f463,plain,
    ( ~ v2_compts_1(k1_xboole_0,sK0)
    | spl3_50 ),
    inference(avatar_component_clause,[],[f462])).

fof(f650,plain,
    ( ~ v1_compts_1(k1_pre_topc(sK0,k1_xboole_0))
    | v2_compts_1(k1_xboole_0,sK0)
    | ~ spl3_2
    | ~ spl3_58 ),
    inference(subsumption_resolution,[],[f550,f62])).

fof(f550,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v1_compts_1(k1_pre_topc(sK0,k1_xboole_0))
    | v2_compts_1(k1_xboole_0,sK0)
    | ~ spl3_58 ),
    inference(resolution,[],[f548,f51])).

fof(f51,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v1_compts_1(k1_pre_topc(X0,k1_xboole_0))
      | v2_compts_1(k1_xboole_0,X0) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_xboole_0 != X1
      | ~ v1_compts_1(k1_pre_topc(X0,X1))
      | v2_compts_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f634,plain,
    ( k1_xboole_0 != sK2
    | v2_compts_1(sK2,sK0)
    | ~ v2_compts_1(k1_xboole_0,sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f618,plain,
    ( ~ spl3_14
    | ~ spl3_23
    | ~ spl3_29
    | ~ spl3_31
    | ~ spl3_51
    | spl3_55 ),
    inference(avatar_contradiction_clause,[],[f617])).

fof(f617,plain,
    ( $false
    | ~ spl3_14
    | ~ spl3_23
    | ~ spl3_29
    | ~ spl3_31
    | ~ spl3_51
    | spl3_55 ),
    inference(subsumption_resolution,[],[f616,f276])).

fof(f276,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1))
    | ~ spl3_31 ),
    inference(avatar_component_clause,[],[f275])).

fof(f275,plain,
    ( spl3_31
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f616,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1))
    | ~ spl3_14
    | ~ spl3_23
    | ~ spl3_29
    | ~ spl3_51
    | spl3_55 ),
    inference(forward_demodulation,[],[f615,f152])).

fof(f152,plain,
    ( sK1 = u1_struct_0(k1_pre_topc(sK0,sK1))
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f150])).

fof(f150,plain,
    ( spl3_14
  <=> sK1 = u1_struct_0(k1_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f615,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1))))
    | ~ spl3_23
    | ~ spl3_29
    | ~ spl3_51
    | spl3_55 ),
    inference(subsumption_resolution,[],[f614,f269])).

fof(f269,plain,
    ( v2_compts_1(k1_xboole_0,k1_pre_topc(sK0,sK1))
    | ~ spl3_29 ),
    inference(avatar_component_clause,[],[f267])).

fof(f267,plain,
    ( spl3_29
  <=> v2_compts_1(k1_xboole_0,k1_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f614,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1))))
    | ~ v2_compts_1(k1_xboole_0,k1_pre_topc(sK0,sK1))
    | ~ spl3_23
    | ~ spl3_51
    | spl3_55 ),
    inference(subsumption_resolution,[],[f613,f217])).

fof(f217,plain,
    ( l1_pre_topc(k1_pre_topc(sK0,sK1))
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f216])).

fof(f216,plain,
    ( spl3_23
  <=> l1_pre_topc(k1_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f613,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1))))
    | ~ l1_pre_topc(k1_pre_topc(sK0,sK1))
    | ~ v2_compts_1(k1_xboole_0,k1_pre_topc(sK0,sK1))
    | ~ spl3_51
    | spl3_55 ),
    inference(subsumption_resolution,[],[f609,f530])).

fof(f609,plain,
    ( v1_compts_1(k1_pre_topc(sK0,k1_xboole_0))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1))))
    | ~ l1_pre_topc(k1_pre_topc(sK0,sK1))
    | ~ v2_compts_1(k1_xboole_0,k1_pre_topc(sK0,sK1))
    | ~ spl3_51 ),
    inference(superposition,[],[f50,f472])).

fof(f472,plain,
    ( k1_pre_topc(k1_pre_topc(sK0,sK1),k1_xboole_0) = k1_pre_topc(sK0,k1_xboole_0)
    | ~ spl3_51 ),
    inference(avatar_component_clause,[],[f470])).

fof(f470,plain,
    ( spl3_51
  <=> k1_pre_topc(k1_pre_topc(sK0,sK1),k1_xboole_0) = k1_pre_topc(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_51])])).

fof(f549,plain,
    ( spl3_58
    | ~ spl3_7
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f481,f201,f89,f546])).

fof(f89,plain,
    ( spl3_7
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f201,plain,
    ( spl3_20
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f481,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_7
    | ~ spl3_20 ),
    inference(superposition,[],[f91,f203])).

fof(f203,plain,
    ( k1_xboole_0 = sK2
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f201])).

fof(f91,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f89])).

fof(f513,plain,
    ( k1_xboole_0 != sK2
    | k1_pre_topc(sK0,sK2) != k1_pre_topc(k1_pre_topc(sK0,sK1),sK2)
    | k1_pre_topc(k1_pre_topc(sK0,sK1),k1_xboole_0) = k1_pre_topc(sK0,k1_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f468,plain,
    ( k1_xboole_0 != sK2
    | v2_compts_1(k1_xboole_0,k1_pre_topc(sK0,sK1))
    | ~ v2_compts_1(sK2,k1_pre_topc(sK0,sK1)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f467,plain,
    ( k1_xboole_0 != sK2
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f465,plain,
    ( spl3_50
    | ~ spl3_3
    | ~ spl3_34 ),
    inference(avatar_split_clause,[],[f435,f300,f65,f462])).

fof(f65,plain,
    ( spl3_3
  <=> v2_compts_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f300,plain,
    ( spl3_34
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).

fof(f435,plain,
    ( v2_compts_1(k1_xboole_0,sK0)
    | ~ spl3_3
    | ~ spl3_34 ),
    inference(superposition,[],[f67,f302])).

fof(f302,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_34 ),
    inference(avatar_component_clause,[],[f300])).

fof(f67,plain,
    ( v2_compts_1(sK1,sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f65])).

fof(f421,plain,
    ( ~ spl3_2
    | ~ spl3_5
    | ~ spl3_7
    | ~ spl3_9
    | ~ spl3_14
    | ~ spl3_40
    | spl3_47 ),
    inference(avatar_contradiction_clause,[],[f420])).

fof(f420,plain,
    ( $false
    | ~ spl3_2
    | ~ spl3_5
    | ~ spl3_7
    | ~ spl3_9
    | ~ spl3_14
    | ~ spl3_40
    | spl3_47 ),
    inference(subsumption_resolution,[],[f419,f101])).

fof(f101,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl3_9
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f419,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK1))
    | ~ spl3_2
    | ~ spl3_5
    | ~ spl3_7
    | ~ spl3_14
    | ~ spl3_40
    | spl3_47 ),
    inference(forward_demodulation,[],[f418,f152])).

fof(f418,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1))))
    | ~ spl3_2
    | ~ spl3_5
    | ~ spl3_7
    | ~ spl3_40
    | spl3_47 ),
    inference(subsumption_resolution,[],[f415,f368])).

fof(f368,plain,
    ( m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)
    | ~ spl3_40 ),
    inference(avatar_component_clause,[],[f367])).

fof(f367,plain,
    ( spl3_40
  <=> m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).

fof(f415,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1))))
    | ~ m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)
    | ~ spl3_2
    | ~ spl3_5
    | ~ spl3_7
    | spl3_47 ),
    inference(resolution,[],[f409,f108])).

fof(f108,plain,
    ( ! [X0] :
        ( v4_pre_topc(sK2,X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_pre_topc(X0,sK0) )
    | ~ spl3_2
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f107,f77])).

fof(f77,plain,
    ( v4_pre_topc(sK2,sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl3_5
  <=> v4_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f107,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | ~ v4_pre_topc(sK2,sK0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
        | v4_pre_topc(sK2,X0) )
    | ~ spl3_2
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f103,f62])).

fof(f103,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ v4_pre_topc(sK2,sK0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
        | v4_pre_topc(sK2,X0) )
    | ~ spl3_7 ),
    inference(resolution,[],[f91,f52])).

fof(f52,plain,(
    ! [X2,X0,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ v4_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | v4_pre_topc(X3,X2) ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X2,X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | X1 != X3
      | v4_pre_topc(X3,X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v4_pre_topc(X3,X2)
                  | X1 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              | ~ v4_pre_topc(X1,X0)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v4_pre_topc(X3,X2)
                  | X1 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              | ~ v4_pre_topc(X1,X0)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( v4_pre_topc(X1,X0)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
                   => ( X1 = X3
                     => v4_pre_topc(X3,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_tops_2)).

fof(f409,plain,
    ( ~ v4_pre_topc(sK2,k1_pre_topc(sK0,sK1))
    | spl3_47 ),
    inference(avatar_component_clause,[],[f407])).

fof(f407,plain,
    ( spl3_47
  <=> v4_pre_topc(sK2,k1_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).

fof(f410,plain,
    ( ~ spl3_47
    | ~ spl3_9
    | ~ spl3_33
    | spl3_46 ),
    inference(avatar_split_clause,[],[f405,f400,f290,f99,f407])).

fof(f290,plain,
    ( spl3_33
  <=> ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(sK1))
        | v2_compts_1(X2,k1_pre_topc(sK0,sK1))
        | ~ v4_pre_topc(X2,k1_pre_topc(sK0,sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

fof(f400,plain,
    ( spl3_46
  <=> v2_compts_1(sK2,k1_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).

fof(f405,plain,
    ( ~ v4_pre_topc(sK2,k1_pre_topc(sK0,sK1))
    | ~ spl3_9
    | ~ spl3_33
    | spl3_46 ),
    inference(subsumption_resolution,[],[f404,f101])).

fof(f404,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK1))
    | ~ v4_pre_topc(sK2,k1_pre_topc(sK0,sK1))
    | ~ spl3_33
    | spl3_46 ),
    inference(resolution,[],[f402,f291])).

fof(f291,plain,
    ( ! [X2] :
        ( v2_compts_1(X2,k1_pre_topc(sK0,sK1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(sK1))
        | ~ v4_pre_topc(X2,k1_pre_topc(sK0,sK1)) )
    | ~ spl3_33 ),
    inference(avatar_component_clause,[],[f290])).

fof(f402,plain,
    ( ~ v2_compts_1(sK2,k1_pre_topc(sK0,sK1))
    | spl3_46 ),
    inference(avatar_component_clause,[],[f400])).

fof(f403,plain,
    ( ~ spl3_46
    | ~ spl3_9
    | ~ spl3_14
    | ~ spl3_18
    | spl3_19
    | spl3_20
    | ~ spl3_23
    | ~ spl3_36 ),
    inference(avatar_split_clause,[],[f351,f331,f216,f201,f197,f184,f150,f99,f400])).

fof(f184,plain,
    ( spl3_18
  <=> v2_pre_topc(k1_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f197,plain,
    ( spl3_19
  <=> v1_compts_1(k1_pre_topc(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f331,plain,
    ( spl3_36
  <=> k1_pre_topc(sK0,sK2) = k1_pre_topc(k1_pre_topc(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).

fof(f351,plain,
    ( ~ v2_compts_1(sK2,k1_pre_topc(sK0,sK1))
    | ~ spl3_9
    | ~ spl3_14
    | ~ spl3_18
    | spl3_19
    | spl3_20
    | ~ spl3_23
    | ~ spl3_36 ),
    inference(subsumption_resolution,[],[f350,f101])).

fof(f350,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK1))
    | ~ v2_compts_1(sK2,k1_pre_topc(sK0,sK1))
    | ~ spl3_14
    | ~ spl3_18
    | spl3_19
    | spl3_20
    | ~ spl3_23
    | ~ spl3_36 ),
    inference(forward_demodulation,[],[f349,f152])).

fof(f349,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1))))
    | ~ v2_compts_1(sK2,k1_pre_topc(sK0,sK1))
    | ~ spl3_18
    | spl3_19
    | spl3_20
    | ~ spl3_23
    | ~ spl3_36 ),
    inference(subsumption_resolution,[],[f348,f217])).

fof(f348,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1))))
    | ~ l1_pre_topc(k1_pre_topc(sK0,sK1))
    | ~ v2_compts_1(sK2,k1_pre_topc(sK0,sK1))
    | ~ spl3_18
    | spl3_19
    | spl3_20
    | ~ spl3_36 ),
    inference(subsumption_resolution,[],[f347,f202])).

fof(f202,plain,
    ( k1_xboole_0 != sK2
    | spl3_20 ),
    inference(avatar_component_clause,[],[f201])).

fof(f347,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1))))
    | k1_xboole_0 = sK2
    | ~ l1_pre_topc(k1_pre_topc(sK0,sK1))
    | ~ v2_compts_1(sK2,k1_pre_topc(sK0,sK1))
    | ~ spl3_18
    | spl3_19
    | ~ spl3_36 ),
    inference(subsumption_resolution,[],[f346,f186])).

fof(f186,plain,
    ( v2_pre_topc(k1_pre_topc(sK0,sK1))
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f184])).

fof(f346,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1))))
    | ~ v2_pre_topc(k1_pre_topc(sK0,sK1))
    | k1_xboole_0 = sK2
    | ~ l1_pre_topc(k1_pre_topc(sK0,sK1))
    | ~ v2_compts_1(sK2,k1_pre_topc(sK0,sK1))
    | spl3_19
    | ~ spl3_36 ),
    inference(subsumption_resolution,[],[f339,f199])).

fof(f199,plain,
    ( ~ v1_compts_1(k1_pre_topc(sK0,sK2))
    | spl3_19 ),
    inference(avatar_component_clause,[],[f197])).

fof(f339,plain,
    ( v1_compts_1(k1_pre_topc(sK0,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1))))
    | ~ v2_pre_topc(k1_pre_topc(sK0,sK1))
    | k1_xboole_0 = sK2
    | ~ l1_pre_topc(k1_pre_topc(sK0,sK1))
    | ~ v2_compts_1(sK2,k1_pre_topc(sK0,sK1))
    | ~ spl3_36 ),
    inference(superposition,[],[f39,f333])).

fof(f333,plain,
    ( k1_pre_topc(sK0,sK2) = k1_pre_topc(k1_pre_topc(sK0,sK1),sK2)
    | ~ spl3_36 ),
    inference(avatar_component_clause,[],[f331])).

fof(f39,plain,(
    ! [X0,X1] :
      ( v1_compts_1(k1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | k1_xboole_0 = X1
      | ~ l1_pre_topc(X0)
      | ~ v2_compts_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f377,plain,
    ( ~ spl3_2
    | ~ spl3_8
    | spl3_40 ),
    inference(avatar_contradiction_clause,[],[f376])).

fof(f376,plain,
    ( $false
    | ~ spl3_2
    | ~ spl3_8
    | spl3_40 ),
    inference(subsumption_resolution,[],[f375,f62])).

fof(f375,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl3_8
    | spl3_40 ),
    inference(subsumption_resolution,[],[f374,f96])).

fof(f96,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl3_8
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f374,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl3_40 ),
    inference(resolution,[],[f369,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_pre_topc)).

fof(f369,plain,
    ( ~ m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)
    | spl3_40 ),
    inference(avatar_component_clause,[],[f367])).

fof(f334,plain,
    ( spl3_36
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f322,f150,f99,f94,f89,f70,f60,f55,f331])).

fof(f55,plain,
    ( spl3_1
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f70,plain,
    ( spl3_4
  <=> r1_tarski(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f322,plain,
    ( k1_pre_topc(sK0,sK2) = k1_pre_topc(k1_pre_topc(sK0,sK1),sK2)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_14 ),
    inference(subsumption_resolution,[],[f321,f72])).

fof(f72,plain,
    ( r1_tarski(sK2,sK1)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f70])).

fof(f321,plain,
    ( ~ r1_tarski(sK2,sK1)
    | k1_pre_topc(sK0,sK2) = k1_pre_topc(k1_pre_topc(sK0,sK1),sK2)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_14 ),
    inference(subsumption_resolution,[],[f320,f96])).

fof(f320,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(sK2,sK1)
    | k1_pre_topc(sK0,sK2) = k1_pre_topc(k1_pre_topc(sK0,sK1),sK2)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_7
    | ~ spl3_9
    | ~ spl3_14 ),
    inference(subsumption_resolution,[],[f317,f101])).

fof(f317,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(sK2,sK1)
    | k1_pre_topc(sK0,sK2) = k1_pre_topc(k1_pre_topc(sK0,sK1),sK2)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_7
    | ~ spl3_14 ),
    inference(superposition,[],[f188,f152])).

fof(f188,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,X0))))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(sK2,X0)
        | k1_pre_topc(sK0,sK2) = k1_pre_topc(k1_pre_topc(sK0,X0),sK2) )
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_7 ),
    inference(resolution,[],[f182,f91])).

fof(f182,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,X1))))
        | ~ r1_tarski(X0,X1)
        | k1_pre_topc(k1_pre_topc(sK0,X1),X0) = k1_pre_topc(sK0,X0) )
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f84,f62])).

fof(f84,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,X1))))
        | ~ r1_tarski(X0,X1)
        | k1_pre_topc(k1_pre_topc(sK0,X1),X0) = k1_pre_topc(sK0,X0) )
    | ~ spl3_1 ),
    inference(resolution,[],[f57,f53])).

fof(f53,plain,(
    ! [X2,X0,X3] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X2))))
      | ~ r1_tarski(X3,X2)
      | k1_pre_topc(k1_pre_topc(X0,X2),X3) = k1_pre_topc(X0,X3) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X2))))
      | X1 != X3
      | ~ r1_tarski(X1,X2)
      | k1_pre_topc(X0,X1) = k1_pre_topc(k1_pre_topc(X0,X2),X3) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k1_pre_topc(X0,X1) = k1_pre_topc(k1_pre_topc(X0,X2),X3)
                  | ~ r1_tarski(X1,X2)
                  | X1 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X2)))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k1_pre_topc(X0,X1) = k1_pre_topc(k1_pre_topc(X0,X2),X3)
                  | ~ r1_tarski(X1,X2)
                  | X1 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X2)))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X2))))
                 => ( ( r1_tarski(X1,X2)
                      & X1 = X3 )
                   => k1_pre_topc(X0,X1) = k1_pre_topc(k1_pre_topc(X0,X2),X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_pre_topc)).

fof(f57,plain,
    ( v2_pre_topc(sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f55])).

fof(f303,plain,
    ( spl3_34
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_8
    | spl3_32 ),
    inference(avatar_split_clause,[],[f297,f286,f94,f65,f60,f55,f300])).

fof(f286,plain,
    ( spl3_32
  <=> v1_compts_1(k1_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f297,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_8
    | spl3_32 ),
    inference(subsumption_resolution,[],[f296,f67])).

fof(f296,plain,
    ( k1_xboole_0 = sK1
    | ~ v2_compts_1(sK1,sK0)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_8
    | spl3_32 ),
    inference(subsumption_resolution,[],[f295,f62])).

fof(f295,plain,
    ( k1_xboole_0 = sK1
    | ~ l1_pre_topc(sK0)
    | ~ v2_compts_1(sK1,sK0)
    | ~ spl3_1
    | ~ spl3_8
    | spl3_32 ),
    inference(subsumption_resolution,[],[f294,f57])).

fof(f294,plain,
    ( ~ v2_pre_topc(sK0)
    | k1_xboole_0 = sK1
    | ~ l1_pre_topc(sK0)
    | ~ v2_compts_1(sK1,sK0)
    | ~ spl3_8
    | spl3_32 ),
    inference(subsumption_resolution,[],[f293,f96])).

fof(f293,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | k1_xboole_0 = sK1
    | ~ l1_pre_topc(sK0)
    | ~ v2_compts_1(sK1,sK0)
    | spl3_32 ),
    inference(resolution,[],[f288,f39])).

fof(f288,plain,
    ( ~ v1_compts_1(k1_pre_topc(sK0,sK1))
    | spl3_32 ),
    inference(avatar_component_clause,[],[f286])).

fof(f292,plain,
    ( ~ spl3_32
    | spl3_33
    | ~ spl3_14
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f281,f216,f150,f290,f286])).

fof(f281,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(sK1))
        | ~ v1_compts_1(k1_pre_topc(sK0,sK1))
        | ~ v4_pre_topc(X2,k1_pre_topc(sK0,sK1))
        | v2_compts_1(X2,k1_pre_topc(sK0,sK1)) )
    | ~ spl3_14
    | ~ spl3_23 ),
    inference(subsumption_resolution,[],[f155,f217])).

fof(f155,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(sK1))
        | ~ l1_pre_topc(k1_pre_topc(sK0,sK1))
        | ~ v1_compts_1(k1_pre_topc(sK0,sK1))
        | ~ v4_pre_topc(X2,k1_pre_topc(sK0,sK1))
        | v2_compts_1(X2,k1_pre_topc(sK0,sK1)) )
    | ~ spl3_14 ),
    inference(superposition,[],[f42,f152])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v1_compts_1(X0)
      | ~ v4_pre_topc(X1,X0)
      | v2_compts_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_compts_1(X1,X0)
          | ~ v4_pre_topc(X1,X0)
          | ~ v1_compts_1(X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_compts_1(X1,X0)
          | ~ v4_pre_topc(X1,X0)
          | ~ v1_compts_1(X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v4_pre_topc(X1,X0)
              & v1_compts_1(X0) )
           => v2_compts_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_compts_1)).

fof(f233,plain,
    ( ~ spl3_2
    | ~ spl3_8
    | spl3_23 ),
    inference(avatar_contradiction_clause,[],[f232])).

fof(f232,plain,
    ( $false
    | ~ spl3_2
    | ~ spl3_8
    | spl3_23 ),
    inference(subsumption_resolution,[],[f231,f96])).

fof(f231,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_2
    | spl3_23 ),
    inference(subsumption_resolution,[],[f230,f62])).

fof(f230,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_23 ),
    inference(duplicate_literal_removal,[],[f229])).

fof(f229,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl3_23 ),
    inference(resolution,[],[f223,f47])).

fof(f223,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(k1_pre_topc(sK0,sK1),X0)
        | ~ l1_pre_topc(X0) )
    | spl3_23 ),
    inference(resolution,[],[f218,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f218,plain,
    ( ~ l1_pre_topc(k1_pre_topc(sK0,sK1))
    | spl3_23 ),
    inference(avatar_component_clause,[],[f216])).

fof(f204,plain,
    ( ~ spl3_19
    | spl3_20
    | ~ spl3_1
    | ~ spl3_2
    | spl3_6
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f175,f89,f80,f60,f55,f201,f197])).

fof(f80,plain,
    ( spl3_6
  <=> v2_compts_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f175,plain,
    ( k1_xboole_0 = sK2
    | ~ v1_compts_1(k1_pre_topc(sK0,sK2))
    | ~ spl3_1
    | ~ spl3_2
    | spl3_6
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f174,f91])).

fof(f174,plain,
    ( k1_xboole_0 = sK2
    | ~ v1_compts_1(k1_pre_topc(sK0,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_1
    | ~ spl3_2
    | spl3_6 ),
    inference(resolution,[],[f173,f82])).

fof(f82,plain,
    ( ~ v2_compts_1(sK2,sK0)
    | spl3_6 ),
    inference(avatar_component_clause,[],[f80])).

fof(f173,plain,
    ( ! [X3] :
        ( v2_compts_1(X3,sK0)
        | k1_xboole_0 = X3
        | ~ v1_compts_1(k1_pre_topc(sK0,X3))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f86,f62])).

fof(f86,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | k1_xboole_0 = X3
        | ~ v1_compts_1(k1_pre_topc(sK0,X3))
        | v2_compts_1(X3,sK0) )
    | ~ spl3_1 ),
    inference(resolution,[],[f57,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k1_xboole_0 = X1
      | ~ v1_compts_1(k1_pre_topc(X0,X1))
      | v2_compts_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f187,plain,
    ( spl3_18
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f159,f94,f60,f55,f184])).

fof(f159,plain,
    ( v2_pre_topc(k1_pre_topc(sK0,sK1))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_8 ),
    inference(resolution,[],[f139,f96])).

fof(f139,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_pre_topc(k1_pre_topc(sK0,X0)) )
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f138,f62])).

fof(f138,plain,
    ( ! [X0] :
        ( v2_pre_topc(k1_pre_topc(sK0,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(resolution,[],[f137,f47])).

fof(f137,plain,
    ( ! [X2] :
        ( ~ m1_pre_topc(X2,sK0)
        | v2_pre_topc(X2) )
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f85,f62])).

fof(f85,plain,
    ( ! [X2] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_pre_topc(X2,sK0)
        | v2_pre_topc(X2) )
    | ~ spl3_1 ),
    inference(resolution,[],[f57,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f153,plain,
    ( spl3_14
    | ~ spl3_2
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f119,f94,f60,f150])).

fof(f119,plain,
    ( sK1 = u1_struct_0(k1_pre_topc(sK0,sK1))
    | ~ spl3_2
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f116,f62])).

fof(f116,plain,
    ( ~ l1_pre_topc(sK0)
    | sK1 = u1_struct_0(k1_pre_topc(sK0,sK1))
    | ~ spl3_8 ),
    inference(resolution,[],[f96,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | u1_struct_0(k1_pre_topc(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => u1_struct_0(k1_pre_topc(X0,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_pre_topc)).

fof(f102,plain,
    ( spl3_9
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f87,f70,f99])).

fof(f87,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1))
    | ~ spl3_4 ),
    inference(resolution,[],[f72,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f97,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f33,f94])).

fof(f33,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_compts_1(X2,X0)
              & v4_pre_topc(X2,X0)
              & r1_tarski(X2,X1)
              & v2_compts_1(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_compts_1(X2,X0)
              & v4_pre_topc(X2,X0)
              & r1_tarski(X2,X1)
              & v2_compts_1(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v4_pre_topc(X2,X0)
                    & r1_tarski(X2,X1)
                    & v2_compts_1(X1,X0) )
                 => v2_compts_1(X2,X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v4_pre_topc(X2,X0)
                  & r1_tarski(X2,X1)
                  & v2_compts_1(X1,X0) )
               => v2_compts_1(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_compts_1)).

fof(f92,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f28,f89])).

fof(f28,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f13])).

fof(f83,plain,(
    ~ spl3_6 ),
    inference(avatar_split_clause,[],[f32,f80])).

fof(f32,plain,(
    ~ v2_compts_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f78,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f31,f75])).

fof(f31,plain,(
    v4_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f73,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f30,f70])).

fof(f30,plain,(
    r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f68,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f29,f65])).

fof(f29,plain,(
    v2_compts_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f63,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f35,f60])).

fof(f35,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f58,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f34,f55])).

fof(f34,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:20:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.46  % (19899)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.47  % (19891)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.47  % (19884)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.47  % (19894)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.47  % (19884)Refutation not found, incomplete strategy% (19884)------------------------------
% 0.22/0.47  % (19884)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (19884)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.47  
% 0.22/0.47  % (19884)Memory used [KB]: 6268
% 0.22/0.47  % (19884)Time elapsed: 0.055 s
% 0.22/0.47  % (19884)------------------------------
% 0.22/0.47  % (19884)------------------------------
% 0.22/0.48  % (19897)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.48  % (19887)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.48  % (19897)Refutation not found, incomplete strategy% (19897)------------------------------
% 0.22/0.48  % (19897)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (19897)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (19897)Memory used [KB]: 1663
% 0.22/0.48  % (19897)Time elapsed: 0.063 s
% 0.22/0.48  % (19897)------------------------------
% 0.22/0.48  % (19897)------------------------------
% 0.22/0.49  % (19894)Refutation not found, incomplete strategy% (19894)------------------------------
% 0.22/0.49  % (19894)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (19894)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (19894)Memory used [KB]: 6268
% 0.22/0.49  % (19894)Time elapsed: 0.076 s
% 0.22/0.49  % (19894)------------------------------
% 0.22/0.49  % (19894)------------------------------
% 0.22/0.49  % (19885)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.49  % (19895)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.49  % (19886)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.49  % (19902)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.50  % (19887)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f721,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(avatar_sat_refutation,[],[f58,f63,f68,f73,f78,f83,f92,f97,f102,f153,f187,f204,f233,f292,f303,f334,f377,f403,f410,f421,f465,f467,f468,f513,f549,f618,f634,f670,f718,f719,f720])).
% 0.22/0.50  fof(f720,plain,(
% 0.22/0.50    k1_xboole_0 != sK1 | v1_compts_1(k1_pre_topc(sK0,sK1)) | ~v1_compts_1(k1_pre_topc(sK0,k1_xboole_0))),
% 0.22/0.50    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.50  fof(f719,plain,(
% 0.22/0.50    k1_xboole_0 != sK1 | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.50    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.50  fof(f718,plain,(
% 0.22/0.50    ~spl3_2 | ~spl3_50 | spl3_55 | ~spl3_58),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f717])).
% 0.22/0.50  fof(f717,plain,(
% 0.22/0.50    $false | (~spl3_2 | ~spl3_50 | spl3_55 | ~spl3_58)),
% 0.22/0.50    inference(subsumption_resolution,[],[f716,f464])).
% 0.22/0.50  fof(f464,plain,(
% 0.22/0.50    v2_compts_1(k1_xboole_0,sK0) | ~spl3_50),
% 0.22/0.50    inference(avatar_component_clause,[],[f462])).
% 0.22/0.50  fof(f462,plain,(
% 0.22/0.50    spl3_50 <=> v2_compts_1(k1_xboole_0,sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_50])])).
% 0.22/0.50  fof(f716,plain,(
% 0.22/0.50    ~v2_compts_1(k1_xboole_0,sK0) | (~spl3_2 | spl3_55 | ~spl3_58)),
% 0.22/0.50    inference(subsumption_resolution,[],[f715,f62])).
% 0.22/0.50  fof(f62,plain,(
% 0.22/0.50    l1_pre_topc(sK0) | ~spl3_2),
% 0.22/0.50    inference(avatar_component_clause,[],[f60])).
% 0.22/0.50  fof(f60,plain,(
% 0.22/0.50    spl3_2 <=> l1_pre_topc(sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.50  fof(f715,plain,(
% 0.22/0.50    ~l1_pre_topc(sK0) | ~v2_compts_1(k1_xboole_0,sK0) | (spl3_55 | ~spl3_58)),
% 0.22/0.50    inference(subsumption_resolution,[],[f713,f548])).
% 0.22/0.50  fof(f548,plain,(
% 0.22/0.50    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_58),
% 0.22/0.50    inference(avatar_component_clause,[],[f546])).
% 0.22/0.50  fof(f546,plain,(
% 0.22/0.50    spl3_58 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_58])])).
% 0.22/0.50  fof(f713,plain,(
% 0.22/0.50    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_compts_1(k1_xboole_0,sK0) | spl3_55),
% 0.22/0.50    inference(resolution,[],[f530,f50])).
% 0.22/0.50  fof(f50,plain,(
% 0.22/0.50    ( ! [X0] : (v1_compts_1(k1_pre_topc(X0,k1_xboole_0)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_compts_1(k1_xboole_0,X0)) )),
% 0.22/0.50    inference(equality_resolution,[],[f41])).
% 0.22/0.50  fof(f41,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_xboole_0 != X1 | v1_compts_1(k1_pre_topc(X0,X1)) | ~v2_compts_1(X1,X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f17])).
% 0.22/0.50  fof(f17,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : ((((v2_compts_1(X1,X0) <=> v1_compts_1(k1_pre_topc(X0,X1))) | k1_xboole_0 = X1 | ~v2_pre_topc(X0)) & ((v2_compts_1(X1,X0) <=> v1_compts_1(k1_pre_topc(X0,X1))) | k1_xboole_0 != X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.50    inference(flattening,[],[f16])).
% 0.22/0.50  fof(f16,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (((((v2_compts_1(X1,X0) <=> v1_compts_1(k1_pre_topc(X0,X1))) | k1_xboole_0 = X1) | ~v2_pre_topc(X0)) & ((v2_compts_1(X1,X0) <=> v1_compts_1(k1_pre_topc(X0,X1))) | k1_xboole_0 != X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f8])).
% 0.22/0.50  fof(f8,axiom,(
% 0.22/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_pre_topc(X0) => ((v2_compts_1(X1,X0) <=> v1_compts_1(k1_pre_topc(X0,X1))) | k1_xboole_0 = X1)) & (k1_xboole_0 = X1 => (v2_compts_1(X1,X0) <=> v1_compts_1(k1_pre_topc(X0,X1)))))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_compts_1)).
% 0.22/0.50  fof(f530,plain,(
% 0.22/0.50    ~v1_compts_1(k1_pre_topc(sK0,k1_xboole_0)) | spl3_55),
% 0.22/0.50    inference(avatar_component_clause,[],[f528])).
% 0.22/0.50  fof(f528,plain,(
% 0.22/0.50    spl3_55 <=> v1_compts_1(k1_pre_topc(sK0,k1_xboole_0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_55])])).
% 0.22/0.50  fof(f670,plain,(
% 0.22/0.50    ~spl3_2 | spl3_50 | ~spl3_55 | ~spl3_58),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f669])).
% 0.22/0.50  fof(f669,plain,(
% 0.22/0.50    $false | (~spl3_2 | spl3_50 | ~spl3_55 | ~spl3_58)),
% 0.22/0.50    inference(subsumption_resolution,[],[f651,f529])).
% 0.22/0.50  fof(f529,plain,(
% 0.22/0.50    v1_compts_1(k1_pre_topc(sK0,k1_xboole_0)) | ~spl3_55),
% 0.22/0.50    inference(avatar_component_clause,[],[f528])).
% 0.22/0.50  fof(f651,plain,(
% 0.22/0.50    ~v1_compts_1(k1_pre_topc(sK0,k1_xboole_0)) | (~spl3_2 | spl3_50 | ~spl3_58)),
% 0.22/0.50    inference(subsumption_resolution,[],[f650,f463])).
% 0.22/0.50  fof(f463,plain,(
% 0.22/0.50    ~v2_compts_1(k1_xboole_0,sK0) | spl3_50),
% 0.22/0.50    inference(avatar_component_clause,[],[f462])).
% 0.22/0.50  fof(f650,plain,(
% 0.22/0.50    ~v1_compts_1(k1_pre_topc(sK0,k1_xboole_0)) | v2_compts_1(k1_xboole_0,sK0) | (~spl3_2 | ~spl3_58)),
% 0.22/0.50    inference(subsumption_resolution,[],[f550,f62])).
% 0.22/0.50  fof(f550,plain,(
% 0.22/0.50    ~l1_pre_topc(sK0) | ~v1_compts_1(k1_pre_topc(sK0,k1_xboole_0)) | v2_compts_1(k1_xboole_0,sK0) | ~spl3_58),
% 0.22/0.50    inference(resolution,[],[f548,f51])).
% 0.22/0.50  fof(f51,plain,(
% 0.22/0.50    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v1_compts_1(k1_pre_topc(X0,k1_xboole_0)) | v2_compts_1(k1_xboole_0,X0)) )),
% 0.22/0.50    inference(equality_resolution,[],[f40])).
% 0.22/0.50  fof(f40,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_xboole_0 != X1 | ~v1_compts_1(k1_pre_topc(X0,X1)) | v2_compts_1(X1,X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f17])).
% 0.22/0.50  fof(f634,plain,(
% 0.22/0.50    k1_xboole_0 != sK2 | v2_compts_1(sK2,sK0) | ~v2_compts_1(k1_xboole_0,sK0)),
% 0.22/0.50    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.50  fof(f618,plain,(
% 0.22/0.50    ~spl3_14 | ~spl3_23 | ~spl3_29 | ~spl3_31 | ~spl3_51 | spl3_55),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f617])).
% 0.22/0.50  fof(f617,plain,(
% 0.22/0.50    $false | (~spl3_14 | ~spl3_23 | ~spl3_29 | ~spl3_31 | ~spl3_51 | spl3_55)),
% 0.22/0.50    inference(subsumption_resolution,[],[f616,f276])).
% 0.22/0.50  fof(f276,plain,(
% 0.22/0.50    m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1)) | ~spl3_31),
% 0.22/0.50    inference(avatar_component_clause,[],[f275])).
% 0.22/0.50  fof(f275,plain,(
% 0.22/0.50    spl3_31 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 0.22/0.50  fof(f616,plain,(
% 0.22/0.50    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1)) | (~spl3_14 | ~spl3_23 | ~spl3_29 | ~spl3_51 | spl3_55)),
% 0.22/0.50    inference(forward_demodulation,[],[f615,f152])).
% 0.22/0.50  fof(f152,plain,(
% 0.22/0.50    sK1 = u1_struct_0(k1_pre_topc(sK0,sK1)) | ~spl3_14),
% 0.22/0.50    inference(avatar_component_clause,[],[f150])).
% 0.22/0.50  fof(f150,plain,(
% 0.22/0.50    spl3_14 <=> sK1 = u1_struct_0(k1_pre_topc(sK0,sK1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.22/0.50  fof(f615,plain,(
% 0.22/0.50    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1)))) | (~spl3_23 | ~spl3_29 | ~spl3_51 | spl3_55)),
% 0.22/0.50    inference(subsumption_resolution,[],[f614,f269])).
% 0.22/0.50  fof(f269,plain,(
% 0.22/0.50    v2_compts_1(k1_xboole_0,k1_pre_topc(sK0,sK1)) | ~spl3_29),
% 0.22/0.50    inference(avatar_component_clause,[],[f267])).
% 0.22/0.50  fof(f267,plain,(
% 0.22/0.50    spl3_29 <=> v2_compts_1(k1_xboole_0,k1_pre_topc(sK0,sK1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 0.22/0.50  fof(f614,plain,(
% 0.22/0.50    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1)))) | ~v2_compts_1(k1_xboole_0,k1_pre_topc(sK0,sK1)) | (~spl3_23 | ~spl3_51 | spl3_55)),
% 0.22/0.50    inference(subsumption_resolution,[],[f613,f217])).
% 0.22/0.50  fof(f217,plain,(
% 0.22/0.50    l1_pre_topc(k1_pre_topc(sK0,sK1)) | ~spl3_23),
% 0.22/0.50    inference(avatar_component_clause,[],[f216])).
% 0.22/0.50  fof(f216,plain,(
% 0.22/0.50    spl3_23 <=> l1_pre_topc(k1_pre_topc(sK0,sK1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.22/0.50  fof(f613,plain,(
% 0.22/0.50    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1)))) | ~l1_pre_topc(k1_pre_topc(sK0,sK1)) | ~v2_compts_1(k1_xboole_0,k1_pre_topc(sK0,sK1)) | (~spl3_51 | spl3_55)),
% 0.22/0.50    inference(subsumption_resolution,[],[f609,f530])).
% 0.22/0.50  fof(f609,plain,(
% 0.22/0.50    v1_compts_1(k1_pre_topc(sK0,k1_xboole_0)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1)))) | ~l1_pre_topc(k1_pre_topc(sK0,sK1)) | ~v2_compts_1(k1_xboole_0,k1_pre_topc(sK0,sK1)) | ~spl3_51),
% 0.22/0.50    inference(superposition,[],[f50,f472])).
% 0.22/0.50  fof(f472,plain,(
% 0.22/0.50    k1_pre_topc(k1_pre_topc(sK0,sK1),k1_xboole_0) = k1_pre_topc(sK0,k1_xboole_0) | ~spl3_51),
% 0.22/0.50    inference(avatar_component_clause,[],[f470])).
% 0.22/0.50  fof(f470,plain,(
% 0.22/0.50    spl3_51 <=> k1_pre_topc(k1_pre_topc(sK0,sK1),k1_xboole_0) = k1_pre_topc(sK0,k1_xboole_0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_51])])).
% 0.22/0.50  fof(f549,plain,(
% 0.22/0.50    spl3_58 | ~spl3_7 | ~spl3_20),
% 0.22/0.50    inference(avatar_split_clause,[],[f481,f201,f89,f546])).
% 0.22/0.50  fof(f89,plain,(
% 0.22/0.50    spl3_7 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.50  fof(f201,plain,(
% 0.22/0.50    spl3_20 <=> k1_xboole_0 = sK2),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.22/0.50  fof(f481,plain,(
% 0.22/0.50    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_7 | ~spl3_20)),
% 0.22/0.50    inference(superposition,[],[f91,f203])).
% 0.22/0.50  fof(f203,plain,(
% 0.22/0.50    k1_xboole_0 = sK2 | ~spl3_20),
% 0.22/0.50    inference(avatar_component_clause,[],[f201])).
% 0.22/0.50  fof(f91,plain,(
% 0.22/0.50    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_7),
% 0.22/0.50    inference(avatar_component_clause,[],[f89])).
% 0.22/0.50  fof(f513,plain,(
% 0.22/0.50    k1_xboole_0 != sK2 | k1_pre_topc(sK0,sK2) != k1_pre_topc(k1_pre_topc(sK0,sK1),sK2) | k1_pre_topc(k1_pre_topc(sK0,sK1),k1_xboole_0) = k1_pre_topc(sK0,k1_xboole_0)),
% 0.22/0.50    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.50  fof(f468,plain,(
% 0.22/0.50    k1_xboole_0 != sK2 | v2_compts_1(k1_xboole_0,k1_pre_topc(sK0,sK1)) | ~v2_compts_1(sK2,k1_pre_topc(sK0,sK1))),
% 0.22/0.50    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.50  fof(f467,plain,(
% 0.22/0.50    k1_xboole_0 != sK2 | m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 0.22/0.50    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.50  fof(f465,plain,(
% 0.22/0.50    spl3_50 | ~spl3_3 | ~spl3_34),
% 0.22/0.50    inference(avatar_split_clause,[],[f435,f300,f65,f462])).
% 0.22/0.50  fof(f65,plain,(
% 0.22/0.50    spl3_3 <=> v2_compts_1(sK1,sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.50  fof(f300,plain,(
% 0.22/0.50    spl3_34 <=> k1_xboole_0 = sK1),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).
% 0.22/0.50  fof(f435,plain,(
% 0.22/0.50    v2_compts_1(k1_xboole_0,sK0) | (~spl3_3 | ~spl3_34)),
% 0.22/0.50    inference(superposition,[],[f67,f302])).
% 0.22/0.50  fof(f302,plain,(
% 0.22/0.50    k1_xboole_0 = sK1 | ~spl3_34),
% 0.22/0.50    inference(avatar_component_clause,[],[f300])).
% 0.22/0.50  fof(f67,plain,(
% 0.22/0.50    v2_compts_1(sK1,sK0) | ~spl3_3),
% 0.22/0.50    inference(avatar_component_clause,[],[f65])).
% 0.22/0.50  fof(f421,plain,(
% 0.22/0.50    ~spl3_2 | ~spl3_5 | ~spl3_7 | ~spl3_9 | ~spl3_14 | ~spl3_40 | spl3_47),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f420])).
% 0.22/0.50  fof(f420,plain,(
% 0.22/0.50    $false | (~spl3_2 | ~spl3_5 | ~spl3_7 | ~spl3_9 | ~spl3_14 | ~spl3_40 | spl3_47)),
% 0.22/0.50    inference(subsumption_resolution,[],[f419,f101])).
% 0.22/0.50  fof(f101,plain,(
% 0.22/0.50    m1_subset_1(sK2,k1_zfmisc_1(sK1)) | ~spl3_9),
% 0.22/0.50    inference(avatar_component_clause,[],[f99])).
% 0.22/0.50  fof(f99,plain,(
% 0.22/0.50    spl3_9 <=> m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.50  fof(f419,plain,(
% 0.22/0.50    ~m1_subset_1(sK2,k1_zfmisc_1(sK1)) | (~spl3_2 | ~spl3_5 | ~spl3_7 | ~spl3_14 | ~spl3_40 | spl3_47)),
% 0.22/0.50    inference(forward_demodulation,[],[f418,f152])).
% 0.22/0.50  fof(f418,plain,(
% 0.22/0.50    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1)))) | (~spl3_2 | ~spl3_5 | ~spl3_7 | ~spl3_40 | spl3_47)),
% 0.22/0.50    inference(subsumption_resolution,[],[f415,f368])).
% 0.22/0.50  fof(f368,plain,(
% 0.22/0.50    m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) | ~spl3_40),
% 0.22/0.50    inference(avatar_component_clause,[],[f367])).
% 0.22/0.50  fof(f367,plain,(
% 0.22/0.50    spl3_40 <=> m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).
% 0.22/0.50  fof(f415,plain,(
% 0.22/0.50    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1)))) | ~m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) | (~spl3_2 | ~spl3_5 | ~spl3_7 | spl3_47)),
% 0.22/0.50    inference(resolution,[],[f409,f108])).
% 0.22/0.50  fof(f108,plain,(
% 0.22/0.50    ( ! [X0] : (v4_pre_topc(sK2,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X0,sK0)) ) | (~spl3_2 | ~spl3_5 | ~spl3_7)),
% 0.22/0.50    inference(subsumption_resolution,[],[f107,f77])).
% 0.22/0.50  fof(f77,plain,(
% 0.22/0.50    v4_pre_topc(sK2,sK0) | ~spl3_5),
% 0.22/0.50    inference(avatar_component_clause,[],[f75])).
% 0.22/0.50  fof(f75,plain,(
% 0.22/0.50    spl3_5 <=> v4_pre_topc(sK2,sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.50  fof(f107,plain,(
% 0.22/0.50    ( ! [X0] : (~m1_pre_topc(X0,sK0) | ~v4_pre_topc(sK2,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) | v4_pre_topc(sK2,X0)) ) | (~spl3_2 | ~spl3_7)),
% 0.22/0.50    inference(subsumption_resolution,[],[f103,f62])).
% 0.22/0.50  fof(f103,plain,(
% 0.22/0.50    ( ! [X0] : (~l1_pre_topc(sK0) | ~m1_pre_topc(X0,sK0) | ~v4_pre_topc(sK2,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) | v4_pre_topc(sK2,X0)) ) | ~spl3_7),
% 0.22/0.50    inference(resolution,[],[f91,f52])).
% 0.22/0.50  fof(f52,plain,(
% 0.22/0.50    ( ! [X2,X0,X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~m1_pre_topc(X2,X0) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | v4_pre_topc(X3,X2)) )),
% 0.22/0.50    inference(equality_resolution,[],[f43])).
% 0.22/0.50  fof(f43,plain,(
% 0.22/0.50    ( ! [X2,X0,X3,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X2,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | X1 != X3 | v4_pre_topc(X3,X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f21])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (v4_pre_topc(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) | ~v4_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.50    inference(flattening,[],[f20])).
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : ((v4_pre_topc(X3,X2) | X1 != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) | ~v4_pre_topc(X1,X0)) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f7])).
% 0.22/0.50  fof(f7,axiom,(
% 0.22/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_pre_topc(X2,X0) => (v4_pre_topc(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) => (X1 = X3 => v4_pre_topc(X3,X2)))))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_tops_2)).
% 0.22/0.50  fof(f409,plain,(
% 0.22/0.50    ~v4_pre_topc(sK2,k1_pre_topc(sK0,sK1)) | spl3_47),
% 0.22/0.50    inference(avatar_component_clause,[],[f407])).
% 0.22/0.50  fof(f407,plain,(
% 0.22/0.50    spl3_47 <=> v4_pre_topc(sK2,k1_pre_topc(sK0,sK1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).
% 0.22/0.50  fof(f410,plain,(
% 0.22/0.50    ~spl3_47 | ~spl3_9 | ~spl3_33 | spl3_46),
% 0.22/0.50    inference(avatar_split_clause,[],[f405,f400,f290,f99,f407])).
% 0.22/0.50  fof(f290,plain,(
% 0.22/0.50    spl3_33 <=> ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(sK1)) | v2_compts_1(X2,k1_pre_topc(sK0,sK1)) | ~v4_pre_topc(X2,k1_pre_topc(sK0,sK1)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).
% 0.22/0.50  fof(f400,plain,(
% 0.22/0.50    spl3_46 <=> v2_compts_1(sK2,k1_pre_topc(sK0,sK1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).
% 0.22/0.50  fof(f405,plain,(
% 0.22/0.50    ~v4_pre_topc(sK2,k1_pre_topc(sK0,sK1)) | (~spl3_9 | ~spl3_33 | spl3_46)),
% 0.22/0.50    inference(subsumption_resolution,[],[f404,f101])).
% 0.22/0.50  fof(f404,plain,(
% 0.22/0.50    ~m1_subset_1(sK2,k1_zfmisc_1(sK1)) | ~v4_pre_topc(sK2,k1_pre_topc(sK0,sK1)) | (~spl3_33 | spl3_46)),
% 0.22/0.50    inference(resolution,[],[f402,f291])).
% 0.22/0.50  fof(f291,plain,(
% 0.22/0.50    ( ! [X2] : (v2_compts_1(X2,k1_pre_topc(sK0,sK1)) | ~m1_subset_1(X2,k1_zfmisc_1(sK1)) | ~v4_pre_topc(X2,k1_pre_topc(sK0,sK1))) ) | ~spl3_33),
% 0.22/0.50    inference(avatar_component_clause,[],[f290])).
% 0.22/0.50  fof(f402,plain,(
% 0.22/0.50    ~v2_compts_1(sK2,k1_pre_topc(sK0,sK1)) | spl3_46),
% 0.22/0.50    inference(avatar_component_clause,[],[f400])).
% 0.22/0.50  fof(f403,plain,(
% 0.22/0.50    ~spl3_46 | ~spl3_9 | ~spl3_14 | ~spl3_18 | spl3_19 | spl3_20 | ~spl3_23 | ~spl3_36),
% 0.22/0.50    inference(avatar_split_clause,[],[f351,f331,f216,f201,f197,f184,f150,f99,f400])).
% 0.22/0.50  fof(f184,plain,(
% 0.22/0.50    spl3_18 <=> v2_pre_topc(k1_pre_topc(sK0,sK1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.22/0.50  fof(f197,plain,(
% 0.22/0.50    spl3_19 <=> v1_compts_1(k1_pre_topc(sK0,sK2))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.22/0.50  fof(f331,plain,(
% 0.22/0.50    spl3_36 <=> k1_pre_topc(sK0,sK2) = k1_pre_topc(k1_pre_topc(sK0,sK1),sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).
% 0.22/0.50  fof(f351,plain,(
% 0.22/0.50    ~v2_compts_1(sK2,k1_pre_topc(sK0,sK1)) | (~spl3_9 | ~spl3_14 | ~spl3_18 | spl3_19 | spl3_20 | ~spl3_23 | ~spl3_36)),
% 0.22/0.50    inference(subsumption_resolution,[],[f350,f101])).
% 0.22/0.50  fof(f350,plain,(
% 0.22/0.50    ~m1_subset_1(sK2,k1_zfmisc_1(sK1)) | ~v2_compts_1(sK2,k1_pre_topc(sK0,sK1)) | (~spl3_14 | ~spl3_18 | spl3_19 | spl3_20 | ~spl3_23 | ~spl3_36)),
% 0.22/0.50    inference(forward_demodulation,[],[f349,f152])).
% 0.22/0.50  fof(f349,plain,(
% 0.22/0.50    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1)))) | ~v2_compts_1(sK2,k1_pre_topc(sK0,sK1)) | (~spl3_18 | spl3_19 | spl3_20 | ~spl3_23 | ~spl3_36)),
% 0.22/0.50    inference(subsumption_resolution,[],[f348,f217])).
% 0.22/0.50  fof(f348,plain,(
% 0.22/0.50    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1)))) | ~l1_pre_topc(k1_pre_topc(sK0,sK1)) | ~v2_compts_1(sK2,k1_pre_topc(sK0,sK1)) | (~spl3_18 | spl3_19 | spl3_20 | ~spl3_36)),
% 0.22/0.50    inference(subsumption_resolution,[],[f347,f202])).
% 0.22/0.50  fof(f202,plain,(
% 0.22/0.50    k1_xboole_0 != sK2 | spl3_20),
% 0.22/0.50    inference(avatar_component_clause,[],[f201])).
% 0.22/0.50  fof(f347,plain,(
% 0.22/0.50    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1)))) | k1_xboole_0 = sK2 | ~l1_pre_topc(k1_pre_topc(sK0,sK1)) | ~v2_compts_1(sK2,k1_pre_topc(sK0,sK1)) | (~spl3_18 | spl3_19 | ~spl3_36)),
% 0.22/0.50    inference(subsumption_resolution,[],[f346,f186])).
% 0.22/0.50  fof(f186,plain,(
% 0.22/0.50    v2_pre_topc(k1_pre_topc(sK0,sK1)) | ~spl3_18),
% 0.22/0.50    inference(avatar_component_clause,[],[f184])).
% 0.22/0.50  fof(f346,plain,(
% 0.22/0.50    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1)))) | ~v2_pre_topc(k1_pre_topc(sK0,sK1)) | k1_xboole_0 = sK2 | ~l1_pre_topc(k1_pre_topc(sK0,sK1)) | ~v2_compts_1(sK2,k1_pre_topc(sK0,sK1)) | (spl3_19 | ~spl3_36)),
% 0.22/0.50    inference(subsumption_resolution,[],[f339,f199])).
% 0.22/0.50  fof(f199,plain,(
% 0.22/0.50    ~v1_compts_1(k1_pre_topc(sK0,sK2)) | spl3_19),
% 0.22/0.50    inference(avatar_component_clause,[],[f197])).
% 0.22/0.50  fof(f339,plain,(
% 0.22/0.50    v1_compts_1(k1_pre_topc(sK0,sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1)))) | ~v2_pre_topc(k1_pre_topc(sK0,sK1)) | k1_xboole_0 = sK2 | ~l1_pre_topc(k1_pre_topc(sK0,sK1)) | ~v2_compts_1(sK2,k1_pre_topc(sK0,sK1)) | ~spl3_36),
% 0.22/0.50    inference(superposition,[],[f39,f333])).
% 0.22/0.50  fof(f333,plain,(
% 0.22/0.50    k1_pre_topc(sK0,sK2) = k1_pre_topc(k1_pre_topc(sK0,sK1),sK2) | ~spl3_36),
% 0.22/0.50    inference(avatar_component_clause,[],[f331])).
% 0.22/0.50  fof(f39,plain,(
% 0.22/0.50    ( ! [X0,X1] : (v1_compts_1(k1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | k1_xboole_0 = X1 | ~l1_pre_topc(X0) | ~v2_compts_1(X1,X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f17])).
% 0.22/0.50  fof(f377,plain,(
% 0.22/0.50    ~spl3_2 | ~spl3_8 | spl3_40),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f376])).
% 0.22/0.50  fof(f376,plain,(
% 0.22/0.50    $false | (~spl3_2 | ~spl3_8 | spl3_40)),
% 0.22/0.50    inference(subsumption_resolution,[],[f375,f62])).
% 0.22/0.50  fof(f375,plain,(
% 0.22/0.50    ~l1_pre_topc(sK0) | (~spl3_8 | spl3_40)),
% 0.22/0.50    inference(subsumption_resolution,[],[f374,f96])).
% 0.22/0.50  fof(f96,plain,(
% 0.22/0.50    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_8),
% 0.22/0.50    inference(avatar_component_clause,[],[f94])).
% 0.22/0.50  fof(f94,plain,(
% 0.22/0.50    spl3_8 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.50  fof(f374,plain,(
% 0.22/0.50    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl3_40),
% 0.22/0.50    inference(resolution,[],[f369,f47])).
% 0.22/0.50  fof(f47,plain,(
% 0.22/0.50    ( ! [X0,X1] : (m1_pre_topc(k1_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f27])).
% 0.22/0.50  fof(f27,plain,(
% 0.22/0.50    ! [X0,X1] : ((m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.22/0.50    inference(flattening,[],[f26])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    ! [X0,X1] : ((m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => (m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_pre_topc)).
% 0.22/0.50  fof(f369,plain,(
% 0.22/0.50    ~m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) | spl3_40),
% 0.22/0.50    inference(avatar_component_clause,[],[f367])).
% 0.22/0.50  fof(f334,plain,(
% 0.22/0.50    spl3_36 | ~spl3_1 | ~spl3_2 | ~spl3_4 | ~spl3_7 | ~spl3_8 | ~spl3_9 | ~spl3_14),
% 0.22/0.50    inference(avatar_split_clause,[],[f322,f150,f99,f94,f89,f70,f60,f55,f331])).
% 0.22/0.50  fof(f55,plain,(
% 0.22/0.50    spl3_1 <=> v2_pre_topc(sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.50  fof(f70,plain,(
% 0.22/0.50    spl3_4 <=> r1_tarski(sK2,sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.50  fof(f322,plain,(
% 0.22/0.50    k1_pre_topc(sK0,sK2) = k1_pre_topc(k1_pre_topc(sK0,sK1),sK2) | (~spl3_1 | ~spl3_2 | ~spl3_4 | ~spl3_7 | ~spl3_8 | ~spl3_9 | ~spl3_14)),
% 0.22/0.50    inference(subsumption_resolution,[],[f321,f72])).
% 0.22/0.50  fof(f72,plain,(
% 0.22/0.50    r1_tarski(sK2,sK1) | ~spl3_4),
% 0.22/0.50    inference(avatar_component_clause,[],[f70])).
% 0.22/0.50  fof(f321,plain,(
% 0.22/0.50    ~r1_tarski(sK2,sK1) | k1_pre_topc(sK0,sK2) = k1_pre_topc(k1_pre_topc(sK0,sK1),sK2) | (~spl3_1 | ~spl3_2 | ~spl3_7 | ~spl3_8 | ~spl3_9 | ~spl3_14)),
% 0.22/0.50    inference(subsumption_resolution,[],[f320,f96])).
% 0.22/0.50  fof(f320,plain,(
% 0.22/0.50    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(sK2,sK1) | k1_pre_topc(sK0,sK2) = k1_pre_topc(k1_pre_topc(sK0,sK1),sK2) | (~spl3_1 | ~spl3_2 | ~spl3_7 | ~spl3_9 | ~spl3_14)),
% 0.22/0.50    inference(subsumption_resolution,[],[f317,f101])).
% 0.22/0.50  fof(f317,plain,(
% 0.22/0.50    ~m1_subset_1(sK2,k1_zfmisc_1(sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(sK2,sK1) | k1_pre_topc(sK0,sK2) = k1_pre_topc(k1_pre_topc(sK0,sK1),sK2) | (~spl3_1 | ~spl3_2 | ~spl3_7 | ~spl3_14)),
% 0.22/0.50    inference(superposition,[],[f188,f152])).
% 0.22/0.50  fof(f188,plain,(
% 0.22/0.50    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,X0)))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(sK2,X0) | k1_pre_topc(sK0,sK2) = k1_pre_topc(k1_pre_topc(sK0,X0),sK2)) ) | (~spl3_1 | ~spl3_2 | ~spl3_7)),
% 0.22/0.50    inference(resolution,[],[f182,f91])).
% 0.22/0.50  fof(f182,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,X1)))) | ~r1_tarski(X0,X1) | k1_pre_topc(k1_pre_topc(sK0,X1),X0) = k1_pre_topc(sK0,X0)) ) | (~spl3_1 | ~spl3_2)),
% 0.22/0.50    inference(subsumption_resolution,[],[f84,f62])).
% 0.22/0.50  fof(f84,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~l1_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,X1)))) | ~r1_tarski(X0,X1) | k1_pre_topc(k1_pre_topc(sK0,X1),X0) = k1_pre_topc(sK0,X0)) ) | ~spl3_1),
% 0.22/0.50    inference(resolution,[],[f57,f53])).
% 0.22/0.50  fof(f53,plain,(
% 0.22/0.50    ( ! [X2,X0,X3] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X2)))) | ~r1_tarski(X3,X2) | k1_pre_topc(k1_pre_topc(X0,X2),X3) = k1_pre_topc(X0,X3)) )),
% 0.22/0.50    inference(equality_resolution,[],[f45])).
% 0.22/0.50  fof(f45,plain,(
% 0.22/0.50    ( ! [X2,X0,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X2)))) | X1 != X3 | ~r1_tarski(X1,X2) | k1_pre_topc(X0,X1) = k1_pre_topc(k1_pre_topc(X0,X2),X3)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f25])).
% 0.22/0.50  fof(f25,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k1_pre_topc(X0,X1) = k1_pre_topc(k1_pre_topc(X0,X2),X3) | ~r1_tarski(X1,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X2))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.50    inference(flattening,[],[f24])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k1_pre_topc(X0,X1) = k1_pre_topc(k1_pre_topc(X0,X2),X3) | (~r1_tarski(X1,X2) | X1 != X3)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X2))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f5])).
% 0.22/0.50  fof(f5,axiom,(
% 0.22/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X2)))) => ((r1_tarski(X1,X2) & X1 = X3) => k1_pre_topc(X0,X1) = k1_pre_topc(k1_pre_topc(X0,X2),X3))))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_pre_topc)).
% 0.22/0.50  fof(f57,plain,(
% 0.22/0.50    v2_pre_topc(sK0) | ~spl3_1),
% 0.22/0.50    inference(avatar_component_clause,[],[f55])).
% 0.22/0.50  fof(f303,plain,(
% 0.22/0.50    spl3_34 | ~spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_8 | spl3_32),
% 0.22/0.50    inference(avatar_split_clause,[],[f297,f286,f94,f65,f60,f55,f300])).
% 0.22/0.50  fof(f286,plain,(
% 0.22/0.50    spl3_32 <=> v1_compts_1(k1_pre_topc(sK0,sK1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 0.22/0.50  fof(f297,plain,(
% 0.22/0.50    k1_xboole_0 = sK1 | (~spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_8 | spl3_32)),
% 0.22/0.50    inference(subsumption_resolution,[],[f296,f67])).
% 0.22/0.50  fof(f296,plain,(
% 0.22/0.50    k1_xboole_0 = sK1 | ~v2_compts_1(sK1,sK0) | (~spl3_1 | ~spl3_2 | ~spl3_8 | spl3_32)),
% 0.22/0.50    inference(subsumption_resolution,[],[f295,f62])).
% 0.22/0.50  fof(f295,plain,(
% 0.22/0.50    k1_xboole_0 = sK1 | ~l1_pre_topc(sK0) | ~v2_compts_1(sK1,sK0) | (~spl3_1 | ~spl3_8 | spl3_32)),
% 0.22/0.50    inference(subsumption_resolution,[],[f294,f57])).
% 0.22/0.50  fof(f294,plain,(
% 0.22/0.50    ~v2_pre_topc(sK0) | k1_xboole_0 = sK1 | ~l1_pre_topc(sK0) | ~v2_compts_1(sK1,sK0) | (~spl3_8 | spl3_32)),
% 0.22/0.50    inference(subsumption_resolution,[],[f293,f96])).
% 0.22/0.50  fof(f293,plain,(
% 0.22/0.50    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | k1_xboole_0 = sK1 | ~l1_pre_topc(sK0) | ~v2_compts_1(sK1,sK0) | spl3_32),
% 0.22/0.50    inference(resolution,[],[f288,f39])).
% 0.22/0.50  fof(f288,plain,(
% 0.22/0.50    ~v1_compts_1(k1_pre_topc(sK0,sK1)) | spl3_32),
% 0.22/0.50    inference(avatar_component_clause,[],[f286])).
% 0.22/0.50  fof(f292,plain,(
% 0.22/0.50    ~spl3_32 | spl3_33 | ~spl3_14 | ~spl3_23),
% 0.22/0.50    inference(avatar_split_clause,[],[f281,f216,f150,f290,f286])).
% 0.22/0.50  fof(f281,plain,(
% 0.22/0.50    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(sK1)) | ~v1_compts_1(k1_pre_topc(sK0,sK1)) | ~v4_pre_topc(X2,k1_pre_topc(sK0,sK1)) | v2_compts_1(X2,k1_pre_topc(sK0,sK1))) ) | (~spl3_14 | ~spl3_23)),
% 0.22/0.50    inference(subsumption_resolution,[],[f155,f217])).
% 0.22/0.50  fof(f155,plain,(
% 0.22/0.50    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(sK1)) | ~l1_pre_topc(k1_pre_topc(sK0,sK1)) | ~v1_compts_1(k1_pre_topc(sK0,sK1)) | ~v4_pre_topc(X2,k1_pre_topc(sK0,sK1)) | v2_compts_1(X2,k1_pre_topc(sK0,sK1))) ) | ~spl3_14),
% 0.22/0.50    inference(superposition,[],[f42,f152])).
% 0.22/0.50  fof(f42,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v1_compts_1(X0) | ~v4_pre_topc(X1,X0) | v2_compts_1(X1,X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f19])).
% 0.22/0.50  fof(f19,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (v2_compts_1(X1,X0) | ~v4_pre_topc(X1,X0) | ~v1_compts_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.50    inference(flattening,[],[f18])).
% 0.22/0.50  fof(f18,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : ((v2_compts_1(X1,X0) | (~v4_pre_topc(X1,X0) | ~v1_compts_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f9])).
% 0.22/0.50  fof(f9,axiom,(
% 0.22/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X1,X0) & v1_compts_1(X0)) => v2_compts_1(X1,X0))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_compts_1)).
% 0.22/0.50  fof(f233,plain,(
% 0.22/0.50    ~spl3_2 | ~spl3_8 | spl3_23),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f232])).
% 0.22/0.50  fof(f232,plain,(
% 0.22/0.50    $false | (~spl3_2 | ~spl3_8 | spl3_23)),
% 0.22/0.50    inference(subsumption_resolution,[],[f231,f96])).
% 0.22/0.50  fof(f231,plain,(
% 0.22/0.50    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_2 | spl3_23)),
% 0.22/0.50    inference(subsumption_resolution,[],[f230,f62])).
% 0.22/0.50  fof(f230,plain,(
% 0.22/0.50    ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_23),
% 0.22/0.50    inference(duplicate_literal_removal,[],[f229])).
% 0.22/0.50  fof(f229,plain,(
% 0.22/0.50    ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl3_23),
% 0.22/0.50    inference(resolution,[],[f223,f47])).
% 0.22/0.50  fof(f223,plain,(
% 0.22/0.50    ( ! [X0] : (~m1_pre_topc(k1_pre_topc(sK0,sK1),X0) | ~l1_pre_topc(X0)) ) | spl3_23),
% 0.22/0.50    inference(resolution,[],[f218,f36])).
% 0.22/0.50  fof(f36,plain,(
% 0.22/0.50    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f14])).
% 0.22/0.50  fof(f14,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.22/0.50  fof(f218,plain,(
% 0.22/0.50    ~l1_pre_topc(k1_pre_topc(sK0,sK1)) | spl3_23),
% 0.22/0.50    inference(avatar_component_clause,[],[f216])).
% 0.22/0.50  fof(f204,plain,(
% 0.22/0.50    ~spl3_19 | spl3_20 | ~spl3_1 | ~spl3_2 | spl3_6 | ~spl3_7),
% 0.22/0.50    inference(avatar_split_clause,[],[f175,f89,f80,f60,f55,f201,f197])).
% 0.22/0.50  fof(f80,plain,(
% 0.22/0.50    spl3_6 <=> v2_compts_1(sK2,sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.50  fof(f175,plain,(
% 0.22/0.50    k1_xboole_0 = sK2 | ~v1_compts_1(k1_pre_topc(sK0,sK2)) | (~spl3_1 | ~spl3_2 | spl3_6 | ~spl3_7)),
% 0.22/0.50    inference(subsumption_resolution,[],[f174,f91])).
% 0.22/0.50  fof(f174,plain,(
% 0.22/0.50    k1_xboole_0 = sK2 | ~v1_compts_1(k1_pre_topc(sK0,sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_1 | ~spl3_2 | spl3_6)),
% 0.22/0.50    inference(resolution,[],[f173,f82])).
% 0.22/0.50  fof(f82,plain,(
% 0.22/0.50    ~v2_compts_1(sK2,sK0) | spl3_6),
% 0.22/0.50    inference(avatar_component_clause,[],[f80])).
% 0.22/0.50  fof(f173,plain,(
% 0.22/0.50    ( ! [X3] : (v2_compts_1(X3,sK0) | k1_xboole_0 = X3 | ~v1_compts_1(k1_pre_topc(sK0,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl3_1 | ~spl3_2)),
% 0.22/0.50    inference(subsumption_resolution,[],[f86,f62])).
% 0.22/0.50  fof(f86,plain,(
% 0.22/0.50    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | k1_xboole_0 = X3 | ~v1_compts_1(k1_pre_topc(sK0,X3)) | v2_compts_1(X3,sK0)) ) | ~spl3_1),
% 0.22/0.50    inference(resolution,[],[f57,f38])).
% 0.22/0.50  fof(f38,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k1_xboole_0 = X1 | ~v1_compts_1(k1_pre_topc(X0,X1)) | v2_compts_1(X1,X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f17])).
% 0.22/0.50  fof(f187,plain,(
% 0.22/0.50    spl3_18 | ~spl3_1 | ~spl3_2 | ~spl3_8),
% 0.22/0.50    inference(avatar_split_clause,[],[f159,f94,f60,f55,f184])).
% 0.22/0.50  fof(f159,plain,(
% 0.22/0.50    v2_pre_topc(k1_pre_topc(sK0,sK1)) | (~spl3_1 | ~spl3_2 | ~spl3_8)),
% 0.22/0.50    inference(resolution,[],[f139,f96])).
% 0.22/0.50  fof(f139,plain,(
% 0.22/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v2_pre_topc(k1_pre_topc(sK0,X0))) ) | (~spl3_1 | ~spl3_2)),
% 0.22/0.50    inference(subsumption_resolution,[],[f138,f62])).
% 0.22/0.50  fof(f138,plain,(
% 0.22/0.50    ( ! [X0] : (v2_pre_topc(k1_pre_topc(sK0,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) ) | (~spl3_1 | ~spl3_2)),
% 0.22/0.50    inference(resolution,[],[f137,f47])).
% 0.22/0.50  fof(f137,plain,(
% 0.22/0.50    ( ! [X2] : (~m1_pre_topc(X2,sK0) | v2_pre_topc(X2)) ) | (~spl3_1 | ~spl3_2)),
% 0.22/0.50    inference(subsumption_resolution,[],[f85,f62])).
% 0.22/0.50  fof(f85,plain,(
% 0.22/0.50    ( ! [X2] : (~l1_pre_topc(sK0) | ~m1_pre_topc(X2,sK0) | v2_pre_topc(X2)) ) | ~spl3_1),
% 0.22/0.50    inference(resolution,[],[f57,f44])).
% 0.22/0.50  fof(f44,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v2_pre_topc(X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f23])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.50    inference(flattening,[],[f22])).
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).
% 0.22/0.50  fof(f153,plain,(
% 0.22/0.50    spl3_14 | ~spl3_2 | ~spl3_8),
% 0.22/0.50    inference(avatar_split_clause,[],[f119,f94,f60,f150])).
% 0.22/0.50  fof(f119,plain,(
% 0.22/0.50    sK1 = u1_struct_0(k1_pre_topc(sK0,sK1)) | (~spl3_2 | ~spl3_8)),
% 0.22/0.50    inference(subsumption_resolution,[],[f116,f62])).
% 0.22/0.50  fof(f116,plain,(
% 0.22/0.50    ~l1_pre_topc(sK0) | sK1 = u1_struct_0(k1_pre_topc(sK0,sK1)) | ~spl3_8),
% 0.22/0.50    inference(resolution,[],[f96,f37])).
% 0.22/0.50  fof(f37,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | u1_struct_0(k1_pre_topc(X0,X1)) = X1) )),
% 0.22/0.50    inference(cnf_transformation,[],[f15])).
% 0.22/0.50  fof(f15,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f6])).
% 0.22/0.50  fof(f6,axiom,(
% 0.22/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => u1_struct_0(k1_pre_topc(X0,X1)) = X1))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_pre_topc)).
% 0.22/0.50  fof(f102,plain,(
% 0.22/0.50    spl3_9 | ~spl3_4),
% 0.22/0.50    inference(avatar_split_clause,[],[f87,f70,f99])).
% 0.22/0.50  fof(f87,plain,(
% 0.22/0.50    m1_subset_1(sK2,k1_zfmisc_1(sK1)) | ~spl3_4),
% 0.22/0.50    inference(resolution,[],[f72,f48])).
% 0.22/0.50  fof(f48,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.50  fof(f97,plain,(
% 0.22/0.50    spl3_8),
% 0.22/0.50    inference(avatar_split_clause,[],[f33,f94])).
% 0.22/0.50  fof(f33,plain,(
% 0.22/0.50    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.50    inference(cnf_transformation,[],[f13])).
% 0.22/0.50  fof(f13,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (? [X2] : (~v2_compts_1(X2,X0) & v4_pre_topc(X2,X0) & r1_tarski(X2,X1) & v2_compts_1(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.22/0.50    inference(flattening,[],[f12])).
% 0.22/0.50  fof(f12,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (? [X2] : ((~v2_compts_1(X2,X0) & (v4_pre_topc(X2,X0) & r1_tarski(X2,X1) & v2_compts_1(X1,X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f11])).
% 0.22/0.50  fof(f11,negated_conjecture,(
% 0.22/0.50    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X2,X0) & r1_tarski(X2,X1) & v2_compts_1(X1,X0)) => v2_compts_1(X2,X0)))))),
% 0.22/0.50    inference(negated_conjecture,[],[f10])).
% 0.22/0.50  fof(f10,conjecture,(
% 0.22/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X2,X0) & r1_tarski(X2,X1) & v2_compts_1(X1,X0)) => v2_compts_1(X2,X0)))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_compts_1)).
% 0.22/0.50  fof(f92,plain,(
% 0.22/0.50    spl3_7),
% 0.22/0.50    inference(avatar_split_clause,[],[f28,f89])).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.50    inference(cnf_transformation,[],[f13])).
% 0.22/0.50  fof(f83,plain,(
% 0.22/0.50    ~spl3_6),
% 0.22/0.50    inference(avatar_split_clause,[],[f32,f80])).
% 0.22/0.50  fof(f32,plain,(
% 0.22/0.50    ~v2_compts_1(sK2,sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f13])).
% 0.22/0.50  fof(f78,plain,(
% 0.22/0.50    spl3_5),
% 0.22/0.50    inference(avatar_split_clause,[],[f31,f75])).
% 0.22/0.50  fof(f31,plain,(
% 0.22/0.50    v4_pre_topc(sK2,sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f13])).
% 0.22/0.50  fof(f73,plain,(
% 0.22/0.50    spl3_4),
% 0.22/0.50    inference(avatar_split_clause,[],[f30,f70])).
% 0.22/0.50  fof(f30,plain,(
% 0.22/0.50    r1_tarski(sK2,sK1)),
% 0.22/0.50    inference(cnf_transformation,[],[f13])).
% 0.22/0.50  fof(f68,plain,(
% 0.22/0.50    spl3_3),
% 0.22/0.50    inference(avatar_split_clause,[],[f29,f65])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    v2_compts_1(sK1,sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f13])).
% 0.22/0.50  fof(f63,plain,(
% 0.22/0.50    spl3_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f35,f60])).
% 0.22/0.50  fof(f35,plain,(
% 0.22/0.50    l1_pre_topc(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f13])).
% 0.22/0.50  fof(f58,plain,(
% 0.22/0.50    spl3_1),
% 0.22/0.50    inference(avatar_split_clause,[],[f34,f55])).
% 0.22/0.50  fof(f34,plain,(
% 0.22/0.50    v2_pre_topc(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f13])).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (19887)------------------------------
% 0.22/0.50  % (19887)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (19887)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (19887)Memory used [KB]: 10874
% 0.22/0.50  % (19887)Time elapsed: 0.080 s
% 0.22/0.50  % (19887)------------------------------
% 0.22/0.50  % (19887)------------------------------
% 0.22/0.50  % (19893)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.50  % (19896)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.50  % (19883)Success in time 0.137 s
%------------------------------------------------------------------------------
