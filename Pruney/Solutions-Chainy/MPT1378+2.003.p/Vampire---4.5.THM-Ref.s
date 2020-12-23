%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:55 EST 2020

% Result     : Theorem 2.11s
% Output     : Refutation 2.11s
% Verified   : 
% Statistics : Number of formulae       :  431 (1672 expanded)
%              Number of leaves         :   80 ( 622 expanded)
%              Depth                    :   15
%              Number of atoms          : 1408 (4892 expanded)
%              Number of equality atoms :  207 ( 900 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3330,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f51,f56,f61,f66,f71,f76,f81,f86,f91,f103,f108,f117,f122,f132,f141,f222,f227,f242,f255,f260,f286,f305,f327,f338,f348,f360,f369,f386,f403,f404,f405,f419,f424,f464,f497,f521,f562,f598,f614,f657,f703,f747,f770,f994,f1175,f1750,f1871,f1880,f1944,f1949,f1954,f1970,f1975,f1980,f2315,f2365,f2538,f2540,f2544,f2546,f2548,f2744,f2800,f2892,f2897,f2992,f2997,f3090,f3134,f3197,f3221,f3226,f3326,f3329])).

fof(f3329,plain,
    ( spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_6
    | spl5_21
    | ~ spl5_23
    | ~ spl5_61
    | ~ spl5_66 ),
    inference(avatar_contradiction_clause,[],[f3328])).

fof(f3328,plain,
    ( $false
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_6
    | spl5_21
    | ~ spl5_23
    | ~ spl5_61
    | ~ spl5_66 ),
    inference(subsumption_resolution,[],[f3327,f326])).

fof(f326,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ spl5_23 ),
    inference(avatar_component_clause,[],[f324])).

fof(f324,plain,
    ( spl5_23
  <=> r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f3327,plain,
    ( ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_6
    | spl5_21
    | ~ spl5_61
    | ~ spl5_66 ),
    inference(subsumption_resolution,[],[f3323,f75])).

fof(f75,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl5_6
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f3323,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_21
    | ~ spl5_61
    | ~ spl5_66 ),
    inference(resolution,[],[f3153,f285])).

fof(f285,plain,
    ( ~ m1_connsp_2(k2_xboole_0(sK2,sK3),sK0,sK1)
    | spl5_21 ),
    inference(avatar_component_clause,[],[f283])).

fof(f283,plain,
    ( spl5_21
  <=> m1_connsp_2(k2_xboole_0(sK2,sK3),sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f3153,plain,
    ( ! [X0] :
        ( m1_connsp_2(k2_xboole_0(sK2,sK3),sK0,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,k1_tops_1(sK0,sK2)) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_61
    | ~ spl5_66 ),
    inference(subsumption_resolution,[],[f3152,f2364])).

fof(f2364,plain,
    ( r1_tarski(k2_xboole_0(sK2,sK3),u1_struct_0(sK0))
    | ~ spl5_61 ),
    inference(avatar_component_clause,[],[f2362])).

fof(f2362,plain,
    ( spl5_61
  <=> r1_tarski(k2_xboole_0(sK2,sK3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_61])])).

fof(f3152,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_tops_1(sK0,sK2))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | m1_connsp_2(k2_xboole_0(sK2,sK3),sK0,X0)
        | ~ r1_tarski(k2_xboole_0(sK2,sK3),u1_struct_0(sK0)) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_66 ),
    inference(subsumption_resolution,[],[f3151,f55])).

fof(f55,plain,
    ( v2_pre_topc(sK0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl5_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f3151,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_tops_1(sK0,sK2))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v2_pre_topc(sK0)
        | m1_connsp_2(k2_xboole_0(sK2,sK3),sK0,X0)
        | ~ r1_tarski(k2_xboole_0(sK2,sK3),u1_struct_0(sK0)) )
    | spl5_1
    | ~ spl5_3
    | ~ spl5_66 ),
    inference(subsumption_resolution,[],[f3150,f50])).

fof(f50,plain,
    ( ~ v2_struct_0(sK0)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f48])).

fof(f48,plain,
    ( spl5_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f3150,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_tops_1(sK0,sK2))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | m1_connsp_2(k2_xboole_0(sK2,sK3),sK0,X0)
        | ~ r1_tarski(k2_xboole_0(sK2,sK3),u1_struct_0(sK0)) )
    | ~ spl5_3
    | ~ spl5_66 ),
    inference(subsumption_resolution,[],[f3143,f60])).

fof(f60,plain,
    ( l1_pre_topc(sK0)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl5_3
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f3143,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_tops_1(sK0,sK2))
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | m1_connsp_2(k2_xboole_0(sK2,sK3),sK0,X0)
        | ~ r1_tarski(k2_xboole_0(sK2,sK3),u1_struct_0(sK0)) )
    | ~ spl5_66 ),
    inference(resolution,[],[f3093,f292])).

fof(f292,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | m1_connsp_2(X2,X0,X1)
      | ~ r1_tarski(X2,u1_struct_0(X0)) ) ),
    inference(resolution,[],[f30,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0)
      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | m1_connsp_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_connsp_2)).

fof(f3093,plain,
    ( ! [X1] :
        ( r2_hidden(X1,k1_tops_1(sK0,k2_xboole_0(sK2,sK3)))
        | ~ r2_hidden(X1,k1_tops_1(sK0,sK2)) )
    | ~ spl5_66 ),
    inference(superposition,[],[f45,f2996])).

fof(f2996,plain,
    ( k1_tops_1(sK0,k2_xboole_0(sK2,sK3)) = k2_xboole_0(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k2_xboole_0(sK2,sK3)))
    | ~ spl5_66 ),
    inference(avatar_component_clause,[],[f2994])).

fof(f2994,plain,
    ( spl5_66
  <=> k1_tops_1(sK0,k2_xboole_0(sK2,sK3)) = k2_xboole_0(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k2_xboole_0(sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_66])])).

fof(f45,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f3326,plain,
    ( spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_6
    | spl5_21
    | ~ spl5_23
    | ~ spl5_61
    | ~ spl5_66 ),
    inference(avatar_contradiction_clause,[],[f3322])).

fof(f3322,plain,
    ( $false
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_6
    | spl5_21
    | ~ spl5_23
    | ~ spl5_61
    | ~ spl5_66 ),
    inference(unit_resulting_resolution,[],[f75,f326,f285,f3153])).

fof(f3226,plain,
    ( spl5_71
    | ~ spl5_67 ),
    inference(avatar_split_clause,[],[f3183,f3087,f3223])).

fof(f3223,plain,
    ( spl5_71
  <=> k1_tops_1(sK0,k2_xboole_0(sK2,sK3)) = k2_xboole_0(k1_tops_1(sK0,k2_xboole_0(sK2,sK3)),k1_tops_1(sK0,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_71])])).

fof(f3087,plain,
    ( spl5_67
  <=> k1_tops_1(sK0,k2_xboole_0(sK2,sK3)) = k2_xboole_0(k1_tops_1(sK0,sK3),k1_tops_1(sK0,k2_xboole_0(sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_67])])).

fof(f3183,plain,
    ( k1_tops_1(sK0,k2_xboole_0(sK2,sK3)) = k2_xboole_0(k1_tops_1(sK0,k2_xboole_0(sK2,sK3)),k1_tops_1(sK0,sK3))
    | ~ spl5_67 ),
    inference(superposition,[],[f641,f3089])).

fof(f3089,plain,
    ( k1_tops_1(sK0,k2_xboole_0(sK2,sK3)) = k2_xboole_0(k1_tops_1(sK0,sK3),k1_tops_1(sK0,k2_xboole_0(sK2,sK3)))
    | ~ spl5_67 ),
    inference(avatar_component_clause,[],[f3087])).

fof(f641,plain,(
    ! [X8,X9] : k2_xboole_0(X8,X9) = k2_xboole_0(k2_xboole_0(X8,X9),X8) ),
    inference(subsumption_resolution,[],[f637,f281])).

fof(f281,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK4(X2,X3,X2),X3)
      | k2_xboole_0(X2,X3) = X2 ) ),
    inference(subsumption_resolution,[],[f272,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1,X2),X2)
      | ~ r2_hidden(sK4(X0,X1,X2),X0)
      | k2_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f272,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK4(X2,X3,X2),X2)
      | r2_hidden(sK4(X2,X3,X2),X3)
      | k2_xboole_0(X2,X3) = X2 ) ),
    inference(factoring,[],[f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X2)
      | r2_hidden(sK4(X0,X1,X2),X1)
      | r2_hidden(sK4(X0,X1,X2),X0)
      | k2_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f637,plain,(
    ! [X8,X9] :
      ( k2_xboole_0(X8,X9) = k2_xboole_0(k2_xboole_0(X8,X9),X8)
      | ~ r2_hidden(sK4(k2_xboole_0(X8,X9),X8,k2_xboole_0(X8,X9)),X8) ) ),
    inference(duplicate_literal_removal,[],[f618])).

fof(f618,plain,(
    ! [X8,X9] :
      ( k2_xboole_0(X8,X9) = k2_xboole_0(k2_xboole_0(X8,X9),X8)
      | ~ r2_hidden(sK4(k2_xboole_0(X8,X9),X8,k2_xboole_0(X8,X9)),X8)
      | k2_xboole_0(X8,X9) = k2_xboole_0(k2_xboole_0(X8,X9),X8) ) ),
    inference(resolution,[],[f228,f281])).

fof(f228,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(sK4(X0,X1,k2_xboole_0(X2,X3)),X2)
      | k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)
      | ~ r2_hidden(sK4(X0,X1,k2_xboole_0(X2,X3)),X1) ) ),
    inference(resolution,[],[f39,f45])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1,X2),X2)
      | ~ r2_hidden(sK4(X0,X1,X2),X1)
      | k2_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f3221,plain,
    ( spl5_70
    | ~ spl5_66 ),
    inference(avatar_split_clause,[],[f3120,f2994,f3218])).

fof(f3218,plain,
    ( spl5_70
  <=> k1_tops_1(sK0,k2_xboole_0(sK2,sK3)) = k2_xboole_0(k1_tops_1(sK0,k2_xboole_0(sK2,sK3)),k1_tops_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_70])])).

fof(f3120,plain,
    ( k1_tops_1(sK0,k2_xboole_0(sK2,sK3)) = k2_xboole_0(k1_tops_1(sK0,k2_xboole_0(sK2,sK3)),k1_tops_1(sK0,sK2))
    | ~ spl5_66 ),
    inference(superposition,[],[f641,f2996])).

fof(f3197,plain,
    ( spl5_69
    | ~ spl5_67 ),
    inference(avatar_split_clause,[],[f3154,f3087,f3194])).

fof(f3194,plain,
    ( spl5_69
  <=> r1_tarski(k1_tops_1(sK0,sK3),k1_tops_1(sK0,k2_xboole_0(sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_69])])).

fof(f3154,plain,
    ( r1_tarski(k1_tops_1(sK0,sK3),k1_tops_1(sK0,k2_xboole_0(sK2,sK3)))
    | ~ spl5_67 ),
    inference(superposition,[],[f32,f3089])).

fof(f32,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f3134,plain,
    ( spl5_68
    | ~ spl5_66 ),
    inference(avatar_split_clause,[],[f3091,f2994,f3131])).

fof(f3131,plain,
    ( spl5_68
  <=> r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k2_xboole_0(sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_68])])).

fof(f3091,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k2_xboole_0(sK2,sK3)))
    | ~ spl5_66 ),
    inference(superposition,[],[f32,f2996])).

fof(f3090,plain,
    ( spl5_67
    | ~ spl5_3
    | ~ spl5_7
    | ~ spl5_61 ),
    inference(avatar_split_clause,[],[f2569,f2362,f78,f58,f3087])).

fof(f78,plain,
    ( spl5_7
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f2569,plain,
    ( k1_tops_1(sK0,k2_xboole_0(sK2,sK3)) = k2_xboole_0(k1_tops_1(sK0,sK3),k1_tops_1(sK0,k2_xboole_0(sK2,sK3)))
    | ~ spl5_3
    | ~ spl5_7
    | ~ spl5_61 ),
    inference(subsumption_resolution,[],[f2556,f92])).

fof(f92,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X1,X0)) ),
    inference(superposition,[],[f32,f33])).

fof(f33,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f2556,plain,
    ( ~ r1_tarski(sK3,k2_xboole_0(sK2,sK3))
    | k1_tops_1(sK0,k2_xboole_0(sK2,sK3)) = k2_xboole_0(k1_tops_1(sK0,sK3),k1_tops_1(sK0,k2_xboole_0(sK2,sK3)))
    | ~ spl5_3
    | ~ spl5_7
    | ~ spl5_61 ),
    inference(resolution,[],[f2364,f506])).

fof(f506,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK0))
        | ~ r1_tarski(sK3,X0)
        | k1_tops_1(sK0,X0) = k2_xboole_0(k1_tops_1(sK0,sK3),k1_tops_1(sK0,X0)) )
    | ~ spl5_3
    | ~ spl5_7 ),
    inference(resolution,[],[f504,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f504,plain,
    ( ! [X4] :
        ( r1_tarski(k1_tops_1(sK0,sK3),k1_tops_1(sK0,X4))
        | ~ r1_tarski(sK3,X4)
        | ~ r1_tarski(X4,u1_struct_0(sK0)) )
    | ~ spl5_3
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f502,f60])).

fof(f502,plain,
    ( ! [X4] :
        ( ~ l1_pre_topc(sK0)
        | ~ r1_tarski(sK3,X4)
        | r1_tarski(k1_tops_1(sK0,sK3),k1_tops_1(sK0,X4))
        | ~ r1_tarski(X4,u1_struct_0(sK0)) )
    | ~ spl5_7 ),
    inference(resolution,[],[f243,f80])).

fof(f80,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f78])).

fof(f243,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ r1_tarski(X0,X2)
      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
      | ~ r1_tarski(X2,u1_struct_0(X1)) ) ),
    inference(resolution,[],[f29,f35])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).

fof(f2997,plain,
    ( spl5_66
    | ~ spl5_3
    | ~ spl5_8
    | ~ spl5_61 ),
    inference(avatar_split_clause,[],[f2568,f2362,f83,f58,f2994])).

fof(f83,plain,
    ( spl5_8
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f2568,plain,
    ( k1_tops_1(sK0,k2_xboole_0(sK2,sK3)) = k2_xboole_0(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k2_xboole_0(sK2,sK3)))
    | ~ spl5_3
    | ~ spl5_8
    | ~ spl5_61 ),
    inference(subsumption_resolution,[],[f2555,f32])).

fof(f2555,plain,
    ( ~ r1_tarski(sK2,k2_xboole_0(sK2,sK3))
    | k1_tops_1(sK0,k2_xboole_0(sK2,sK3)) = k2_xboole_0(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k2_xboole_0(sK2,sK3)))
    | ~ spl5_3
    | ~ spl5_8
    | ~ spl5_61 ),
    inference(resolution,[],[f2364,f505])).

fof(f505,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK0))
        | ~ r1_tarski(sK2,X0)
        | k1_tops_1(sK0,X0) = k2_xboole_0(k1_tops_1(sK0,sK2),k1_tops_1(sK0,X0)) )
    | ~ spl5_3
    | ~ spl5_8 ),
    inference(resolution,[],[f503,f34])).

fof(f503,plain,
    ( ! [X3] :
        ( r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,X3))
        | ~ r1_tarski(sK2,X3)
        | ~ r1_tarski(X3,u1_struct_0(sK0)) )
    | ~ spl5_3
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f501,f60])).

fof(f501,plain,
    ( ! [X3] :
        ( ~ l1_pre_topc(sK0)
        | ~ r1_tarski(sK2,X3)
        | r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,X3))
        | ~ r1_tarski(X3,u1_struct_0(sK0)) )
    | ~ spl5_8 ),
    inference(resolution,[],[f243,f85])).

fof(f85,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f83])).

fof(f2992,plain,
    ( spl5_65
    | ~ spl5_13
    | ~ spl5_59 ),
    inference(avatar_split_clause,[],[f2360,f2308,f119,f2989])).

fof(f2989,plain,
    ( spl5_65
  <=> k2_xboole_0(sK2,sK3) = k4_subset_1(u1_struct_0(sK0),k2_xboole_0(sK2,sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_65])])).

fof(f119,plain,
    ( spl5_13
  <=> u1_struct_0(sK0) = k2_xboole_0(sK3,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f2308,plain,
    ( spl5_59
  <=> u1_struct_0(sK0) = k2_xboole_0(u1_struct_0(sK0),k2_xboole_0(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_59])])).

fof(f2360,plain,
    ( k2_xboole_0(sK2,sK3) = k4_subset_1(u1_struct_0(sK0),k2_xboole_0(sK2,sK3),sK3)
    | ~ spl5_13
    | ~ spl5_59 ),
    inference(forward_demodulation,[],[f2359,f110])).

fof(f110,plain,(
    ! [X2,X3] : k2_xboole_0(X3,X2) = k2_xboole_0(X2,k2_xboole_0(X3,X2)) ),
    inference(resolution,[],[f34,f92])).

fof(f2359,plain,
    ( k4_subset_1(u1_struct_0(sK0),k2_xboole_0(sK2,sK3),sK3) = k2_xboole_0(sK3,k2_xboole_0(sK2,sK3))
    | ~ spl5_13
    | ~ spl5_59 ),
    inference(forward_demodulation,[],[f2323,f33])).

fof(f2323,plain,
    ( k2_xboole_0(k2_xboole_0(sK2,sK3),sK3) = k4_subset_1(u1_struct_0(sK0),k2_xboole_0(sK2,sK3),sK3)
    | ~ spl5_13
    | ~ spl5_59 ),
    inference(superposition,[],[f1717,f2310])).

fof(f2310,plain,
    ( u1_struct_0(sK0) = k2_xboole_0(u1_struct_0(sK0),k2_xboole_0(sK2,sK3))
    | ~ spl5_59 ),
    inference(avatar_component_clause,[],[f2308])).

fof(f1717,plain,
    ( ! [X1] : k2_xboole_0(X1,sK3) = k4_subset_1(k2_xboole_0(u1_struct_0(sK0),X1),X1,sK3)
    | ~ spl5_13 ),
    inference(resolution,[],[f1666,f92])).

fof(f1666,plain,
    ( ! [X12,X11] :
        ( ~ r1_tarski(X12,k2_xboole_0(u1_struct_0(sK0),X11))
        | k4_subset_1(k2_xboole_0(u1_struct_0(sK0),X11),X12,sK3) = k2_xboole_0(X12,sK3) )
    | ~ spl5_13 ),
    inference(resolution,[],[f451,f1513])).

fof(f1513,plain,
    ( ! [X0] : r1_tarski(sK3,k2_xboole_0(u1_struct_0(sK0),X0))
    | ~ spl5_13 ),
    inference(superposition,[],[f32,f1498])).

fof(f1498,plain,
    ( ! [X7] : k2_xboole_0(u1_struct_0(sK0),X7) = k2_xboole_0(sK3,k2_xboole_0(u1_struct_0(sK0),X7))
    | ~ spl5_13 ),
    inference(subsumption_resolution,[],[f1492,f280])).

fof(f280,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1,X1),X0)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(subsumption_resolution,[],[f271,f39])).

fof(f271,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1,X1),X1)
      | r2_hidden(sK4(X0,X1,X1),X0)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(factoring,[],[f40])).

fof(f1492,plain,
    ( ! [X7] :
        ( ~ r2_hidden(sK4(sK3,k2_xboole_0(u1_struct_0(sK0),X7),k2_xboole_0(u1_struct_0(sK0),X7)),sK3)
        | k2_xboole_0(u1_struct_0(sK0),X7) = k2_xboole_0(sK3,k2_xboole_0(u1_struct_0(sK0),X7)) )
    | ~ spl5_13 ),
    inference(duplicate_literal_removal,[],[f1465])).

fof(f1465,plain,
    ( ! [X7] :
        ( ~ r2_hidden(sK4(sK3,k2_xboole_0(u1_struct_0(sK0),X7),k2_xboole_0(u1_struct_0(sK0),X7)),sK3)
        | k2_xboole_0(u1_struct_0(sK0),X7) = k2_xboole_0(sK3,k2_xboole_0(u1_struct_0(sK0),X7))
        | k2_xboole_0(u1_struct_0(sK0),X7) = k2_xboole_0(sK3,k2_xboole_0(u1_struct_0(sK0),X7)) )
    | ~ spl5_13 ),
    inference(resolution,[],[f529,f280])).

fof(f529,plain,
    ( ! [X24,X23,X22] :
        ( ~ r2_hidden(sK4(X22,X23,k2_xboole_0(u1_struct_0(sK0),X24)),sK3)
        | ~ r2_hidden(sK4(X22,X23,k2_xboole_0(u1_struct_0(sK0),X24)),X22)
        | k2_xboole_0(X22,X23) = k2_xboole_0(u1_struct_0(sK0),X24) )
    | ~ spl5_13 ),
    inference(resolution,[],[f210,f145])).

fof(f145,plain,
    ( ! [X7] :
        ( r2_hidden(X7,u1_struct_0(sK0))
        | ~ r2_hidden(X7,sK3) )
    | ~ spl5_13 ),
    inference(superposition,[],[f45,f121])).

fof(f121,plain,
    ( u1_struct_0(sK0) = k2_xboole_0(sK3,u1_struct_0(sK0))
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f119])).

fof(f210,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(sK4(X0,X1,k2_xboole_0(X2,X3)),X2)
      | k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)
      | ~ r2_hidden(sK4(X0,X1,k2_xboole_0(X2,X3)),X0) ) ),
    inference(resolution,[],[f38,f45])).

fof(f451,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X0)
      | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ r1_tarski(X1,X0) ) ),
    inference(resolution,[],[f207,f35])).

fof(f207,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2)
      | ~ r1_tarski(X2,X1) ) ),
    inference(resolution,[],[f37,f35])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f2897,plain,
    ( spl5_64
    | ~ spl5_7
    | ~ spl5_61 ),
    inference(avatar_split_clause,[],[f2565,f2362,f78,f2894])).

fof(f2894,plain,
    ( spl5_64
  <=> k2_xboole_0(sK2,sK3) = k4_subset_1(u1_struct_0(sK0),sK3,k2_xboole_0(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_64])])).

fof(f2565,plain,
    ( k2_xboole_0(sK2,sK3) = k4_subset_1(u1_struct_0(sK0),sK3,k2_xboole_0(sK2,sK3))
    | ~ spl5_7
    | ~ spl5_61 ),
    inference(forward_demodulation,[],[f2552,f110])).

fof(f2552,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(sK2,sK3)) = k4_subset_1(u1_struct_0(sK0),sK3,k2_xboole_0(sK2,sK3))
    | ~ spl5_7
    | ~ spl5_61 ),
    inference(resolution,[],[f2364,f453])).

fof(f453,plain,
    ( ! [X4] :
        ( ~ r1_tarski(X4,u1_struct_0(sK0))
        | k2_xboole_0(sK3,X4) = k4_subset_1(u1_struct_0(sK0),sK3,X4) )
    | ~ spl5_7 ),
    inference(resolution,[],[f207,f80])).

fof(f2892,plain,
    ( spl5_63
    | ~ spl5_8
    | ~ spl5_61 ),
    inference(avatar_split_clause,[],[f2564,f2362,f83,f2889])).

fof(f2889,plain,
    ( spl5_63
  <=> k2_xboole_0(sK2,sK3) = k4_subset_1(u1_struct_0(sK0),sK2,k2_xboole_0(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_63])])).

fof(f2564,plain,
    ( k2_xboole_0(sK2,sK3) = k4_subset_1(u1_struct_0(sK0),sK2,k2_xboole_0(sK2,sK3))
    | ~ spl5_8
    | ~ spl5_61 ),
    inference(forward_demodulation,[],[f2551,f109])).

fof(f109,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(resolution,[],[f34,f32])).

fof(f2551,plain,
    ( k2_xboole_0(sK2,k2_xboole_0(sK2,sK3)) = k4_subset_1(u1_struct_0(sK0),sK2,k2_xboole_0(sK2,sK3))
    | ~ spl5_8
    | ~ spl5_61 ),
    inference(resolution,[],[f2364,f452])).

fof(f452,plain,
    ( ! [X3] :
        ( ~ r1_tarski(X3,u1_struct_0(sK0))
        | k2_xboole_0(sK2,X3) = k4_subset_1(u1_struct_0(sK0),sK2,X3) )
    | ~ spl5_8 ),
    inference(resolution,[],[f207,f85])).

fof(f2800,plain,
    ( spl5_62
    | ~ spl5_8
    | ~ spl5_61 ),
    inference(avatar_split_clause,[],[f2562,f2362,f83,f2797])).

fof(f2797,plain,
    ( spl5_62
  <=> k2_xboole_0(sK2,sK3) = k4_subset_1(u1_struct_0(sK0),k2_xboole_0(sK2,sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_62])])).

fof(f2562,plain,
    ( k2_xboole_0(sK2,sK3) = k4_subset_1(u1_struct_0(sK0),k2_xboole_0(sK2,sK3),sK2)
    | ~ spl5_8
    | ~ spl5_61 ),
    inference(forward_demodulation,[],[f2561,f109])).

fof(f2561,plain,
    ( k4_subset_1(u1_struct_0(sK0),k2_xboole_0(sK2,sK3),sK2) = k2_xboole_0(sK2,k2_xboole_0(sK2,sK3))
    | ~ spl5_8
    | ~ spl5_61 ),
    inference(forward_demodulation,[],[f2549,f33])).

fof(f2549,plain,
    ( k4_subset_1(u1_struct_0(sK0),k2_xboole_0(sK2,sK3),sK2) = k2_xboole_0(k2_xboole_0(sK2,sK3),sK2)
    | ~ spl5_8
    | ~ spl5_61 ),
    inference(resolution,[],[f2364,f214])).

fof(f214,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK0))
        | k4_subset_1(u1_struct_0(sK0),X0,sK2) = k2_xboole_0(X0,sK2) )
    | ~ spl5_8 ),
    inference(resolution,[],[f208,f35])).

fof(f208,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | k4_subset_1(u1_struct_0(sK0),X3,sK2) = k2_xboole_0(X3,sK2) )
    | ~ spl5_8 ),
    inference(resolution,[],[f37,f85])).

fof(f2744,plain,
    ( spl5_60
    | ~ spl5_59 ),
    inference(avatar_split_clause,[],[f2336,f2308,f2312])).

fof(f2312,plain,
    ( spl5_60
  <=> u1_struct_0(sK0) = k2_xboole_0(k2_xboole_0(sK2,sK3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_60])])).

fof(f2336,plain,
    ( u1_struct_0(sK0) = k2_xboole_0(k2_xboole_0(sK2,sK3),u1_struct_0(sK0))
    | ~ spl5_59 ),
    inference(superposition,[],[f110,f2310])).

fof(f2548,plain,
    ( spl5_59
    | ~ spl5_60 ),
    inference(avatar_contradiction_clause,[],[f2547])).

fof(f2547,plain,
    ( $false
    | spl5_59
    | ~ spl5_60 ),
    inference(subsumption_resolution,[],[f2535,f2309])).

fof(f2309,plain,
    ( u1_struct_0(sK0) != k2_xboole_0(u1_struct_0(sK0),k2_xboole_0(sK2,sK3))
    | spl5_59 ),
    inference(avatar_component_clause,[],[f2308])).

fof(f2535,plain,
    ( u1_struct_0(sK0) = k2_xboole_0(u1_struct_0(sK0),k2_xboole_0(sK2,sK3))
    | ~ spl5_60 ),
    inference(superposition,[],[f641,f2314])).

fof(f2314,plain,
    ( u1_struct_0(sK0) = k2_xboole_0(k2_xboole_0(sK2,sK3),u1_struct_0(sK0))
    | ~ spl5_60 ),
    inference(avatar_component_clause,[],[f2312])).

fof(f2546,plain,
    ( spl5_59
    | ~ spl5_60 ),
    inference(avatar_contradiction_clause,[],[f2545])).

fof(f2545,plain,
    ( $false
    | spl5_59
    | ~ spl5_60 ),
    inference(subsumption_resolution,[],[f2506,f2309])).

fof(f2506,plain,
    ( u1_struct_0(sK0) = k2_xboole_0(u1_struct_0(sK0),k2_xboole_0(sK2,sK3))
    | ~ spl5_60 ),
    inference(superposition,[],[f33,f2314])).

fof(f2544,plain,
    ( spl5_59
    | ~ spl5_60 ),
    inference(avatar_contradiction_clause,[],[f2543])).

fof(f2543,plain,
    ( $false
    | spl5_59
    | ~ spl5_60 ),
    inference(subsumption_resolution,[],[f2505,f2309])).

fof(f2505,plain,
    ( u1_struct_0(sK0) = k2_xboole_0(u1_struct_0(sK0),k2_xboole_0(sK2,sK3))
    | ~ spl5_60 ),
    inference(superposition,[],[f33,f2314])).

fof(f2540,plain,
    ( spl5_59
    | ~ spl5_60 ),
    inference(avatar_contradiction_clause,[],[f2539])).

fof(f2539,plain,
    ( $false
    | spl5_59
    | ~ spl5_60 ),
    inference(subsumption_resolution,[],[f2490,f2309])).

fof(f2490,plain,
    ( u1_struct_0(sK0) = k2_xboole_0(u1_struct_0(sK0),k2_xboole_0(sK2,sK3))
    | ~ spl5_60 ),
    inference(superposition,[],[f2314,f33])).

fof(f2538,plain,
    ( spl5_59
    | ~ spl5_60 ),
    inference(avatar_contradiction_clause,[],[f2537])).

fof(f2537,plain,
    ( $false
    | spl5_59
    | ~ spl5_60 ),
    inference(subsumption_resolution,[],[f2489,f2309])).

fof(f2489,plain,
    ( u1_struct_0(sK0) = k2_xboole_0(u1_struct_0(sK0),k2_xboole_0(sK2,sK3))
    | ~ spl5_60 ),
    inference(superposition,[],[f2314,f33])).

fof(f2365,plain,
    ( spl5_61
    | ~ spl5_59 ),
    inference(avatar_split_clause,[],[f2334,f2308,f2362])).

fof(f2334,plain,
    ( r1_tarski(k2_xboole_0(sK2,sK3),u1_struct_0(sK0))
    | ~ spl5_59 ),
    inference(superposition,[],[f92,f2310])).

fof(f2315,plain,
    ( spl5_59
    | spl5_60
    | ~ spl5_12
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f2288,f119,f114,f2312,f2308])).

fof(f114,plain,
    ( spl5_12
  <=> u1_struct_0(sK0) = k2_xboole_0(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f2288,plain,
    ( u1_struct_0(sK0) = k2_xboole_0(k2_xboole_0(sK2,sK3),u1_struct_0(sK0))
    | u1_struct_0(sK0) = k2_xboole_0(u1_struct_0(sK0),k2_xboole_0(sK2,sK3))
    | ~ spl5_12
    | ~ spl5_13 ),
    inference(forward_demodulation,[],[f2287,f33])).

fof(f2287,plain,
    ( u1_struct_0(sK0) = k2_xboole_0(u1_struct_0(sK0),k2_xboole_0(sK2,sK3))
    | u1_struct_0(sK0) = k2_xboole_0(k2_xboole_0(sK3,sK2),u1_struct_0(sK0))
    | ~ spl5_12
    | ~ spl5_13 ),
    inference(forward_demodulation,[],[f2286,f33])).

fof(f2286,plain,
    ( u1_struct_0(sK0) = k2_xboole_0(u1_struct_0(sK0),k2_xboole_0(sK3,sK2))
    | u1_struct_0(sK0) = k2_xboole_0(k2_xboole_0(sK3,sK2),u1_struct_0(sK0))
    | ~ spl5_12
    | ~ spl5_13 ),
    inference(subsumption_resolution,[],[f2261,f280])).

fof(f2261,plain,
    ( u1_struct_0(sK0) = k2_xboole_0(u1_struct_0(sK0),k2_xboole_0(sK3,sK2))
    | u1_struct_0(sK0) = k2_xboole_0(k2_xboole_0(sK3,sK2),u1_struct_0(sK0))
    | ~ r2_hidden(sK4(k2_xboole_0(sK3,sK2),u1_struct_0(sK0),u1_struct_0(sK0)),k2_xboole_0(sK3,sK2))
    | ~ spl5_12
    | ~ spl5_13 ),
    inference(resolution,[],[f2229,f212])).

fof(f212,plain,
    ( ! [X8,X9] :
        ( ~ r2_hidden(sK4(X8,X9,u1_struct_0(sK0)),sK3)
        | u1_struct_0(sK0) = k2_xboole_0(X8,X9)
        | ~ r2_hidden(sK4(X8,X9,u1_struct_0(sK0)),X8) )
    | ~ spl5_13 ),
    inference(resolution,[],[f38,f145])).

fof(f2229,plain,
    ( ! [X16] :
        ( r2_hidden(sK4(k2_xboole_0(X16,sK2),u1_struct_0(sK0),u1_struct_0(sK0)),X16)
        | u1_struct_0(sK0) = k2_xboole_0(u1_struct_0(sK0),k2_xboole_0(X16,sK2)) )
    | ~ spl5_12 ),
    inference(forward_demodulation,[],[f2228,f33])).

fof(f2228,plain,
    ( ! [X16] :
        ( r2_hidden(sK4(k2_xboole_0(X16,sK2),u1_struct_0(sK0),u1_struct_0(sK0)),X16)
        | u1_struct_0(sK0) = k2_xboole_0(k2_xboole_0(X16,sK2),u1_struct_0(sK0)) )
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f2213,f1447])).

fof(f1447,plain,
    ( ! [X24,X25] :
        ( r2_hidden(sK4(k2_xboole_0(X24,sK2),X25,u1_struct_0(sK0)),u1_struct_0(sK0))
        | r2_hidden(sK4(k2_xboole_0(X24,sK2),X25,u1_struct_0(sK0)),X25)
        | r2_hidden(sK4(k2_xboole_0(X24,sK2),X25,u1_struct_0(sK0)),X24)
        | u1_struct_0(sK0) = k2_xboole_0(k2_xboole_0(X24,sK2),X25) )
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f1425,f40])).

fof(f1425,plain,
    ( ! [X24,X25] :
        ( r2_hidden(sK4(k2_xboole_0(X24,sK2),X25,u1_struct_0(sK0)),u1_struct_0(sK0))
        | r2_hidden(sK4(k2_xboole_0(X24,sK2),X25,u1_struct_0(sK0)),X25)
        | r2_hidden(sK4(k2_xboole_0(X24,sK2),X25,u1_struct_0(sK0)),X24)
        | u1_struct_0(sK0) = k2_xboole_0(k2_xboole_0(X24,sK2),X25)
        | ~ r2_hidden(sK4(k2_xboole_0(X24,sK2),X25,u1_struct_0(sK0)),k2_xboole_0(X24,sK2)) )
    | ~ spl5_12 ),
    inference(duplicate_literal_removal,[],[f1302])).

fof(f1302,plain,
    ( ! [X24,X25] :
        ( r2_hidden(sK4(k2_xboole_0(X24,sK2),X25,u1_struct_0(sK0)),u1_struct_0(sK0))
        | r2_hidden(sK4(k2_xboole_0(X24,sK2),X25,u1_struct_0(sK0)),X25)
        | r2_hidden(sK4(k2_xboole_0(X24,sK2),X25,u1_struct_0(sK0)),X24)
        | u1_struct_0(sK0) = k2_xboole_0(k2_xboole_0(X24,sK2),X25)
        | u1_struct_0(sK0) = k2_xboole_0(k2_xboole_0(X24,sK2),X25)
        | ~ r2_hidden(sK4(k2_xboole_0(X24,sK2),X25,u1_struct_0(sK0)),k2_xboole_0(X24,sK2)) )
    | ~ spl5_12 ),
    inference(resolution,[],[f270,f213])).

fof(f213,plain,
    ( ! [X10,X11] :
        ( ~ r2_hidden(sK4(X10,X11,u1_struct_0(sK0)),sK2)
        | u1_struct_0(sK0) = k2_xboole_0(X10,X11)
        | ~ r2_hidden(sK4(X10,X11,u1_struct_0(sK0)),X10) )
    | ~ spl5_12 ),
    inference(resolution,[],[f38,f144])).

fof(f144,plain,
    ( ! [X6] :
        ( r2_hidden(X6,u1_struct_0(sK0))
        | ~ r2_hidden(X6,sK2) )
    | ~ spl5_12 ),
    inference(superposition,[],[f45,f116])).

fof(f116,plain,
    ( u1_struct_0(sK0) = k2_xboole_0(sK2,u1_struct_0(sK0))
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f114])).

fof(f270,plain,(
    ! [X6,X4,X7,X5] :
      ( r2_hidden(sK4(k2_xboole_0(X4,X5),X6,X7),X7)
      | r2_hidden(sK4(k2_xboole_0(X4,X5),X6,X7),X6)
      | r2_hidden(sK4(k2_xboole_0(X4,X5),X6,X7),X5)
      | r2_hidden(sK4(k2_xboole_0(X4,X5),X6,X7),X4)
      | k2_xboole_0(k2_xboole_0(X4,X5),X6) = X7 ) ),
    inference(resolution,[],[f40,f46])).

fof(f46,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k2_xboole_0(X0,X1))
      | r2_hidden(X3,X1)
      | r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2213,plain,
    ( ! [X16] :
        ( r2_hidden(sK4(k2_xboole_0(X16,sK2),u1_struct_0(sK0),u1_struct_0(sK0)),X16)
        | u1_struct_0(sK0) = k2_xboole_0(k2_xboole_0(X16,sK2),u1_struct_0(sK0))
        | ~ r2_hidden(sK4(k2_xboole_0(X16,sK2),u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0)) )
    | ~ spl5_12 ),
    inference(duplicate_literal_removal,[],[f2121])).

fof(f2121,plain,
    ( ! [X16] :
        ( r2_hidden(sK4(k2_xboole_0(X16,sK2),u1_struct_0(sK0),u1_struct_0(sK0)),X16)
        | u1_struct_0(sK0) = k2_xboole_0(k2_xboole_0(X16,sK2),u1_struct_0(sK0))
        | u1_struct_0(sK0) = k2_xboole_0(k2_xboole_0(X16,sK2),u1_struct_0(sK0))
        | ~ r2_hidden(sK4(k2_xboole_0(X16,sK2),u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0)) )
    | ~ spl5_12 ),
    inference(resolution,[],[f372,f231])).

fof(f231,plain,
    ( ! [X10,X11] :
        ( ~ r2_hidden(sK4(X10,X11,u1_struct_0(sK0)),sK2)
        | u1_struct_0(sK0) = k2_xboole_0(X10,X11)
        | ~ r2_hidden(sK4(X10,X11,u1_struct_0(sK0)),X11) )
    | ~ spl5_12 ),
    inference(resolution,[],[f39,f144])).

fof(f372,plain,(
    ! [X4,X2,X3] :
      ( r2_hidden(sK4(k2_xboole_0(X2,X3),X4,X4),X3)
      | r2_hidden(sK4(k2_xboole_0(X2,X3),X4,X4),X2)
      | k2_xboole_0(k2_xboole_0(X2,X3),X4) = X4 ) ),
    inference(resolution,[],[f280,f46])).

fof(f1980,plain,
    ( spl5_58
    | ~ spl5_42
    | ~ spl5_44 ),
    inference(avatar_split_clause,[],[f1955,f700,f611,f1977])).

fof(f1977,plain,
    ( spl5_58
  <=> k2_xboole_0(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK3)) = k4_subset_1(k1_tops_1(sK0,u1_struct_0(sK0)),k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_58])])).

fof(f611,plain,
    ( spl5_42
  <=> r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_42])])).

fof(f700,plain,
    ( spl5_44
  <=> r1_tarski(k1_tops_1(sK0,sK3),k1_tops_1(sK0,u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_44])])).

fof(f1955,plain,
    ( k2_xboole_0(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK3)) = k4_subset_1(k1_tops_1(sK0,u1_struct_0(sK0)),k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK3))
    | ~ spl5_42
    | ~ spl5_44 ),
    inference(resolution,[],[f1676,f613])).

fof(f613,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,u1_struct_0(sK0)))
    | ~ spl5_42 ),
    inference(avatar_component_clause,[],[f611])).

fof(f1676,plain,
    ( ! [X27] :
        ( ~ r1_tarski(X27,k1_tops_1(sK0,u1_struct_0(sK0)))
        | k2_xboole_0(X27,k1_tops_1(sK0,sK3)) = k4_subset_1(k1_tops_1(sK0,u1_struct_0(sK0)),X27,k1_tops_1(sK0,sK3)) )
    | ~ spl5_44 ),
    inference(resolution,[],[f451,f702])).

fof(f702,plain,
    ( r1_tarski(k1_tops_1(sK0,sK3),k1_tops_1(sK0,u1_struct_0(sK0)))
    | ~ spl5_44 ),
    inference(avatar_component_clause,[],[f700])).

fof(f1975,plain,
    ( spl5_57
    | ~ spl5_43
    | ~ spl5_44 ),
    inference(avatar_split_clause,[],[f1965,f700,f654,f1972])).

fof(f1972,plain,
    ( spl5_57
  <=> k1_tops_1(sK0,u1_struct_0(sK0)) = k4_subset_1(k1_tops_1(sK0,u1_struct_0(sK0)),k1_tops_1(sK0,u1_struct_0(sK0)),k1_tops_1(sK0,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_57])])).

fof(f654,plain,
    ( spl5_43
  <=> k1_tops_1(sK0,u1_struct_0(sK0)) = k2_xboole_0(k1_tops_1(sK0,sK3),k1_tops_1(sK0,u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_43])])).

fof(f1965,plain,
    ( k1_tops_1(sK0,u1_struct_0(sK0)) = k4_subset_1(k1_tops_1(sK0,u1_struct_0(sK0)),k1_tops_1(sK0,u1_struct_0(sK0)),k1_tops_1(sK0,sK3))
    | ~ spl5_43
    | ~ spl5_44 ),
    inference(forward_demodulation,[],[f1964,f656])).

fof(f656,plain,
    ( k1_tops_1(sK0,u1_struct_0(sK0)) = k2_xboole_0(k1_tops_1(sK0,sK3),k1_tops_1(sK0,u1_struct_0(sK0)))
    | ~ spl5_43 ),
    inference(avatar_component_clause,[],[f654])).

fof(f1964,plain,
    ( k2_xboole_0(k1_tops_1(sK0,sK3),k1_tops_1(sK0,u1_struct_0(sK0))) = k4_subset_1(k1_tops_1(sK0,u1_struct_0(sK0)),k1_tops_1(sK0,u1_struct_0(sK0)),k1_tops_1(sK0,sK3))
    | ~ spl5_44 ),
    inference(forward_demodulation,[],[f1959,f33])).

fof(f1959,plain,
    ( k2_xboole_0(k1_tops_1(sK0,u1_struct_0(sK0)),k1_tops_1(sK0,sK3)) = k4_subset_1(k1_tops_1(sK0,u1_struct_0(sK0)),k1_tops_1(sK0,u1_struct_0(sK0)),k1_tops_1(sK0,sK3))
    | ~ spl5_44 ),
    inference(resolution,[],[f1676,f387])).

fof(f387,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(superposition,[],[f32,f377])).

fof(f377,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(subsumption_resolution,[],[f376,f40])).

fof(f376,plain,(
    ! [X0] :
      ( k2_xboole_0(X0,X0) = X0
      | ~ r2_hidden(sK4(X0,X0,X0),X0) ) ),
    inference(duplicate_literal_removal,[],[f370])).

fof(f370,plain,(
    ! [X0] :
      ( k2_xboole_0(X0,X0) = X0
      | ~ r2_hidden(sK4(X0,X0,X0),X0)
      | k2_xboole_0(X0,X0) = X0 ) ),
    inference(resolution,[],[f280,f39])).

fof(f1970,plain,
    ( spl5_56
    | ~ spl5_44 ),
    inference(avatar_split_clause,[],[f1960,f700,f1967])).

fof(f1967,plain,
    ( spl5_56
  <=> k1_tops_1(sK0,sK3) = k4_subset_1(k1_tops_1(sK0,u1_struct_0(sK0)),k1_tops_1(sK0,sK3),k1_tops_1(sK0,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_56])])).

fof(f1960,plain,
    ( k1_tops_1(sK0,sK3) = k4_subset_1(k1_tops_1(sK0,u1_struct_0(sK0)),k1_tops_1(sK0,sK3),k1_tops_1(sK0,sK3))
    | ~ spl5_44 ),
    inference(forward_demodulation,[],[f1957,f377])).

fof(f1957,plain,
    ( k2_xboole_0(k1_tops_1(sK0,sK3),k1_tops_1(sK0,sK3)) = k4_subset_1(k1_tops_1(sK0,u1_struct_0(sK0)),k1_tops_1(sK0,sK3),k1_tops_1(sK0,sK3))
    | ~ spl5_44 ),
    inference(resolution,[],[f1676,f702])).

fof(f1954,plain,
    ( spl5_55
    | ~ spl5_42
    | ~ spl5_44 ),
    inference(avatar_split_clause,[],[f1934,f700,f611,f1951])).

fof(f1951,plain,
    ( spl5_55
  <=> k2_xboole_0(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK3)) = k4_subset_1(k1_tops_1(sK0,u1_struct_0(sK0)),k1_tops_1(sK0,sK3),k1_tops_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_55])])).

fof(f1934,plain,
    ( k2_xboole_0(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK3)) = k4_subset_1(k1_tops_1(sK0,u1_struct_0(sK0)),k1_tops_1(sK0,sK3),k1_tops_1(sK0,sK2))
    | ~ spl5_42
    | ~ spl5_44 ),
    inference(forward_demodulation,[],[f1927,f33])).

fof(f1927,plain,
    ( k2_xboole_0(k1_tops_1(sK0,sK3),k1_tops_1(sK0,sK2)) = k4_subset_1(k1_tops_1(sK0,u1_struct_0(sK0)),k1_tops_1(sK0,sK3),k1_tops_1(sK0,sK2))
    | ~ spl5_42
    | ~ spl5_44 ),
    inference(resolution,[],[f1674,f702])).

fof(f1674,plain,
    ( ! [X24] :
        ( ~ r1_tarski(X24,k1_tops_1(sK0,u1_struct_0(sK0)))
        | k2_xboole_0(X24,k1_tops_1(sK0,sK2)) = k4_subset_1(k1_tops_1(sK0,u1_struct_0(sK0)),X24,k1_tops_1(sK0,sK2)) )
    | ~ spl5_42 ),
    inference(resolution,[],[f451,f613])).

fof(f1949,plain,
    ( spl5_54
    | ~ spl5_41
    | ~ spl5_42 ),
    inference(avatar_split_clause,[],[f1939,f611,f595,f1946])).

fof(f1946,plain,
    ( spl5_54
  <=> k1_tops_1(sK0,u1_struct_0(sK0)) = k4_subset_1(k1_tops_1(sK0,u1_struct_0(sK0)),k1_tops_1(sK0,u1_struct_0(sK0)),k1_tops_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_54])])).

fof(f595,plain,
    ( spl5_41
  <=> k1_tops_1(sK0,u1_struct_0(sK0)) = k2_xboole_0(k1_tops_1(sK0,sK2),k1_tops_1(sK0,u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_41])])).

fof(f1939,plain,
    ( k1_tops_1(sK0,u1_struct_0(sK0)) = k4_subset_1(k1_tops_1(sK0,u1_struct_0(sK0)),k1_tops_1(sK0,u1_struct_0(sK0)),k1_tops_1(sK0,sK2))
    | ~ spl5_41
    | ~ spl5_42 ),
    inference(forward_demodulation,[],[f1938,f597])).

fof(f597,plain,
    ( k1_tops_1(sK0,u1_struct_0(sK0)) = k2_xboole_0(k1_tops_1(sK0,sK2),k1_tops_1(sK0,u1_struct_0(sK0)))
    | ~ spl5_41 ),
    inference(avatar_component_clause,[],[f595])).

fof(f1938,plain,
    ( k2_xboole_0(k1_tops_1(sK0,sK2),k1_tops_1(sK0,u1_struct_0(sK0))) = k4_subset_1(k1_tops_1(sK0,u1_struct_0(sK0)),k1_tops_1(sK0,u1_struct_0(sK0)),k1_tops_1(sK0,sK2))
    | ~ spl5_42 ),
    inference(forward_demodulation,[],[f1929,f33])).

fof(f1929,plain,
    ( k2_xboole_0(k1_tops_1(sK0,u1_struct_0(sK0)),k1_tops_1(sK0,sK2)) = k4_subset_1(k1_tops_1(sK0,u1_struct_0(sK0)),k1_tops_1(sK0,u1_struct_0(sK0)),k1_tops_1(sK0,sK2))
    | ~ spl5_42 ),
    inference(resolution,[],[f1674,f387])).

fof(f1944,plain,
    ( spl5_53
    | ~ spl5_42 ),
    inference(avatar_split_clause,[],[f1930,f611,f1941])).

fof(f1941,plain,
    ( spl5_53
  <=> k1_tops_1(sK0,sK2) = k4_subset_1(k1_tops_1(sK0,u1_struct_0(sK0)),k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_53])])).

fof(f1930,plain,
    ( k1_tops_1(sK0,sK2) = k4_subset_1(k1_tops_1(sK0,u1_struct_0(sK0)),k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK2))
    | ~ spl5_42 ),
    inference(forward_demodulation,[],[f1925,f377])).

fof(f1925,plain,
    ( k2_xboole_0(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK2)) = k4_subset_1(k1_tops_1(sK0,u1_struct_0(sK0)),k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK2))
    | ~ spl5_42 ),
    inference(resolution,[],[f1674,f613])).

fof(f1880,plain,
    ( ~ spl5_52
    | spl5_50
    | ~ spl5_51 ),
    inference(avatar_split_clause,[],[f1874,f1868,f1864,f1877])).

fof(f1877,plain,
    ( spl5_52
  <=> r2_hidden(sK4(sK3,sK3,u1_struct_0(sK0)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_52])])).

fof(f1864,plain,
    ( spl5_50
  <=> sK3 = u1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_50])])).

fof(f1868,plain,
    ( spl5_51
  <=> r2_hidden(sK4(sK3,sK3,u1_struct_0(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_51])])).

fof(f1874,plain,
    ( sK3 = u1_struct_0(sK0)
    | ~ r2_hidden(sK4(sK3,sK3,u1_struct_0(sK0)),sK3)
    | ~ spl5_51 ),
    inference(forward_demodulation,[],[f1872,f377])).

fof(f1872,plain,
    ( ~ r2_hidden(sK4(sK3,sK3,u1_struct_0(sK0)),sK3)
    | u1_struct_0(sK0) = k2_xboole_0(sK3,sK3)
    | ~ spl5_51 ),
    inference(resolution,[],[f1870,f39])).

fof(f1870,plain,
    ( r2_hidden(sK4(sK3,sK3,u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl5_51 ),
    inference(avatar_component_clause,[],[f1868])).

fof(f1871,plain,
    ( spl5_50
    | spl5_51
    | ~ spl5_13
    | ~ spl5_15 ),
    inference(avatar_split_clause,[],[f1853,f138,f119,f1868,f1864])).

fof(f138,plain,
    ( spl5_15
  <=> u1_struct_0(sK0) = k2_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f1853,plain,
    ( r2_hidden(sK4(sK3,sK3,u1_struct_0(sK0)),u1_struct_0(sK0))
    | sK3 = u1_struct_0(sK0)
    | ~ spl5_13
    | ~ spl5_15 ),
    inference(superposition,[],[f1501,f140])).

fof(f140,plain,
    ( u1_struct_0(sK0) = k2_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f138])).

fof(f1501,plain,
    ( ! [X12] :
        ( r2_hidden(sK4(sK3,sK3,k2_xboole_0(u1_struct_0(sK0),X12)),k2_xboole_0(u1_struct_0(sK0),X12))
        | sK3 = k2_xboole_0(u1_struct_0(sK0),X12) )
    | ~ spl5_13 ),
    inference(forward_demodulation,[],[f1500,f377])).

fof(f1500,plain,
    ( ! [X12] :
        ( k2_xboole_0(sK3,sK3) = k2_xboole_0(u1_struct_0(sK0),X12)
        | r2_hidden(sK4(sK3,sK3,k2_xboole_0(u1_struct_0(sK0),X12)),k2_xboole_0(u1_struct_0(sK0),X12)) )
    | ~ spl5_13 ),
    inference(subsumption_resolution,[],[f1489,f1499])).

fof(f1499,plain,
    ( ! [X10,X11] :
        ( k2_xboole_0(u1_struct_0(sK0),X11) = k2_xboole_0(sK3,X10)
        | r2_hidden(sK4(sK3,X10,k2_xboole_0(u1_struct_0(sK0),X11)),k2_xboole_0(u1_struct_0(sK0),X11))
        | r2_hidden(sK4(sK3,X10,k2_xboole_0(u1_struct_0(sK0),X11)),X10) )
    | ~ spl5_13 ),
    inference(subsumption_resolution,[],[f1490,f40])).

fof(f1490,plain,
    ( ! [X10,X11] :
        ( ~ r2_hidden(sK4(sK3,X10,k2_xboole_0(u1_struct_0(sK0),X11)),sK3)
        | k2_xboole_0(u1_struct_0(sK0),X11) = k2_xboole_0(sK3,X10)
        | r2_hidden(sK4(sK3,X10,k2_xboole_0(u1_struct_0(sK0),X11)),k2_xboole_0(u1_struct_0(sK0),X11))
        | r2_hidden(sK4(sK3,X10,k2_xboole_0(u1_struct_0(sK0),X11)),X10) )
    | ~ spl5_13 ),
    inference(duplicate_literal_removal,[],[f1467])).

fof(f1467,plain,
    ( ! [X10,X11] :
        ( ~ r2_hidden(sK4(sK3,X10,k2_xboole_0(u1_struct_0(sK0),X11)),sK3)
        | k2_xboole_0(u1_struct_0(sK0),X11) = k2_xboole_0(sK3,X10)
        | r2_hidden(sK4(sK3,X10,k2_xboole_0(u1_struct_0(sK0),X11)),k2_xboole_0(u1_struct_0(sK0),X11))
        | r2_hidden(sK4(sK3,X10,k2_xboole_0(u1_struct_0(sK0),X11)),X10)
        | k2_xboole_0(u1_struct_0(sK0),X11) = k2_xboole_0(sK3,X10) )
    | ~ spl5_13 ),
    inference(resolution,[],[f529,f40])).

fof(f1489,plain,
    ( ! [X12] :
        ( ~ r2_hidden(sK4(sK3,sK3,k2_xboole_0(u1_struct_0(sK0),X12)),sK3)
        | k2_xboole_0(sK3,sK3) = k2_xboole_0(u1_struct_0(sK0),X12)
        | r2_hidden(sK4(sK3,sK3,k2_xboole_0(u1_struct_0(sK0),X12)),k2_xboole_0(u1_struct_0(sK0),X12)) )
    | ~ spl5_13 ),
    inference(duplicate_literal_removal,[],[f1468])).

fof(f1468,plain,
    ( ! [X12] :
        ( ~ r2_hidden(sK4(sK3,sK3,k2_xboole_0(u1_struct_0(sK0),X12)),sK3)
        | k2_xboole_0(sK3,sK3) = k2_xboole_0(u1_struct_0(sK0),X12)
        | r2_hidden(sK4(sK3,sK3,k2_xboole_0(u1_struct_0(sK0),X12)),k2_xboole_0(u1_struct_0(sK0),X12))
        | k2_xboole_0(sK3,sK3) = k2_xboole_0(u1_struct_0(sK0),X12) )
    | ~ spl5_13 ),
    inference(resolution,[],[f529,f273])).

fof(f273,plain,(
    ! [X4,X5] :
      ( r2_hidden(sK4(X4,X4,X5),X5)
      | r2_hidden(sK4(X4,X4,X5),X4)
      | k2_xboole_0(X4,X4) = X5 ) ),
    inference(factoring,[],[f40])).

fof(f1750,plain,
    ( spl5_49
    | ~ spl5_13
    | ~ spl5_15 ),
    inference(avatar_split_clause,[],[f1738,f138,f119,f1747])).

fof(f1747,plain,
    ( spl5_49
  <=> sK3 = k4_subset_1(u1_struct_0(sK0),sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_49])])).

fof(f1738,plain,
    ( sK3 = k4_subset_1(u1_struct_0(sK0),sK3,sK3)
    | ~ spl5_13
    | ~ spl5_15 ),
    inference(superposition,[],[f1734,f140])).

fof(f1734,plain,
    ( ! [X3] : sK3 = k4_subset_1(k2_xboole_0(u1_struct_0(sK0),X3),sK3,sK3)
    | ~ spl5_13 ),
    inference(forward_demodulation,[],[f1719,f377])).

fof(f1719,plain,
    ( ! [X3] : k2_xboole_0(sK3,sK3) = k4_subset_1(k2_xboole_0(u1_struct_0(sK0),X3),sK3,sK3)
    | ~ spl5_13 ),
    inference(resolution,[],[f1666,f1513])).

fof(f1175,plain,
    ( spl5_48
    | ~ spl5_43 ),
    inference(avatar_split_clause,[],[f966,f654,f1172])).

fof(f1172,plain,
    ( spl5_48
  <=> k1_tops_1(sK0,u1_struct_0(sK0)) = k2_xboole_0(k1_tops_1(sK0,u1_struct_0(sK0)),k1_tops_1(sK0,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_48])])).

fof(f966,plain,
    ( k1_tops_1(sK0,u1_struct_0(sK0)) = k2_xboole_0(k1_tops_1(sK0,u1_struct_0(sK0)),k1_tops_1(sK0,sK3))
    | ~ spl5_43 ),
    inference(superposition,[],[f641,f656])).

fof(f994,plain,
    ( spl5_47
    | ~ spl5_41 ),
    inference(avatar_split_clause,[],[f965,f595,f991])).

fof(f991,plain,
    ( spl5_47
  <=> k1_tops_1(sK0,u1_struct_0(sK0)) = k2_xboole_0(k1_tops_1(sK0,u1_struct_0(sK0)),k1_tops_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_47])])).

fof(f965,plain,
    ( k1_tops_1(sK0,u1_struct_0(sK0)) = k2_xboole_0(k1_tops_1(sK0,u1_struct_0(sK0)),k1_tops_1(sK0,sK2))
    | ~ spl5_41 ),
    inference(superposition,[],[f641,f597])).

fof(f770,plain,
    ( spl5_46
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_6
    | ~ spl5_14
    | ~ spl5_45 ),
    inference(avatar_split_clause,[],[f765,f744,f129,f73,f58,f53,f48,f767])).

fof(f767,plain,
    ( spl5_46
  <=> r2_hidden(sK1,k1_tops_1(sK0,u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_46])])).

fof(f129,plain,
    ( spl5_14
  <=> r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f744,plain,
    ( spl5_45
  <=> m1_connsp_2(u1_struct_0(sK0),sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_45])])).

fof(f765,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,u1_struct_0(sK0)))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_6
    | ~ spl5_14
    | ~ spl5_45 ),
    inference(subsumption_resolution,[],[f764,f131])).

fof(f131,plain,
    ( r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f129])).

fof(f764,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,u1_struct_0(sK0)))
    | ~ r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_6
    | ~ spl5_45 ),
    inference(subsumption_resolution,[],[f763,f55])).

fof(f763,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0))
    | spl5_1
    | ~ spl5_3
    | ~ spl5_6
    | ~ spl5_45 ),
    inference(subsumption_resolution,[],[f762,f50])).

fof(f762,plain,
    ( v2_struct_0(sK0)
    | r2_hidden(sK1,k1_tops_1(sK0,u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ spl5_3
    | ~ spl5_6
    | ~ spl5_45 ),
    inference(subsumption_resolution,[],[f761,f75])).

fof(f761,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | r2_hidden(sK1,k1_tops_1(sK0,u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ spl5_3
    | ~ spl5_45 ),
    inference(subsumption_resolution,[],[f760,f60])).

fof(f760,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | r2_hidden(sK1,k1_tops_1(sK0,u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ spl5_45 ),
    inference(resolution,[],[f312,f746])).

fof(f746,plain,
    ( m1_connsp_2(u1_struct_0(sK0),sK0,sK1)
    | ~ spl5_45 ),
    inference(avatar_component_clause,[],[f744])).

fof(f312,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_connsp_2(X2,X0,X1)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0)
      | r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ v2_pre_topc(X0)
      | ~ r1_tarski(X2,u1_struct_0(X0)) ) ),
    inference(resolution,[],[f31,f35])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0)
      | r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_connsp_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f747,plain,
    ( spl5_45
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_6
    | ~ spl5_14
    | ~ spl5_24
    | ~ spl5_43 ),
    inference(avatar_split_clause,[],[f742,f654,f335,f129,f73,f58,f53,f48,f744])).

fof(f335,plain,
    ( spl5_24
  <=> r2_hidden(sK1,k1_tops_1(sK0,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f742,plain,
    ( m1_connsp_2(u1_struct_0(sK0),sK0,sK1)
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_6
    | ~ spl5_14
    | ~ spl5_24
    | ~ spl5_43 ),
    inference(subsumption_resolution,[],[f739,f75])).

fof(f739,plain,
    ( m1_connsp_2(u1_struct_0(sK0),sK0,sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_14
    | ~ spl5_24
    | ~ spl5_43 ),
    inference(resolution,[],[f725,f337])).

fof(f337,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK3))
    | ~ spl5_24 ),
    inference(avatar_component_clause,[],[f335])).

fof(f725,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_tops_1(sK0,sK3))
        | m1_connsp_2(u1_struct_0(sK0),sK0,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_14
    | ~ spl5_43 ),
    inference(subsumption_resolution,[],[f724,f131])).

fof(f724,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | m1_connsp_2(u1_struct_0(sK0),sK0,X0)
        | ~ r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ r2_hidden(X0,k1_tops_1(sK0,sK3)) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_43 ),
    inference(subsumption_resolution,[],[f723,f55])).

fof(f723,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v2_pre_topc(sK0)
        | m1_connsp_2(u1_struct_0(sK0),sK0,X0)
        | ~ r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ r2_hidden(X0,k1_tops_1(sK0,sK3)) )
    | spl5_1
    | ~ spl5_3
    | ~ spl5_43 ),
    inference(subsumption_resolution,[],[f722,f50])).

fof(f722,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | m1_connsp_2(u1_struct_0(sK0),sK0,X0)
        | ~ r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ r2_hidden(X0,k1_tops_1(sK0,sK3)) )
    | ~ spl5_3
    | ~ spl5_43 ),
    inference(subsumption_resolution,[],[f711,f60])).

fof(f711,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | m1_connsp_2(u1_struct_0(sK0),sK0,X0)
        | ~ r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ r2_hidden(X0,k1_tops_1(sK0,sK3)) )
    | ~ spl5_43 ),
    inference(resolution,[],[f292,f688])).

fof(f688,plain,
    ( ! [X1] :
        ( r2_hidden(X1,k1_tops_1(sK0,u1_struct_0(sK0)))
        | ~ r2_hidden(X1,k1_tops_1(sK0,sK3)) )
    | ~ spl5_43 ),
    inference(superposition,[],[f45,f656])).

fof(f703,plain,
    ( spl5_44
    | ~ spl5_43 ),
    inference(avatar_split_clause,[],[f686,f654,f700])).

fof(f686,plain,
    ( r1_tarski(k1_tops_1(sK0,sK3),k1_tops_1(sK0,u1_struct_0(sK0)))
    | ~ spl5_43 ),
    inference(superposition,[],[f32,f656])).

fof(f657,plain,
    ( spl5_43
    | ~ spl5_3
    | ~ spl5_7
    | ~ spl5_11
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f652,f129,f105,f78,f58,f654])).

fof(f105,plain,
    ( spl5_11
  <=> r1_tarski(sK3,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f652,plain,
    ( k1_tops_1(sK0,u1_struct_0(sK0)) = k2_xboole_0(k1_tops_1(sK0,sK3),k1_tops_1(sK0,u1_struct_0(sK0)))
    | ~ spl5_3
    | ~ spl5_7
    | ~ spl5_11
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f650,f107])).

fof(f107,plain,
    ( r1_tarski(sK3,u1_struct_0(sK0))
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f105])).

fof(f650,plain,
    ( ~ r1_tarski(sK3,u1_struct_0(sK0))
    | k1_tops_1(sK0,u1_struct_0(sK0)) = k2_xboole_0(k1_tops_1(sK0,sK3),k1_tops_1(sK0,u1_struct_0(sK0)))
    | ~ spl5_3
    | ~ spl5_7
    | ~ spl5_14 ),
    inference(resolution,[],[f506,f131])).

fof(f614,plain,
    ( spl5_42
    | ~ spl5_41 ),
    inference(avatar_split_clause,[],[f599,f595,f611])).

fof(f599,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,u1_struct_0(sK0)))
    | ~ spl5_41 ),
    inference(superposition,[],[f32,f597])).

fof(f598,plain,
    ( spl5_41
    | ~ spl5_3
    | ~ spl5_8
    | ~ spl5_10
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f593,f129,f100,f83,f58,f595])).

fof(f100,plain,
    ( spl5_10
  <=> r1_tarski(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f593,plain,
    ( k1_tops_1(sK0,u1_struct_0(sK0)) = k2_xboole_0(k1_tops_1(sK0,sK2),k1_tops_1(sK0,u1_struct_0(sK0)))
    | ~ spl5_3
    | ~ spl5_8
    | ~ spl5_10
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f591,f102])).

fof(f102,plain,
    ( r1_tarski(sK2,u1_struct_0(sK0))
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f100])).

fof(f591,plain,
    ( ~ r1_tarski(sK2,u1_struct_0(sK0))
    | k1_tops_1(sK0,u1_struct_0(sK0)) = k2_xboole_0(k1_tops_1(sK0,sK2),k1_tops_1(sK0,u1_struct_0(sK0)))
    | ~ spl5_3
    | ~ spl5_8
    | ~ spl5_14 ),
    inference(resolution,[],[f505,f131])).

fof(f562,plain,
    ( ~ spl5_39
    | spl5_40
    | ~ spl5_3
    | ~ spl5_7
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f552,f129,f78,f58,f559,f555])).

fof(f555,plain,
    ( spl5_39
  <=> r1_tarski(u1_struct_0(sK0),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_39])])).

fof(f559,plain,
    ( spl5_40
  <=> k1_tops_1(sK0,sK3) = k2_xboole_0(k1_tops_1(sK0,sK3),k1_tops_1(sK0,u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_40])])).

fof(f552,plain,
    ( k1_tops_1(sK0,sK3) = k2_xboole_0(k1_tops_1(sK0,sK3),k1_tops_1(sK0,u1_struct_0(sK0)))
    | ~ r1_tarski(u1_struct_0(sK0),sK3)
    | ~ spl5_3
    | ~ spl5_7
    | ~ spl5_14 ),
    inference(forward_demodulation,[],[f550,f33])).

fof(f550,plain,
    ( ~ r1_tarski(u1_struct_0(sK0),sK3)
    | k1_tops_1(sK0,sK3) = k2_xboole_0(k1_tops_1(sK0,u1_struct_0(sK0)),k1_tops_1(sK0,sK3))
    | ~ spl5_3
    | ~ spl5_7
    | ~ spl5_14 ),
    inference(resolution,[],[f499,f131])).

fof(f499,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK0))
        | ~ r1_tarski(X0,sK3)
        | k1_tops_1(sK0,sK3) = k2_xboole_0(k1_tops_1(sK0,X0),k1_tops_1(sK0,sK3)) )
    | ~ spl5_3
    | ~ spl5_7 ),
    inference(resolution,[],[f349,f34])).

fof(f349,plain,
    ( ! [X0] :
        ( r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,sK3))
        | ~ r1_tarski(X0,sK3)
        | ~ r1_tarski(X0,u1_struct_0(sK0)) )
    | ~ spl5_3
    | ~ spl5_7 ),
    inference(resolution,[],[f247,f35])).

fof(f247,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X4,sK3)
        | r1_tarski(k1_tops_1(sK0,X4),k1_tops_1(sK0,sK3)) )
    | ~ spl5_3
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f245,f60])).

fof(f245,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ r1_tarski(X4,sK3)
        | r1_tarski(k1_tops_1(sK0,X4),k1_tops_1(sK0,sK3)) )
    | ~ spl5_7 ),
    inference(resolution,[],[f29,f80])).

fof(f521,plain,
    ( ~ spl5_37
    | spl5_38
    | ~ spl5_3
    | ~ spl5_8
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f511,f129,f83,f58,f518,f514])).

fof(f514,plain,
    ( spl5_37
  <=> r1_tarski(u1_struct_0(sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).

fof(f518,plain,
    ( spl5_38
  <=> k1_tops_1(sK0,sK2) = k2_xboole_0(k1_tops_1(sK0,sK2),k1_tops_1(sK0,u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).

fof(f511,plain,
    ( k1_tops_1(sK0,sK2) = k2_xboole_0(k1_tops_1(sK0,sK2),k1_tops_1(sK0,u1_struct_0(sK0)))
    | ~ r1_tarski(u1_struct_0(sK0),sK2)
    | ~ spl5_3
    | ~ spl5_8
    | ~ spl5_14 ),
    inference(forward_demodulation,[],[f509,f33])).

fof(f509,plain,
    ( ~ r1_tarski(u1_struct_0(sK0),sK2)
    | k1_tops_1(sK0,sK2) = k2_xboole_0(k1_tops_1(sK0,u1_struct_0(sK0)),k1_tops_1(sK0,sK2))
    | ~ spl5_3
    | ~ spl5_8
    | ~ spl5_14 ),
    inference(resolution,[],[f498,f131])).

fof(f498,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK0))
        | ~ r1_tarski(X0,sK2)
        | k1_tops_1(sK0,sK2) = k2_xboole_0(k1_tops_1(sK0,X0),k1_tops_1(sK0,sK2)) )
    | ~ spl5_3
    | ~ spl5_8 ),
    inference(resolution,[],[f331,f34])).

fof(f331,plain,
    ( ! [X0] :
        ( r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,sK2))
        | ~ r1_tarski(X0,sK2)
        | ~ r1_tarski(X0,u1_struct_0(sK0)) )
    | ~ spl5_3
    | ~ spl5_8 ),
    inference(resolution,[],[f246,f35])).

fof(f246,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X3,sK2)
        | r1_tarski(k1_tops_1(sK0,X3),k1_tops_1(sK0,sK2)) )
    | ~ spl5_3
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f244,f60])).

fof(f244,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ r1_tarski(X3,sK2)
        | r1_tarski(k1_tops_1(sK0,X3),k1_tops_1(sK0,sK2)) )
    | ~ spl5_8 ),
    inference(resolution,[],[f29,f85])).

fof(f497,plain,
    ( spl5_36
    | ~ spl5_7
    | ~ spl5_13
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f470,f129,f119,f78,f494])).

fof(f494,plain,
    ( spl5_36
  <=> u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK3,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).

fof(f470,plain,
    ( u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK3,u1_struct_0(sK0))
    | ~ spl5_7
    | ~ spl5_13
    | ~ spl5_14 ),
    inference(forward_demodulation,[],[f467,f121])).

fof(f467,plain,
    ( k2_xboole_0(sK3,u1_struct_0(sK0)) = k4_subset_1(u1_struct_0(sK0),sK3,u1_struct_0(sK0))
    | ~ spl5_7
    | ~ spl5_14 ),
    inference(resolution,[],[f453,f131])).

fof(f464,plain,
    ( spl5_35
    | ~ spl5_8
    | ~ spl5_12
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f458,f129,f114,f83,f461])).

fof(f461,plain,
    ( spl5_35
  <=> u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).

fof(f458,plain,
    ( u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0))
    | ~ spl5_8
    | ~ spl5_12
    | ~ spl5_14 ),
    inference(forward_demodulation,[],[f456,f116])).

fof(f456,plain,
    ( k2_xboole_0(sK2,u1_struct_0(sK0)) = k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0))
    | ~ spl5_8
    | ~ spl5_14 ),
    inference(resolution,[],[f452,f131])).

fof(f424,plain,
    ( spl5_34
    | ~ spl5_8
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f407,f239,f83,f421])).

fof(f421,plain,
    ( spl5_34
  <=> u1_struct_0(sK0) = k2_xboole_0(u1_struct_0(sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).

fof(f239,plain,
    ( spl5_18
  <=> u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f407,plain,
    ( u1_struct_0(sK0) = k2_xboole_0(u1_struct_0(sK0),sK2)
    | ~ spl5_8
    | ~ spl5_18 ),
    inference(forward_demodulation,[],[f400,f241])).

fof(f241,plain,
    ( u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2)
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f239])).

fof(f400,plain,
    ( k2_xboole_0(u1_struct_0(sK0),sK2) = k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2)
    | ~ spl5_8 ),
    inference(resolution,[],[f387,f214])).

fof(f419,plain,
    ( spl5_33
    | ~ spl5_7
    | ~ spl5_22 ),
    inference(avatar_split_clause,[],[f406,f302,f78,f416])).

fof(f416,plain,
    ( spl5_33
  <=> u1_struct_0(sK0) = k2_xboole_0(u1_struct_0(sK0),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).

fof(f302,plain,
    ( spl5_22
  <=> u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f406,plain,
    ( u1_struct_0(sK0) = k2_xboole_0(u1_struct_0(sK0),sK3)
    | ~ spl5_7
    | ~ spl5_22 ),
    inference(forward_demodulation,[],[f399,f304])).

fof(f304,plain,
    ( u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK3)
    | ~ spl5_22 ),
    inference(avatar_component_clause,[],[f302])).

fof(f399,plain,
    ( k2_xboole_0(u1_struct_0(sK0),sK3) = k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK3)
    | ~ spl5_7 ),
    inference(resolution,[],[f387,f248])).

fof(f248,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK0))
        | k4_subset_1(u1_struct_0(sK0),X0,sK3) = k2_xboole_0(X0,sK3) )
    | ~ spl5_7 ),
    inference(resolution,[],[f209,f35])).

fof(f209,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | k4_subset_1(u1_struct_0(sK0),X4,sK3) = k2_xboole_0(X4,sK3) )
    | ~ spl5_7 ),
    inference(resolution,[],[f37,f80])).

fof(f405,plain,(
    spl5_26 ),
    inference(avatar_contradiction_clause,[],[f397])).

fof(f397,plain,
    ( $false
    | spl5_26 ),
    inference(unit_resulting_resolution,[],[f347,f387])).

fof(f347,plain,
    ( ~ r1_tarski(sK2,sK2)
    | spl5_26 ),
    inference(avatar_component_clause,[],[f345])).

fof(f345,plain,
    ( spl5_26
  <=> r1_tarski(sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f404,plain,(
    spl5_26 ),
    inference(avatar_contradiction_clause,[],[f401])).

fof(f401,plain,
    ( $false
    | spl5_26 ),
    inference(resolution,[],[f387,f347])).

fof(f403,plain,(
    spl5_32 ),
    inference(avatar_contradiction_clause,[],[f402])).

fof(f402,plain,
    ( $false
    | spl5_32 ),
    inference(resolution,[],[f387,f385])).

fof(f385,plain,
    ( ~ r1_tarski(sK3,sK3)
    | spl5_32 ),
    inference(avatar_component_clause,[],[f383])).

fof(f383,plain,
    ( spl5_32
  <=> r1_tarski(sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).

fof(f386,plain,
    ( spl5_31
    | ~ spl5_32
    | ~ spl5_3
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f351,f78,f58,f383,f379])).

fof(f379,plain,
    ( spl5_31
  <=> r1_tarski(k1_tops_1(sK0,sK3),k1_tops_1(sK0,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).

fof(f351,plain,
    ( ~ r1_tarski(sK3,sK3)
    | r1_tarski(k1_tops_1(sK0,sK3),k1_tops_1(sK0,sK3))
    | ~ spl5_3
    | ~ spl5_7 ),
    inference(resolution,[],[f247,f80])).

fof(f369,plain,
    ( spl5_29
    | ~ spl5_30
    | ~ spl5_3
    | ~ spl5_7
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f350,f83,f78,f58,f366,f362])).

fof(f362,plain,
    ( spl5_29
  <=> r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).

fof(f366,plain,
    ( spl5_30
  <=> r1_tarski(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f350,plain,
    ( ~ r1_tarski(sK2,sK3)
    | r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK3))
    | ~ spl5_3
    | ~ spl5_7
    | ~ spl5_8 ),
    inference(resolution,[],[f247,f85])).

fof(f360,plain,
    ( spl5_27
    | ~ spl5_28
    | ~ spl5_3
    | ~ spl5_7
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f333,f83,f78,f58,f357,f353])).

fof(f353,plain,
    ( spl5_27
  <=> r1_tarski(k1_tops_1(sK0,sK3),k1_tops_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f357,plain,
    ( spl5_28
  <=> r1_tarski(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).

fof(f333,plain,
    ( ~ r1_tarski(sK3,sK2)
    | r1_tarski(k1_tops_1(sK0,sK3),k1_tops_1(sK0,sK2))
    | ~ spl5_3
    | ~ spl5_7
    | ~ spl5_8 ),
    inference(resolution,[],[f246,f80])).

fof(f348,plain,
    ( spl5_25
    | ~ spl5_26
    | ~ spl5_3
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f332,f83,f58,f345,f341])).

fof(f341,plain,
    ( spl5_25
  <=> r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f332,plain,
    ( ~ r1_tarski(sK2,sK2)
    | r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK2))
    | ~ spl5_3
    | ~ spl5_8 ),
    inference(resolution,[],[f246,f85])).

fof(f338,plain,
    ( spl5_24
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f330,f78,f73,f68,f58,f53,f48,f335])).

fof(f68,plain,
    ( spl5_5
  <=> m1_connsp_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f330,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK3))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f329,f75])).

fof(f329,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK3))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5
    | ~ spl5_7 ),
    inference(resolution,[],[f320,f70])).

fof(f70,plain,
    ( m1_connsp_2(sK3,sK0,sK1)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f68])).

fof(f320,plain,
    ( ! [X4] :
        ( ~ m1_connsp_2(sK3,sK0,X4)
        | r2_hidden(X4,k1_tops_1(sK0,sK3))
        | ~ m1_subset_1(X4,u1_struct_0(sK0)) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f319,f50])).

fof(f319,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(X4,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | r2_hidden(X4,k1_tops_1(sK0,sK3))
        | ~ m1_connsp_2(sK3,sK0,X4) )
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f318,f60])).

fof(f318,plain,
    ( ! [X4] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | r2_hidden(X4,k1_tops_1(sK0,sK3))
        | ~ m1_connsp_2(sK3,sK0,X4) )
    | ~ spl5_2
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f314,f55])).

fof(f314,plain,
    ( ! [X4] :
        ( ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | r2_hidden(X4,k1_tops_1(sK0,sK3))
        | ~ m1_connsp_2(sK3,sK0,X4) )
    | ~ spl5_7 ),
    inference(resolution,[],[f31,f80])).

fof(f327,plain,
    ( spl5_23
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f322,f83,f73,f63,f58,f53,f48,f324])).

fof(f63,plain,
    ( spl5_4
  <=> m1_connsp_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f322,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f321,f75])).

fof(f321,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_8 ),
    inference(resolution,[],[f317,f65])).

fof(f65,plain,
    ( m1_connsp_2(sK2,sK0,sK1)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f63])).

fof(f317,plain,
    ( ! [X3] :
        ( ~ m1_connsp_2(sK2,sK0,X3)
        | r2_hidden(X3,k1_tops_1(sK0,sK2))
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f316,f50])).

fof(f316,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | r2_hidden(X3,k1_tops_1(sK0,sK2))
        | ~ m1_connsp_2(sK2,sK0,X3) )
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f315,f60])).

fof(f315,plain,
    ( ! [X3] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | r2_hidden(X3,k1_tops_1(sK0,sK2))
        | ~ m1_connsp_2(sK2,sK0,X3) )
    | ~ spl5_2
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f313,f55])).

fof(f313,plain,
    ( ! [X3] :
        ( ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | r2_hidden(X3,k1_tops_1(sK0,sK2))
        | ~ m1_connsp_2(sK2,sK0,X3) )
    | ~ spl5_8 ),
    inference(resolution,[],[f31,f85])).

fof(f305,plain,
    ( spl5_22
    | ~ spl5_7
    | ~ spl5_13
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f291,f129,f119,f78,f302])).

fof(f291,plain,
    ( u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK3)
    | ~ spl5_7
    | ~ spl5_13
    | ~ spl5_14 ),
    inference(forward_demodulation,[],[f290,f121])).

fof(f290,plain,
    ( k2_xboole_0(sK3,u1_struct_0(sK0)) = k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK3)
    | ~ spl5_7
    | ~ spl5_14 ),
    inference(forward_demodulation,[],[f289,f33])).

fof(f289,plain,
    ( k2_xboole_0(u1_struct_0(sK0),sK3) = k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK3)
    | ~ spl5_7
    | ~ spl5_14 ),
    inference(resolution,[],[f248,f131])).

fof(f286,plain,
    ( ~ spl5_21
    | spl5_9
    | ~ spl5_19 ),
    inference(avatar_split_clause,[],[f261,f252,f88,f283])).

fof(f88,plain,
    ( spl5_9
  <=> m1_connsp_2(k4_subset_1(u1_struct_0(sK0),sK2,sK3),sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f252,plain,
    ( spl5_19
  <=> k4_subset_1(u1_struct_0(sK0),sK2,sK3) = k2_xboole_0(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f261,plain,
    ( ~ m1_connsp_2(k2_xboole_0(sK2,sK3),sK0,sK1)
    | spl5_9
    | ~ spl5_19 ),
    inference(superposition,[],[f90,f254])).

fof(f254,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK2,sK3) = k2_xboole_0(sK2,sK3)
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f252])).

fof(f90,plain,
    ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(sK0),sK2,sK3),sK0,sK1)
    | spl5_9 ),
    inference(avatar_component_clause,[],[f88])).

fof(f260,plain,
    ( spl5_20
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f250,f78,f257])).

fof(f257,plain,
    ( spl5_20
  <=> k4_subset_1(u1_struct_0(sK0),sK3,sK3) = k2_xboole_0(sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f250,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK3,sK3) = k2_xboole_0(sK3,sK3)
    | ~ spl5_7 ),
    inference(resolution,[],[f209,f80])).

fof(f255,plain,
    ( spl5_19
    | ~ spl5_7
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f249,f83,f78,f252])).

fof(f249,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK2,sK3) = k2_xboole_0(sK2,sK3)
    | ~ spl5_7
    | ~ spl5_8 ),
    inference(resolution,[],[f209,f85])).

fof(f242,plain,
    ( spl5_18
    | ~ spl5_8
    | ~ spl5_12
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f237,f129,f114,f83,f239])).

fof(f237,plain,
    ( u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2)
    | ~ spl5_8
    | ~ spl5_12
    | ~ spl5_14 ),
    inference(forward_demodulation,[],[f236,f116])).

fof(f236,plain,
    ( k2_xboole_0(sK2,u1_struct_0(sK0)) = k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2)
    | ~ spl5_8
    | ~ spl5_14 ),
    inference(forward_demodulation,[],[f234,f33])).

fof(f234,plain,
    ( k2_xboole_0(u1_struct_0(sK0),sK2) = k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2)
    | ~ spl5_8
    | ~ spl5_14 ),
    inference(resolution,[],[f214,f131])).

fof(f227,plain,
    ( spl5_17
    | ~ spl5_7
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f217,f83,f78,f224])).

fof(f224,plain,
    ( spl5_17
  <=> k4_subset_1(u1_struct_0(sK0),sK3,sK2) = k2_xboole_0(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f217,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK3,sK2) = k2_xboole_0(sK2,sK3)
    | ~ spl5_7
    | ~ spl5_8 ),
    inference(forward_demodulation,[],[f216,f33])).

fof(f216,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK3,sK2) = k2_xboole_0(sK3,sK2)
    | ~ spl5_7
    | ~ spl5_8 ),
    inference(resolution,[],[f208,f80])).

fof(f222,plain,
    ( spl5_16
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f215,f83,f219])).

fof(f219,plain,
    ( spl5_16
  <=> k4_subset_1(u1_struct_0(sK0),sK2,sK2) = k2_xboole_0(sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f215,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK2,sK2) = k2_xboole_0(sK2,sK2)
    | ~ spl5_8 ),
    inference(resolution,[],[f208,f85])).

fof(f141,plain,
    ( spl5_15
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f133,f129,f138])).

fof(f133,plain,
    ( u1_struct_0(sK0) = k2_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ spl5_14 ),
    inference(resolution,[],[f131,f34])).

fof(f132,plain,
    ( spl5_14
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f123,f114,f129])).

fof(f123,plain,
    ( r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ spl5_12 ),
    inference(superposition,[],[f92,f116])).

fof(f122,plain,
    ( spl5_13
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f112,f105,f119])).

fof(f112,plain,
    ( u1_struct_0(sK0) = k2_xboole_0(sK3,u1_struct_0(sK0))
    | ~ spl5_11 ),
    inference(resolution,[],[f107,f34])).

fof(f117,plain,
    ( spl5_12
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f111,f100,f114])).

fof(f111,plain,
    ( u1_struct_0(sK0) = k2_xboole_0(sK2,u1_struct_0(sK0))
    | ~ spl5_10 ),
    inference(resolution,[],[f34,f102])).

fof(f108,plain,
    ( spl5_11
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f98,f78,f105])).

fof(f98,plain,
    ( r1_tarski(sK3,u1_struct_0(sK0))
    | ~ spl5_7 ),
    inference(resolution,[],[f36,f80])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f103,plain,
    ( spl5_10
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f97,f83,f100])).

fof(f97,plain,
    ( r1_tarski(sK2,u1_struct_0(sK0))
    | ~ spl5_8 ),
    inference(resolution,[],[f36,f85])).

fof(f91,plain,(
    ~ spl5_9 ),
    inference(avatar_split_clause,[],[f23,f88])).

fof(f23,plain,(
    ~ m1_connsp_2(k4_subset_1(u1_struct_0(sK0),sK2,sK3),sK0,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1)
                  & m1_connsp_2(X3,X0,X1)
                  & m1_connsp_2(X2,X0,X1)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1)
                  & m1_connsp_2(X3,X0,X1)
                  & m1_connsp_2(X2,X0,X1)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ( ( m1_connsp_2(X3,X0,X1)
                        & m1_connsp_2(X2,X0,X1) )
                     => m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( m1_connsp_2(X3,X0,X1)
                      & m1_connsp_2(X2,X0,X1) )
                   => m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_connsp_2)).

fof(f86,plain,(
    spl5_8 ),
    inference(avatar_split_clause,[],[f24,f83])).

fof(f24,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f12])).

fof(f81,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f20,f78])).

fof(f20,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f12])).

fof(f76,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f25,f73])).

fof(f25,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f71,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f22,f68])).

fof(f22,plain,(
    m1_connsp_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f66,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f21,f63])).

fof(f21,plain,(
    m1_connsp_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f61,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f28,f58])).

fof(f28,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f56,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f27,f53])).

fof(f27,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f51,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f26,f48])).

fof(f26,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:20:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.42  % (4878)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.49  % (4874)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.49  % (4872)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.50  % (4880)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.50  % (4884)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.50  % (4875)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.51  % (4889)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.51  % (4876)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.51  % (4888)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.51  % (4891)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.51  % (4887)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.51  % (4877)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.51  % (4890)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.51  % (4891)Refutation not found, incomplete strategy% (4891)------------------------------
% 0.22/0.51  % (4891)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (4891)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (4891)Memory used [KB]: 10618
% 0.22/0.51  % (4891)Time elapsed: 0.096 s
% 0.22/0.51  % (4891)------------------------------
% 0.22/0.51  % (4891)------------------------------
% 0.22/0.51  % (4885)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.51  % (4872)Refutation not found, incomplete strategy% (4872)------------------------------
% 0.22/0.51  % (4872)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (4872)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (4872)Memory used [KB]: 10618
% 0.22/0.51  % (4872)Time elapsed: 0.104 s
% 0.22/0.51  % (4872)------------------------------
% 0.22/0.51  % (4872)------------------------------
% 0.22/0.52  % (4883)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (4871)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.52  % (4881)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.52  % (4879)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.53  % (4882)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.53  % (4873)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 1.37/0.54  % (4886)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 2.11/0.66  % (4879)Refutation found. Thanks to Tanya!
% 2.11/0.66  % SZS status Theorem for theBenchmark
% 2.11/0.66  % SZS output start Proof for theBenchmark
% 2.11/0.66  fof(f3330,plain,(
% 2.11/0.66    $false),
% 2.11/0.66    inference(avatar_sat_refutation,[],[f51,f56,f61,f66,f71,f76,f81,f86,f91,f103,f108,f117,f122,f132,f141,f222,f227,f242,f255,f260,f286,f305,f327,f338,f348,f360,f369,f386,f403,f404,f405,f419,f424,f464,f497,f521,f562,f598,f614,f657,f703,f747,f770,f994,f1175,f1750,f1871,f1880,f1944,f1949,f1954,f1970,f1975,f1980,f2315,f2365,f2538,f2540,f2544,f2546,f2548,f2744,f2800,f2892,f2897,f2992,f2997,f3090,f3134,f3197,f3221,f3226,f3326,f3329])).
% 2.11/0.66  fof(f3329,plain,(
% 2.11/0.66    spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_6 | spl5_21 | ~spl5_23 | ~spl5_61 | ~spl5_66),
% 2.11/0.66    inference(avatar_contradiction_clause,[],[f3328])).
% 2.11/0.66  fof(f3328,plain,(
% 2.11/0.66    $false | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_6 | spl5_21 | ~spl5_23 | ~spl5_61 | ~spl5_66)),
% 2.11/0.66    inference(subsumption_resolution,[],[f3327,f326])).
% 2.11/0.66  fof(f326,plain,(
% 2.11/0.66    r2_hidden(sK1,k1_tops_1(sK0,sK2)) | ~spl5_23),
% 2.11/0.66    inference(avatar_component_clause,[],[f324])).
% 2.11/0.66  fof(f324,plain,(
% 2.11/0.66    spl5_23 <=> r2_hidden(sK1,k1_tops_1(sK0,sK2))),
% 2.11/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).
% 2.11/0.66  fof(f3327,plain,(
% 2.11/0.66    ~r2_hidden(sK1,k1_tops_1(sK0,sK2)) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_6 | spl5_21 | ~spl5_61 | ~spl5_66)),
% 2.11/0.66    inference(subsumption_resolution,[],[f3323,f75])).
% 2.11/0.66  fof(f75,plain,(
% 2.11/0.66    m1_subset_1(sK1,u1_struct_0(sK0)) | ~spl5_6),
% 2.11/0.66    inference(avatar_component_clause,[],[f73])).
% 2.11/0.66  fof(f73,plain,(
% 2.11/0.66    spl5_6 <=> m1_subset_1(sK1,u1_struct_0(sK0))),
% 2.11/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 2.11/0.66  fof(f3323,plain,(
% 2.11/0.66    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~r2_hidden(sK1,k1_tops_1(sK0,sK2)) | (spl5_1 | ~spl5_2 | ~spl5_3 | spl5_21 | ~spl5_61 | ~spl5_66)),
% 2.11/0.66    inference(resolution,[],[f3153,f285])).
% 2.11/0.66  fof(f285,plain,(
% 2.11/0.66    ~m1_connsp_2(k2_xboole_0(sK2,sK3),sK0,sK1) | spl5_21),
% 2.11/0.66    inference(avatar_component_clause,[],[f283])).
% 2.11/0.66  fof(f283,plain,(
% 2.11/0.66    spl5_21 <=> m1_connsp_2(k2_xboole_0(sK2,sK3),sK0,sK1)),
% 2.11/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 2.11/0.66  fof(f3153,plain,(
% 2.11/0.66    ( ! [X0] : (m1_connsp_2(k2_xboole_0(sK2,sK3),sK0,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,k1_tops_1(sK0,sK2))) ) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_61 | ~spl5_66)),
% 2.11/0.66    inference(subsumption_resolution,[],[f3152,f2364])).
% 2.11/0.66  fof(f2364,plain,(
% 2.11/0.66    r1_tarski(k2_xboole_0(sK2,sK3),u1_struct_0(sK0)) | ~spl5_61),
% 2.11/0.66    inference(avatar_component_clause,[],[f2362])).
% 2.11/0.66  fof(f2362,plain,(
% 2.11/0.66    spl5_61 <=> r1_tarski(k2_xboole_0(sK2,sK3),u1_struct_0(sK0))),
% 2.11/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_61])])).
% 2.11/0.66  fof(f3152,plain,(
% 2.11/0.66    ( ! [X0] : (~r2_hidden(X0,k1_tops_1(sK0,sK2)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | m1_connsp_2(k2_xboole_0(sK2,sK3),sK0,X0) | ~r1_tarski(k2_xboole_0(sK2,sK3),u1_struct_0(sK0))) ) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_66)),
% 2.11/0.66    inference(subsumption_resolution,[],[f3151,f55])).
% 2.11/0.66  fof(f55,plain,(
% 2.11/0.66    v2_pre_topc(sK0) | ~spl5_2),
% 2.11/0.66    inference(avatar_component_clause,[],[f53])).
% 2.11/0.66  fof(f53,plain,(
% 2.11/0.66    spl5_2 <=> v2_pre_topc(sK0)),
% 2.11/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 2.11/0.66  fof(f3151,plain,(
% 2.11/0.66    ( ! [X0] : (~r2_hidden(X0,k1_tops_1(sK0,sK2)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v2_pre_topc(sK0) | m1_connsp_2(k2_xboole_0(sK2,sK3),sK0,X0) | ~r1_tarski(k2_xboole_0(sK2,sK3),u1_struct_0(sK0))) ) | (spl5_1 | ~spl5_3 | ~spl5_66)),
% 2.11/0.66    inference(subsumption_resolution,[],[f3150,f50])).
% 2.11/0.66  fof(f50,plain,(
% 2.11/0.66    ~v2_struct_0(sK0) | spl5_1),
% 2.11/0.66    inference(avatar_component_clause,[],[f48])).
% 2.11/0.66  fof(f48,plain,(
% 2.11/0.66    spl5_1 <=> v2_struct_0(sK0)),
% 2.11/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 2.11/0.66  fof(f3150,plain,(
% 2.11/0.66    ( ! [X0] : (~r2_hidden(X0,k1_tops_1(sK0,sK2)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | m1_connsp_2(k2_xboole_0(sK2,sK3),sK0,X0) | ~r1_tarski(k2_xboole_0(sK2,sK3),u1_struct_0(sK0))) ) | (~spl5_3 | ~spl5_66)),
% 2.11/0.66    inference(subsumption_resolution,[],[f3143,f60])).
% 2.11/0.66  fof(f60,plain,(
% 2.11/0.66    l1_pre_topc(sK0) | ~spl5_3),
% 2.11/0.66    inference(avatar_component_clause,[],[f58])).
% 2.11/0.66  fof(f58,plain,(
% 2.11/0.66    spl5_3 <=> l1_pre_topc(sK0)),
% 2.11/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 2.11/0.66  fof(f3143,plain,(
% 2.11/0.66    ( ! [X0] : (~r2_hidden(X0,k1_tops_1(sK0,sK2)) | ~l1_pre_topc(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | m1_connsp_2(k2_xboole_0(sK2,sK3),sK0,X0) | ~r1_tarski(k2_xboole_0(sK2,sK3),u1_struct_0(sK0))) ) | ~spl5_66),
% 2.11/0.66    inference(resolution,[],[f3093,f292])).
% 2.11/0.66  fof(f292,plain,(
% 2.11/0.66    ( ! [X2,X0,X1] : (~r2_hidden(X1,k1_tops_1(X0,X2)) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0) | ~v2_pre_topc(X0) | m1_connsp_2(X2,X0,X1) | ~r1_tarski(X2,u1_struct_0(X0))) )),
% 2.11/0.66    inference(resolution,[],[f30,f35])).
% 2.11/0.66  fof(f35,plain,(
% 2.11/0.66    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.11/0.66    inference(cnf_transformation,[],[f6])).
% 2.11/0.66  fof(f6,axiom,(
% 2.11/0.66    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.11/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 2.11/0.66  fof(f30,plain,(
% 2.11/0.66    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0) | ~r2_hidden(X1,k1_tops_1(X0,X2)) | m1_connsp_2(X2,X0,X1)) )),
% 2.11/0.66    inference(cnf_transformation,[],[f16])).
% 2.11/0.66  fof(f16,plain,(
% 2.11/0.66    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.11/0.66    inference(flattening,[],[f15])).
% 2.11/0.66  fof(f15,plain,(
% 2.11/0.66    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.11/0.66    inference(ennf_transformation,[],[f8])).
% 2.11/0.66  fof(f8,axiom,(
% 2.11/0.66    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))))))),
% 2.11/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_connsp_2)).
% 2.11/0.66  fof(f3093,plain,(
% 2.11/0.66    ( ! [X1] : (r2_hidden(X1,k1_tops_1(sK0,k2_xboole_0(sK2,sK3))) | ~r2_hidden(X1,k1_tops_1(sK0,sK2))) ) | ~spl5_66),
% 2.11/0.66    inference(superposition,[],[f45,f2996])).
% 2.11/0.66  fof(f2996,plain,(
% 2.11/0.66    k1_tops_1(sK0,k2_xboole_0(sK2,sK3)) = k2_xboole_0(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k2_xboole_0(sK2,sK3))) | ~spl5_66),
% 2.11/0.66    inference(avatar_component_clause,[],[f2994])).
% 2.11/0.66  fof(f2994,plain,(
% 2.11/0.66    spl5_66 <=> k1_tops_1(sK0,k2_xboole_0(sK2,sK3)) = k2_xboole_0(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k2_xboole_0(sK2,sK3)))),
% 2.11/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_66])])).
% 2.11/0.66  fof(f45,plain,(
% 2.11/0.66    ( ! [X0,X3,X1] : (r2_hidden(X3,k2_xboole_0(X0,X1)) | ~r2_hidden(X3,X0)) )),
% 2.11/0.66    inference(equality_resolution,[],[f42])).
% 2.11/0.66  fof(f42,plain,(
% 2.11/0.66    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X2) | k2_xboole_0(X0,X1) != X2) )),
% 2.11/0.66    inference(cnf_transformation,[],[f2])).
% 2.11/0.66  fof(f2,axiom,(
% 2.11/0.66    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 2.11/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).
% 2.11/0.66  fof(f3326,plain,(
% 2.11/0.66    spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_6 | spl5_21 | ~spl5_23 | ~spl5_61 | ~spl5_66),
% 2.11/0.66    inference(avatar_contradiction_clause,[],[f3322])).
% 2.11/0.66  fof(f3322,plain,(
% 2.11/0.66    $false | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_6 | spl5_21 | ~spl5_23 | ~spl5_61 | ~spl5_66)),
% 2.11/0.66    inference(unit_resulting_resolution,[],[f75,f326,f285,f3153])).
% 2.11/0.66  fof(f3226,plain,(
% 2.11/0.66    spl5_71 | ~spl5_67),
% 2.11/0.66    inference(avatar_split_clause,[],[f3183,f3087,f3223])).
% 2.11/0.66  fof(f3223,plain,(
% 2.11/0.66    spl5_71 <=> k1_tops_1(sK0,k2_xboole_0(sK2,sK3)) = k2_xboole_0(k1_tops_1(sK0,k2_xboole_0(sK2,sK3)),k1_tops_1(sK0,sK3))),
% 2.11/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_71])])).
% 2.11/0.66  fof(f3087,plain,(
% 2.11/0.66    spl5_67 <=> k1_tops_1(sK0,k2_xboole_0(sK2,sK3)) = k2_xboole_0(k1_tops_1(sK0,sK3),k1_tops_1(sK0,k2_xboole_0(sK2,sK3)))),
% 2.11/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_67])])).
% 2.11/0.66  fof(f3183,plain,(
% 2.11/0.66    k1_tops_1(sK0,k2_xboole_0(sK2,sK3)) = k2_xboole_0(k1_tops_1(sK0,k2_xboole_0(sK2,sK3)),k1_tops_1(sK0,sK3)) | ~spl5_67),
% 2.11/0.66    inference(superposition,[],[f641,f3089])).
% 2.11/0.66  fof(f3089,plain,(
% 2.11/0.66    k1_tops_1(sK0,k2_xboole_0(sK2,sK3)) = k2_xboole_0(k1_tops_1(sK0,sK3),k1_tops_1(sK0,k2_xboole_0(sK2,sK3))) | ~spl5_67),
% 2.11/0.66    inference(avatar_component_clause,[],[f3087])).
% 2.11/0.66  fof(f641,plain,(
% 2.11/0.66    ( ! [X8,X9] : (k2_xboole_0(X8,X9) = k2_xboole_0(k2_xboole_0(X8,X9),X8)) )),
% 2.11/0.66    inference(subsumption_resolution,[],[f637,f281])).
% 2.11/0.66  fof(f281,plain,(
% 2.11/0.66    ( ! [X2,X3] : (r2_hidden(sK4(X2,X3,X2),X3) | k2_xboole_0(X2,X3) = X2) )),
% 2.11/0.66    inference(subsumption_resolution,[],[f272,f38])).
% 2.11/0.66  fof(f38,plain,(
% 2.11/0.66    ( ! [X2,X0,X1] : (~r2_hidden(sK4(X0,X1,X2),X2) | ~r2_hidden(sK4(X0,X1,X2),X0) | k2_xboole_0(X0,X1) = X2) )),
% 2.11/0.66    inference(cnf_transformation,[],[f2])).
% 2.11/0.66  fof(f272,plain,(
% 2.11/0.66    ( ! [X2,X3] : (r2_hidden(sK4(X2,X3,X2),X2) | r2_hidden(sK4(X2,X3,X2),X3) | k2_xboole_0(X2,X3) = X2) )),
% 2.11/0.66    inference(factoring,[],[f40])).
% 2.11/0.66  fof(f40,plain,(
% 2.11/0.66    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),X2) | r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X0) | k2_xboole_0(X0,X1) = X2) )),
% 2.11/0.66    inference(cnf_transformation,[],[f2])).
% 2.11/0.66  fof(f637,plain,(
% 2.11/0.66    ( ! [X8,X9] : (k2_xboole_0(X8,X9) = k2_xboole_0(k2_xboole_0(X8,X9),X8) | ~r2_hidden(sK4(k2_xboole_0(X8,X9),X8,k2_xboole_0(X8,X9)),X8)) )),
% 2.11/0.66    inference(duplicate_literal_removal,[],[f618])).
% 2.11/0.66  fof(f618,plain,(
% 2.11/0.66    ( ! [X8,X9] : (k2_xboole_0(X8,X9) = k2_xboole_0(k2_xboole_0(X8,X9),X8) | ~r2_hidden(sK4(k2_xboole_0(X8,X9),X8,k2_xboole_0(X8,X9)),X8) | k2_xboole_0(X8,X9) = k2_xboole_0(k2_xboole_0(X8,X9),X8)) )),
% 2.11/0.66    inference(resolution,[],[f228,f281])).
% 2.11/0.66  fof(f228,plain,(
% 2.11/0.66    ( ! [X2,X0,X3,X1] : (~r2_hidden(sK4(X0,X1,k2_xboole_0(X2,X3)),X2) | k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) | ~r2_hidden(sK4(X0,X1,k2_xboole_0(X2,X3)),X1)) )),
% 2.11/0.66    inference(resolution,[],[f39,f45])).
% 2.11/0.66  fof(f39,plain,(
% 2.11/0.66    ( ! [X2,X0,X1] : (~r2_hidden(sK4(X0,X1,X2),X2) | ~r2_hidden(sK4(X0,X1,X2),X1) | k2_xboole_0(X0,X1) = X2) )),
% 2.11/0.66    inference(cnf_transformation,[],[f2])).
% 2.11/0.66  fof(f3221,plain,(
% 2.11/0.66    spl5_70 | ~spl5_66),
% 2.11/0.66    inference(avatar_split_clause,[],[f3120,f2994,f3218])).
% 2.11/0.66  fof(f3218,plain,(
% 2.11/0.66    spl5_70 <=> k1_tops_1(sK0,k2_xboole_0(sK2,sK3)) = k2_xboole_0(k1_tops_1(sK0,k2_xboole_0(sK2,sK3)),k1_tops_1(sK0,sK2))),
% 2.11/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_70])])).
% 2.11/0.66  fof(f3120,plain,(
% 2.11/0.66    k1_tops_1(sK0,k2_xboole_0(sK2,sK3)) = k2_xboole_0(k1_tops_1(sK0,k2_xboole_0(sK2,sK3)),k1_tops_1(sK0,sK2)) | ~spl5_66),
% 2.11/0.66    inference(superposition,[],[f641,f2996])).
% 2.11/0.66  fof(f3197,plain,(
% 2.11/0.66    spl5_69 | ~spl5_67),
% 2.11/0.66    inference(avatar_split_clause,[],[f3154,f3087,f3194])).
% 2.11/0.66  fof(f3194,plain,(
% 2.11/0.66    spl5_69 <=> r1_tarski(k1_tops_1(sK0,sK3),k1_tops_1(sK0,k2_xboole_0(sK2,sK3)))),
% 2.11/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_69])])).
% 2.11/0.66  fof(f3154,plain,(
% 2.11/0.66    r1_tarski(k1_tops_1(sK0,sK3),k1_tops_1(sK0,k2_xboole_0(sK2,sK3))) | ~spl5_67),
% 2.11/0.66    inference(superposition,[],[f32,f3089])).
% 2.11/0.66  fof(f32,plain,(
% 2.11/0.66    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.11/0.66    inference(cnf_transformation,[],[f4])).
% 2.11/0.66  fof(f4,axiom,(
% 2.11/0.66    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 2.11/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 2.11/0.66  fof(f3134,plain,(
% 2.11/0.66    spl5_68 | ~spl5_66),
% 2.11/0.66    inference(avatar_split_clause,[],[f3091,f2994,f3131])).
% 2.11/0.66  fof(f3131,plain,(
% 2.11/0.66    spl5_68 <=> r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k2_xboole_0(sK2,sK3)))),
% 2.11/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_68])])).
% 2.11/0.66  fof(f3091,plain,(
% 2.11/0.66    r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k2_xboole_0(sK2,sK3))) | ~spl5_66),
% 2.11/0.66    inference(superposition,[],[f32,f2996])).
% 2.11/0.66  fof(f3090,plain,(
% 2.11/0.66    spl5_67 | ~spl5_3 | ~spl5_7 | ~spl5_61),
% 2.11/0.66    inference(avatar_split_clause,[],[f2569,f2362,f78,f58,f3087])).
% 2.11/0.66  fof(f78,plain,(
% 2.11/0.66    spl5_7 <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.11/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 2.11/0.66  fof(f2569,plain,(
% 2.11/0.66    k1_tops_1(sK0,k2_xboole_0(sK2,sK3)) = k2_xboole_0(k1_tops_1(sK0,sK3),k1_tops_1(sK0,k2_xboole_0(sK2,sK3))) | (~spl5_3 | ~spl5_7 | ~spl5_61)),
% 2.11/0.66    inference(subsumption_resolution,[],[f2556,f92])).
% 2.11/0.66  fof(f92,plain,(
% 2.11/0.66    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X0))) )),
% 2.11/0.66    inference(superposition,[],[f32,f33])).
% 2.11/0.66  fof(f33,plain,(
% 2.11/0.66    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 2.11/0.66    inference(cnf_transformation,[],[f1])).
% 2.11/0.66  fof(f1,axiom,(
% 2.11/0.66    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 2.11/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 2.11/0.66  fof(f2556,plain,(
% 2.11/0.66    ~r1_tarski(sK3,k2_xboole_0(sK2,sK3)) | k1_tops_1(sK0,k2_xboole_0(sK2,sK3)) = k2_xboole_0(k1_tops_1(sK0,sK3),k1_tops_1(sK0,k2_xboole_0(sK2,sK3))) | (~spl5_3 | ~spl5_7 | ~spl5_61)),
% 2.11/0.66    inference(resolution,[],[f2364,f506])).
% 2.11/0.66  fof(f506,plain,(
% 2.11/0.66    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK0)) | ~r1_tarski(sK3,X0) | k1_tops_1(sK0,X0) = k2_xboole_0(k1_tops_1(sK0,sK3),k1_tops_1(sK0,X0))) ) | (~spl5_3 | ~spl5_7)),
% 2.11/0.66    inference(resolution,[],[f504,f34])).
% 2.11/0.66  fof(f34,plain,(
% 2.11/0.66    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 2.11/0.66    inference(cnf_transformation,[],[f17])).
% 2.11/0.66  fof(f17,plain,(
% 2.11/0.66    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 2.11/0.66    inference(ennf_transformation,[],[f3])).
% 2.11/0.66  fof(f3,axiom,(
% 2.11/0.66    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 2.11/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 2.11/0.66  fof(f504,plain,(
% 2.11/0.66    ( ! [X4] : (r1_tarski(k1_tops_1(sK0,sK3),k1_tops_1(sK0,X4)) | ~r1_tarski(sK3,X4) | ~r1_tarski(X4,u1_struct_0(sK0))) ) | (~spl5_3 | ~spl5_7)),
% 2.11/0.66    inference(subsumption_resolution,[],[f502,f60])).
% 2.11/0.66  fof(f502,plain,(
% 2.11/0.66    ( ! [X4] : (~l1_pre_topc(sK0) | ~r1_tarski(sK3,X4) | r1_tarski(k1_tops_1(sK0,sK3),k1_tops_1(sK0,X4)) | ~r1_tarski(X4,u1_struct_0(sK0))) ) | ~spl5_7),
% 2.11/0.66    inference(resolution,[],[f243,f80])).
% 2.11/0.66  fof(f80,plain,(
% 2.11/0.66    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_7),
% 2.11/0.66    inference(avatar_component_clause,[],[f78])).
% 2.11/0.66  fof(f243,plain,(
% 2.11/0.66    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | ~r1_tarski(X0,X2) | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2)) | ~r1_tarski(X2,u1_struct_0(X1))) )),
% 2.11/0.66    inference(resolution,[],[f29,f35])).
% 2.11/0.66  fof(f29,plain,(
% 2.11/0.66    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~r1_tarski(X1,X2) | r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))) )),
% 2.11/0.66    inference(cnf_transformation,[],[f14])).
% 2.11/0.66  fof(f14,plain,(
% 2.11/0.66    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.11/0.66    inference(flattening,[],[f13])).
% 2.11/0.66  fof(f13,plain,(
% 2.11/0.66    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.11/0.66    inference(ennf_transformation,[],[f7])).
% 2.11/0.66  fof(f7,axiom,(
% 2.11/0.66    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 2.11/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).
% 2.11/0.66  fof(f2997,plain,(
% 2.11/0.66    spl5_66 | ~spl5_3 | ~spl5_8 | ~spl5_61),
% 2.11/0.66    inference(avatar_split_clause,[],[f2568,f2362,f83,f58,f2994])).
% 2.11/0.66  fof(f83,plain,(
% 2.11/0.66    spl5_8 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.11/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 2.11/0.66  fof(f2568,plain,(
% 2.11/0.66    k1_tops_1(sK0,k2_xboole_0(sK2,sK3)) = k2_xboole_0(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k2_xboole_0(sK2,sK3))) | (~spl5_3 | ~spl5_8 | ~spl5_61)),
% 2.11/0.66    inference(subsumption_resolution,[],[f2555,f32])).
% 2.11/0.66  fof(f2555,plain,(
% 2.11/0.66    ~r1_tarski(sK2,k2_xboole_0(sK2,sK3)) | k1_tops_1(sK0,k2_xboole_0(sK2,sK3)) = k2_xboole_0(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k2_xboole_0(sK2,sK3))) | (~spl5_3 | ~spl5_8 | ~spl5_61)),
% 2.11/0.66    inference(resolution,[],[f2364,f505])).
% 2.11/0.66  fof(f505,plain,(
% 2.11/0.66    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK0)) | ~r1_tarski(sK2,X0) | k1_tops_1(sK0,X0) = k2_xboole_0(k1_tops_1(sK0,sK2),k1_tops_1(sK0,X0))) ) | (~spl5_3 | ~spl5_8)),
% 2.11/0.66    inference(resolution,[],[f503,f34])).
% 2.11/0.66  fof(f503,plain,(
% 2.11/0.66    ( ! [X3] : (r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,X3)) | ~r1_tarski(sK2,X3) | ~r1_tarski(X3,u1_struct_0(sK0))) ) | (~spl5_3 | ~spl5_8)),
% 2.11/0.66    inference(subsumption_resolution,[],[f501,f60])).
% 2.11/0.66  fof(f501,plain,(
% 2.11/0.66    ( ! [X3] : (~l1_pre_topc(sK0) | ~r1_tarski(sK2,X3) | r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,X3)) | ~r1_tarski(X3,u1_struct_0(sK0))) ) | ~spl5_8),
% 2.11/0.66    inference(resolution,[],[f243,f85])).
% 2.11/0.66  fof(f85,plain,(
% 2.11/0.66    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_8),
% 2.11/0.66    inference(avatar_component_clause,[],[f83])).
% 2.11/0.66  fof(f2992,plain,(
% 2.11/0.66    spl5_65 | ~spl5_13 | ~spl5_59),
% 2.11/0.66    inference(avatar_split_clause,[],[f2360,f2308,f119,f2989])).
% 2.11/0.66  fof(f2989,plain,(
% 2.11/0.66    spl5_65 <=> k2_xboole_0(sK2,sK3) = k4_subset_1(u1_struct_0(sK0),k2_xboole_0(sK2,sK3),sK3)),
% 2.11/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_65])])).
% 2.11/0.66  fof(f119,plain,(
% 2.11/0.66    spl5_13 <=> u1_struct_0(sK0) = k2_xboole_0(sK3,u1_struct_0(sK0))),
% 2.11/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 2.11/0.66  fof(f2308,plain,(
% 2.11/0.66    spl5_59 <=> u1_struct_0(sK0) = k2_xboole_0(u1_struct_0(sK0),k2_xboole_0(sK2,sK3))),
% 2.11/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_59])])).
% 2.11/0.66  fof(f2360,plain,(
% 2.11/0.66    k2_xboole_0(sK2,sK3) = k4_subset_1(u1_struct_0(sK0),k2_xboole_0(sK2,sK3),sK3) | (~spl5_13 | ~spl5_59)),
% 2.11/0.66    inference(forward_demodulation,[],[f2359,f110])).
% 2.11/0.66  fof(f110,plain,(
% 2.11/0.66    ( ! [X2,X3] : (k2_xboole_0(X3,X2) = k2_xboole_0(X2,k2_xboole_0(X3,X2))) )),
% 2.11/0.66    inference(resolution,[],[f34,f92])).
% 2.11/0.66  fof(f2359,plain,(
% 2.11/0.66    k4_subset_1(u1_struct_0(sK0),k2_xboole_0(sK2,sK3),sK3) = k2_xboole_0(sK3,k2_xboole_0(sK2,sK3)) | (~spl5_13 | ~spl5_59)),
% 2.11/0.66    inference(forward_demodulation,[],[f2323,f33])).
% 2.11/0.66  fof(f2323,plain,(
% 2.11/0.66    k2_xboole_0(k2_xboole_0(sK2,sK3),sK3) = k4_subset_1(u1_struct_0(sK0),k2_xboole_0(sK2,sK3),sK3) | (~spl5_13 | ~spl5_59)),
% 2.11/0.66    inference(superposition,[],[f1717,f2310])).
% 2.11/0.66  fof(f2310,plain,(
% 2.11/0.66    u1_struct_0(sK0) = k2_xboole_0(u1_struct_0(sK0),k2_xboole_0(sK2,sK3)) | ~spl5_59),
% 2.11/0.66    inference(avatar_component_clause,[],[f2308])).
% 2.11/0.66  fof(f1717,plain,(
% 2.11/0.66    ( ! [X1] : (k2_xboole_0(X1,sK3) = k4_subset_1(k2_xboole_0(u1_struct_0(sK0),X1),X1,sK3)) ) | ~spl5_13),
% 2.11/0.66    inference(resolution,[],[f1666,f92])).
% 2.11/0.66  fof(f1666,plain,(
% 2.11/0.66    ( ! [X12,X11] : (~r1_tarski(X12,k2_xboole_0(u1_struct_0(sK0),X11)) | k4_subset_1(k2_xboole_0(u1_struct_0(sK0),X11),X12,sK3) = k2_xboole_0(X12,sK3)) ) | ~spl5_13),
% 2.11/0.66    inference(resolution,[],[f451,f1513])).
% 2.11/0.66  fof(f1513,plain,(
% 2.11/0.66    ( ! [X0] : (r1_tarski(sK3,k2_xboole_0(u1_struct_0(sK0),X0))) ) | ~spl5_13),
% 2.11/0.66    inference(superposition,[],[f32,f1498])).
% 2.11/0.66  fof(f1498,plain,(
% 2.11/0.66    ( ! [X7] : (k2_xboole_0(u1_struct_0(sK0),X7) = k2_xboole_0(sK3,k2_xboole_0(u1_struct_0(sK0),X7))) ) | ~spl5_13),
% 2.11/0.66    inference(subsumption_resolution,[],[f1492,f280])).
% 2.11/0.66  fof(f280,plain,(
% 2.11/0.66    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1,X1),X0) | k2_xboole_0(X0,X1) = X1) )),
% 2.11/0.66    inference(subsumption_resolution,[],[f271,f39])).
% 2.11/0.66  fof(f271,plain,(
% 2.11/0.66    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1,X1),X1) | r2_hidden(sK4(X0,X1,X1),X0) | k2_xboole_0(X0,X1) = X1) )),
% 2.11/0.66    inference(factoring,[],[f40])).
% 2.11/0.66  fof(f1492,plain,(
% 2.11/0.66    ( ! [X7] : (~r2_hidden(sK4(sK3,k2_xboole_0(u1_struct_0(sK0),X7),k2_xboole_0(u1_struct_0(sK0),X7)),sK3) | k2_xboole_0(u1_struct_0(sK0),X7) = k2_xboole_0(sK3,k2_xboole_0(u1_struct_0(sK0),X7))) ) | ~spl5_13),
% 2.11/0.66    inference(duplicate_literal_removal,[],[f1465])).
% 2.11/0.66  fof(f1465,plain,(
% 2.11/0.66    ( ! [X7] : (~r2_hidden(sK4(sK3,k2_xboole_0(u1_struct_0(sK0),X7),k2_xboole_0(u1_struct_0(sK0),X7)),sK3) | k2_xboole_0(u1_struct_0(sK0),X7) = k2_xboole_0(sK3,k2_xboole_0(u1_struct_0(sK0),X7)) | k2_xboole_0(u1_struct_0(sK0),X7) = k2_xboole_0(sK3,k2_xboole_0(u1_struct_0(sK0),X7))) ) | ~spl5_13),
% 2.11/0.66    inference(resolution,[],[f529,f280])).
% 2.11/0.66  fof(f529,plain,(
% 2.11/0.66    ( ! [X24,X23,X22] : (~r2_hidden(sK4(X22,X23,k2_xboole_0(u1_struct_0(sK0),X24)),sK3) | ~r2_hidden(sK4(X22,X23,k2_xboole_0(u1_struct_0(sK0),X24)),X22) | k2_xboole_0(X22,X23) = k2_xboole_0(u1_struct_0(sK0),X24)) ) | ~spl5_13),
% 2.11/0.66    inference(resolution,[],[f210,f145])).
% 2.11/0.66  fof(f145,plain,(
% 2.11/0.66    ( ! [X7] : (r2_hidden(X7,u1_struct_0(sK0)) | ~r2_hidden(X7,sK3)) ) | ~spl5_13),
% 2.11/0.66    inference(superposition,[],[f45,f121])).
% 2.11/0.66  fof(f121,plain,(
% 2.11/0.66    u1_struct_0(sK0) = k2_xboole_0(sK3,u1_struct_0(sK0)) | ~spl5_13),
% 2.11/0.66    inference(avatar_component_clause,[],[f119])).
% 2.11/0.66  fof(f210,plain,(
% 2.11/0.66    ( ! [X2,X0,X3,X1] : (~r2_hidden(sK4(X0,X1,k2_xboole_0(X2,X3)),X2) | k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) | ~r2_hidden(sK4(X0,X1,k2_xboole_0(X2,X3)),X0)) )),
% 2.11/0.66    inference(resolution,[],[f38,f45])).
% 2.11/0.66  fof(f451,plain,(
% 2.11/0.66    ( ! [X2,X0,X1] : (~r1_tarski(X2,X0) | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~r1_tarski(X1,X0)) )),
% 2.11/0.66    inference(resolution,[],[f207,f35])).
% 2.11/0.66  fof(f207,plain,(
% 2.11/0.66    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) | ~r1_tarski(X2,X1)) )),
% 2.11/0.66    inference(resolution,[],[f37,f35])).
% 2.11/0.66  fof(f37,plain,(
% 2.11/0.66    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)) )),
% 2.11/0.66    inference(cnf_transformation,[],[f19])).
% 2.11/0.66  fof(f19,plain,(
% 2.11/0.66    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.11/0.66    inference(flattening,[],[f18])).
% 2.11/0.66  fof(f18,plain,(
% 2.11/0.66    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 2.11/0.66    inference(ennf_transformation,[],[f5])).
% 2.11/0.66  fof(f5,axiom,(
% 2.11/0.66    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 2.11/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 2.11/0.66  fof(f2897,plain,(
% 2.11/0.66    spl5_64 | ~spl5_7 | ~spl5_61),
% 2.11/0.66    inference(avatar_split_clause,[],[f2565,f2362,f78,f2894])).
% 2.11/0.66  fof(f2894,plain,(
% 2.11/0.66    spl5_64 <=> k2_xboole_0(sK2,sK3) = k4_subset_1(u1_struct_0(sK0),sK3,k2_xboole_0(sK2,sK3))),
% 2.11/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_64])])).
% 2.11/0.66  fof(f2565,plain,(
% 2.11/0.66    k2_xboole_0(sK2,sK3) = k4_subset_1(u1_struct_0(sK0),sK3,k2_xboole_0(sK2,sK3)) | (~spl5_7 | ~spl5_61)),
% 2.11/0.66    inference(forward_demodulation,[],[f2552,f110])).
% 2.11/0.66  fof(f2552,plain,(
% 2.11/0.66    k2_xboole_0(sK3,k2_xboole_0(sK2,sK3)) = k4_subset_1(u1_struct_0(sK0),sK3,k2_xboole_0(sK2,sK3)) | (~spl5_7 | ~spl5_61)),
% 2.11/0.66    inference(resolution,[],[f2364,f453])).
% 2.11/0.66  fof(f453,plain,(
% 2.11/0.66    ( ! [X4] : (~r1_tarski(X4,u1_struct_0(sK0)) | k2_xboole_0(sK3,X4) = k4_subset_1(u1_struct_0(sK0),sK3,X4)) ) | ~spl5_7),
% 2.11/0.66    inference(resolution,[],[f207,f80])).
% 2.11/0.66  fof(f2892,plain,(
% 2.11/0.66    spl5_63 | ~spl5_8 | ~spl5_61),
% 2.11/0.66    inference(avatar_split_clause,[],[f2564,f2362,f83,f2889])).
% 2.11/0.66  fof(f2889,plain,(
% 2.11/0.66    spl5_63 <=> k2_xboole_0(sK2,sK3) = k4_subset_1(u1_struct_0(sK0),sK2,k2_xboole_0(sK2,sK3))),
% 2.11/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_63])])).
% 2.11/0.66  fof(f2564,plain,(
% 2.11/0.66    k2_xboole_0(sK2,sK3) = k4_subset_1(u1_struct_0(sK0),sK2,k2_xboole_0(sK2,sK3)) | (~spl5_8 | ~spl5_61)),
% 2.11/0.66    inference(forward_demodulation,[],[f2551,f109])).
% 2.11/0.66  fof(f109,plain,(
% 2.11/0.66    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 2.11/0.66    inference(resolution,[],[f34,f32])).
% 2.11/0.66  fof(f2551,plain,(
% 2.11/0.66    k2_xboole_0(sK2,k2_xboole_0(sK2,sK3)) = k4_subset_1(u1_struct_0(sK0),sK2,k2_xboole_0(sK2,sK3)) | (~spl5_8 | ~spl5_61)),
% 2.11/0.66    inference(resolution,[],[f2364,f452])).
% 2.11/0.66  fof(f452,plain,(
% 2.11/0.66    ( ! [X3] : (~r1_tarski(X3,u1_struct_0(sK0)) | k2_xboole_0(sK2,X3) = k4_subset_1(u1_struct_0(sK0),sK2,X3)) ) | ~spl5_8),
% 2.11/0.66    inference(resolution,[],[f207,f85])).
% 2.11/0.66  fof(f2800,plain,(
% 2.11/0.66    spl5_62 | ~spl5_8 | ~spl5_61),
% 2.11/0.66    inference(avatar_split_clause,[],[f2562,f2362,f83,f2797])).
% 2.11/0.66  fof(f2797,plain,(
% 2.11/0.66    spl5_62 <=> k2_xboole_0(sK2,sK3) = k4_subset_1(u1_struct_0(sK0),k2_xboole_0(sK2,sK3),sK2)),
% 2.11/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_62])])).
% 2.11/0.66  fof(f2562,plain,(
% 2.11/0.66    k2_xboole_0(sK2,sK3) = k4_subset_1(u1_struct_0(sK0),k2_xboole_0(sK2,sK3),sK2) | (~spl5_8 | ~spl5_61)),
% 2.11/0.66    inference(forward_demodulation,[],[f2561,f109])).
% 2.11/0.66  fof(f2561,plain,(
% 2.11/0.66    k4_subset_1(u1_struct_0(sK0),k2_xboole_0(sK2,sK3),sK2) = k2_xboole_0(sK2,k2_xboole_0(sK2,sK3)) | (~spl5_8 | ~spl5_61)),
% 2.11/0.66    inference(forward_demodulation,[],[f2549,f33])).
% 2.11/0.66  fof(f2549,plain,(
% 2.11/0.66    k4_subset_1(u1_struct_0(sK0),k2_xboole_0(sK2,sK3),sK2) = k2_xboole_0(k2_xboole_0(sK2,sK3),sK2) | (~spl5_8 | ~spl5_61)),
% 2.11/0.66    inference(resolution,[],[f2364,f214])).
% 2.11/0.66  fof(f214,plain,(
% 2.11/0.66    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK0)) | k4_subset_1(u1_struct_0(sK0),X0,sK2) = k2_xboole_0(X0,sK2)) ) | ~spl5_8),
% 2.11/0.66    inference(resolution,[],[f208,f35])).
% 2.11/0.66  fof(f208,plain,(
% 2.11/0.66    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),X3,sK2) = k2_xboole_0(X3,sK2)) ) | ~spl5_8),
% 2.11/0.66    inference(resolution,[],[f37,f85])).
% 2.11/0.66  fof(f2744,plain,(
% 2.11/0.66    spl5_60 | ~spl5_59),
% 2.11/0.66    inference(avatar_split_clause,[],[f2336,f2308,f2312])).
% 2.11/0.66  fof(f2312,plain,(
% 2.11/0.66    spl5_60 <=> u1_struct_0(sK0) = k2_xboole_0(k2_xboole_0(sK2,sK3),u1_struct_0(sK0))),
% 2.11/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_60])])).
% 2.11/0.66  fof(f2336,plain,(
% 2.11/0.66    u1_struct_0(sK0) = k2_xboole_0(k2_xboole_0(sK2,sK3),u1_struct_0(sK0)) | ~spl5_59),
% 2.11/0.66    inference(superposition,[],[f110,f2310])).
% 2.11/0.66  fof(f2548,plain,(
% 2.11/0.66    spl5_59 | ~spl5_60),
% 2.11/0.66    inference(avatar_contradiction_clause,[],[f2547])).
% 2.11/0.66  fof(f2547,plain,(
% 2.11/0.66    $false | (spl5_59 | ~spl5_60)),
% 2.11/0.66    inference(subsumption_resolution,[],[f2535,f2309])).
% 2.11/0.66  fof(f2309,plain,(
% 2.11/0.66    u1_struct_0(sK0) != k2_xboole_0(u1_struct_0(sK0),k2_xboole_0(sK2,sK3)) | spl5_59),
% 2.11/0.66    inference(avatar_component_clause,[],[f2308])).
% 2.11/0.66  fof(f2535,plain,(
% 2.11/0.66    u1_struct_0(sK0) = k2_xboole_0(u1_struct_0(sK0),k2_xboole_0(sK2,sK3)) | ~spl5_60),
% 2.11/0.66    inference(superposition,[],[f641,f2314])).
% 2.11/0.66  fof(f2314,plain,(
% 2.11/0.66    u1_struct_0(sK0) = k2_xboole_0(k2_xboole_0(sK2,sK3),u1_struct_0(sK0)) | ~spl5_60),
% 2.11/0.66    inference(avatar_component_clause,[],[f2312])).
% 2.11/0.66  fof(f2546,plain,(
% 2.11/0.66    spl5_59 | ~spl5_60),
% 2.11/0.66    inference(avatar_contradiction_clause,[],[f2545])).
% 2.11/0.66  fof(f2545,plain,(
% 2.11/0.66    $false | (spl5_59 | ~spl5_60)),
% 2.11/0.66    inference(subsumption_resolution,[],[f2506,f2309])).
% 2.11/0.66  fof(f2506,plain,(
% 2.11/0.66    u1_struct_0(sK0) = k2_xboole_0(u1_struct_0(sK0),k2_xboole_0(sK2,sK3)) | ~spl5_60),
% 2.11/0.66    inference(superposition,[],[f33,f2314])).
% 2.11/0.66  fof(f2544,plain,(
% 2.11/0.66    spl5_59 | ~spl5_60),
% 2.11/0.66    inference(avatar_contradiction_clause,[],[f2543])).
% 2.11/0.66  fof(f2543,plain,(
% 2.11/0.66    $false | (spl5_59 | ~spl5_60)),
% 2.11/0.66    inference(subsumption_resolution,[],[f2505,f2309])).
% 2.11/0.66  fof(f2505,plain,(
% 2.11/0.66    u1_struct_0(sK0) = k2_xboole_0(u1_struct_0(sK0),k2_xboole_0(sK2,sK3)) | ~spl5_60),
% 2.11/0.66    inference(superposition,[],[f33,f2314])).
% 2.11/0.66  fof(f2540,plain,(
% 2.11/0.66    spl5_59 | ~spl5_60),
% 2.11/0.66    inference(avatar_contradiction_clause,[],[f2539])).
% 2.11/0.66  fof(f2539,plain,(
% 2.11/0.66    $false | (spl5_59 | ~spl5_60)),
% 2.11/0.66    inference(subsumption_resolution,[],[f2490,f2309])).
% 2.11/0.66  fof(f2490,plain,(
% 2.11/0.66    u1_struct_0(sK0) = k2_xboole_0(u1_struct_0(sK0),k2_xboole_0(sK2,sK3)) | ~spl5_60),
% 2.11/0.66    inference(superposition,[],[f2314,f33])).
% 2.11/0.66  fof(f2538,plain,(
% 2.11/0.66    spl5_59 | ~spl5_60),
% 2.11/0.66    inference(avatar_contradiction_clause,[],[f2537])).
% 2.11/0.66  fof(f2537,plain,(
% 2.11/0.66    $false | (spl5_59 | ~spl5_60)),
% 2.11/0.66    inference(subsumption_resolution,[],[f2489,f2309])).
% 2.11/0.66  fof(f2489,plain,(
% 2.11/0.66    u1_struct_0(sK0) = k2_xboole_0(u1_struct_0(sK0),k2_xboole_0(sK2,sK3)) | ~spl5_60),
% 2.11/0.66    inference(superposition,[],[f2314,f33])).
% 2.11/0.66  fof(f2365,plain,(
% 2.11/0.66    spl5_61 | ~spl5_59),
% 2.11/0.66    inference(avatar_split_clause,[],[f2334,f2308,f2362])).
% 2.11/0.66  fof(f2334,plain,(
% 2.11/0.66    r1_tarski(k2_xboole_0(sK2,sK3),u1_struct_0(sK0)) | ~spl5_59),
% 2.11/0.66    inference(superposition,[],[f92,f2310])).
% 2.11/0.66  fof(f2315,plain,(
% 2.11/0.66    spl5_59 | spl5_60 | ~spl5_12 | ~spl5_13),
% 2.11/0.66    inference(avatar_split_clause,[],[f2288,f119,f114,f2312,f2308])).
% 2.11/0.66  fof(f114,plain,(
% 2.11/0.66    spl5_12 <=> u1_struct_0(sK0) = k2_xboole_0(sK2,u1_struct_0(sK0))),
% 2.11/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 2.11/0.66  fof(f2288,plain,(
% 2.11/0.66    u1_struct_0(sK0) = k2_xboole_0(k2_xboole_0(sK2,sK3),u1_struct_0(sK0)) | u1_struct_0(sK0) = k2_xboole_0(u1_struct_0(sK0),k2_xboole_0(sK2,sK3)) | (~spl5_12 | ~spl5_13)),
% 2.11/0.66    inference(forward_demodulation,[],[f2287,f33])).
% 2.11/0.66  fof(f2287,plain,(
% 2.11/0.66    u1_struct_0(sK0) = k2_xboole_0(u1_struct_0(sK0),k2_xboole_0(sK2,sK3)) | u1_struct_0(sK0) = k2_xboole_0(k2_xboole_0(sK3,sK2),u1_struct_0(sK0)) | (~spl5_12 | ~spl5_13)),
% 2.11/0.66    inference(forward_demodulation,[],[f2286,f33])).
% 2.11/0.66  fof(f2286,plain,(
% 2.11/0.66    u1_struct_0(sK0) = k2_xboole_0(u1_struct_0(sK0),k2_xboole_0(sK3,sK2)) | u1_struct_0(sK0) = k2_xboole_0(k2_xboole_0(sK3,sK2),u1_struct_0(sK0)) | (~spl5_12 | ~spl5_13)),
% 2.11/0.66    inference(subsumption_resolution,[],[f2261,f280])).
% 2.11/0.66  fof(f2261,plain,(
% 2.11/0.66    u1_struct_0(sK0) = k2_xboole_0(u1_struct_0(sK0),k2_xboole_0(sK3,sK2)) | u1_struct_0(sK0) = k2_xboole_0(k2_xboole_0(sK3,sK2),u1_struct_0(sK0)) | ~r2_hidden(sK4(k2_xboole_0(sK3,sK2),u1_struct_0(sK0),u1_struct_0(sK0)),k2_xboole_0(sK3,sK2)) | (~spl5_12 | ~spl5_13)),
% 2.11/0.66    inference(resolution,[],[f2229,f212])).
% 2.11/0.66  fof(f212,plain,(
% 2.11/0.66    ( ! [X8,X9] : (~r2_hidden(sK4(X8,X9,u1_struct_0(sK0)),sK3) | u1_struct_0(sK0) = k2_xboole_0(X8,X9) | ~r2_hidden(sK4(X8,X9,u1_struct_0(sK0)),X8)) ) | ~spl5_13),
% 2.11/0.66    inference(resolution,[],[f38,f145])).
% 2.11/0.66  fof(f2229,plain,(
% 2.11/0.66    ( ! [X16] : (r2_hidden(sK4(k2_xboole_0(X16,sK2),u1_struct_0(sK0),u1_struct_0(sK0)),X16) | u1_struct_0(sK0) = k2_xboole_0(u1_struct_0(sK0),k2_xboole_0(X16,sK2))) ) | ~spl5_12),
% 2.11/0.66    inference(forward_demodulation,[],[f2228,f33])).
% 2.11/0.66  fof(f2228,plain,(
% 2.11/0.66    ( ! [X16] : (r2_hidden(sK4(k2_xboole_0(X16,sK2),u1_struct_0(sK0),u1_struct_0(sK0)),X16) | u1_struct_0(sK0) = k2_xboole_0(k2_xboole_0(X16,sK2),u1_struct_0(sK0))) ) | ~spl5_12),
% 2.11/0.66    inference(subsumption_resolution,[],[f2213,f1447])).
% 2.11/0.66  fof(f1447,plain,(
% 2.11/0.66    ( ! [X24,X25] : (r2_hidden(sK4(k2_xboole_0(X24,sK2),X25,u1_struct_0(sK0)),u1_struct_0(sK0)) | r2_hidden(sK4(k2_xboole_0(X24,sK2),X25,u1_struct_0(sK0)),X25) | r2_hidden(sK4(k2_xboole_0(X24,sK2),X25,u1_struct_0(sK0)),X24) | u1_struct_0(sK0) = k2_xboole_0(k2_xboole_0(X24,sK2),X25)) ) | ~spl5_12),
% 2.11/0.66    inference(subsumption_resolution,[],[f1425,f40])).
% 2.11/0.66  fof(f1425,plain,(
% 2.11/0.66    ( ! [X24,X25] : (r2_hidden(sK4(k2_xboole_0(X24,sK2),X25,u1_struct_0(sK0)),u1_struct_0(sK0)) | r2_hidden(sK4(k2_xboole_0(X24,sK2),X25,u1_struct_0(sK0)),X25) | r2_hidden(sK4(k2_xboole_0(X24,sK2),X25,u1_struct_0(sK0)),X24) | u1_struct_0(sK0) = k2_xboole_0(k2_xboole_0(X24,sK2),X25) | ~r2_hidden(sK4(k2_xboole_0(X24,sK2),X25,u1_struct_0(sK0)),k2_xboole_0(X24,sK2))) ) | ~spl5_12),
% 2.11/0.66    inference(duplicate_literal_removal,[],[f1302])).
% 2.11/0.66  fof(f1302,plain,(
% 2.11/0.66    ( ! [X24,X25] : (r2_hidden(sK4(k2_xboole_0(X24,sK2),X25,u1_struct_0(sK0)),u1_struct_0(sK0)) | r2_hidden(sK4(k2_xboole_0(X24,sK2),X25,u1_struct_0(sK0)),X25) | r2_hidden(sK4(k2_xboole_0(X24,sK2),X25,u1_struct_0(sK0)),X24) | u1_struct_0(sK0) = k2_xboole_0(k2_xboole_0(X24,sK2),X25) | u1_struct_0(sK0) = k2_xboole_0(k2_xboole_0(X24,sK2),X25) | ~r2_hidden(sK4(k2_xboole_0(X24,sK2),X25,u1_struct_0(sK0)),k2_xboole_0(X24,sK2))) ) | ~spl5_12),
% 2.11/0.66    inference(resolution,[],[f270,f213])).
% 2.11/0.66  fof(f213,plain,(
% 2.11/0.66    ( ! [X10,X11] : (~r2_hidden(sK4(X10,X11,u1_struct_0(sK0)),sK2) | u1_struct_0(sK0) = k2_xboole_0(X10,X11) | ~r2_hidden(sK4(X10,X11,u1_struct_0(sK0)),X10)) ) | ~spl5_12),
% 2.11/0.66    inference(resolution,[],[f38,f144])).
% 2.11/0.66  fof(f144,plain,(
% 2.11/0.66    ( ! [X6] : (r2_hidden(X6,u1_struct_0(sK0)) | ~r2_hidden(X6,sK2)) ) | ~spl5_12),
% 2.11/0.66    inference(superposition,[],[f45,f116])).
% 2.11/0.66  fof(f116,plain,(
% 2.11/0.66    u1_struct_0(sK0) = k2_xboole_0(sK2,u1_struct_0(sK0)) | ~spl5_12),
% 2.11/0.66    inference(avatar_component_clause,[],[f114])).
% 2.11/0.66  fof(f270,plain,(
% 2.11/0.66    ( ! [X6,X4,X7,X5] : (r2_hidden(sK4(k2_xboole_0(X4,X5),X6,X7),X7) | r2_hidden(sK4(k2_xboole_0(X4,X5),X6,X7),X6) | r2_hidden(sK4(k2_xboole_0(X4,X5),X6,X7),X5) | r2_hidden(sK4(k2_xboole_0(X4,X5),X6,X7),X4) | k2_xboole_0(k2_xboole_0(X4,X5),X6) = X7) )),
% 2.11/0.66    inference(resolution,[],[f40,f46])).
% 2.11/0.66  fof(f46,plain,(
% 2.11/0.66    ( ! [X0,X3,X1] : (~r2_hidden(X3,k2_xboole_0(X0,X1)) | r2_hidden(X3,X1) | r2_hidden(X3,X0)) )),
% 2.11/0.66    inference(equality_resolution,[],[f41])).
% 2.11/0.66  fof(f41,plain,(
% 2.11/0.66    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k2_xboole_0(X0,X1) != X2) )),
% 2.11/0.66    inference(cnf_transformation,[],[f2])).
% 2.11/0.66  fof(f2213,plain,(
% 2.11/0.66    ( ! [X16] : (r2_hidden(sK4(k2_xboole_0(X16,sK2),u1_struct_0(sK0),u1_struct_0(sK0)),X16) | u1_struct_0(sK0) = k2_xboole_0(k2_xboole_0(X16,sK2),u1_struct_0(sK0)) | ~r2_hidden(sK4(k2_xboole_0(X16,sK2),u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))) ) | ~spl5_12),
% 2.11/0.66    inference(duplicate_literal_removal,[],[f2121])).
% 2.11/0.66  fof(f2121,plain,(
% 2.11/0.66    ( ! [X16] : (r2_hidden(sK4(k2_xboole_0(X16,sK2),u1_struct_0(sK0),u1_struct_0(sK0)),X16) | u1_struct_0(sK0) = k2_xboole_0(k2_xboole_0(X16,sK2),u1_struct_0(sK0)) | u1_struct_0(sK0) = k2_xboole_0(k2_xboole_0(X16,sK2),u1_struct_0(sK0)) | ~r2_hidden(sK4(k2_xboole_0(X16,sK2),u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))) ) | ~spl5_12),
% 2.11/0.66    inference(resolution,[],[f372,f231])).
% 2.11/0.66  fof(f231,plain,(
% 2.11/0.66    ( ! [X10,X11] : (~r2_hidden(sK4(X10,X11,u1_struct_0(sK0)),sK2) | u1_struct_0(sK0) = k2_xboole_0(X10,X11) | ~r2_hidden(sK4(X10,X11,u1_struct_0(sK0)),X11)) ) | ~spl5_12),
% 2.11/0.66    inference(resolution,[],[f39,f144])).
% 2.11/0.66  fof(f372,plain,(
% 2.11/0.66    ( ! [X4,X2,X3] : (r2_hidden(sK4(k2_xboole_0(X2,X3),X4,X4),X3) | r2_hidden(sK4(k2_xboole_0(X2,X3),X4,X4),X2) | k2_xboole_0(k2_xboole_0(X2,X3),X4) = X4) )),
% 2.11/0.66    inference(resolution,[],[f280,f46])).
% 2.11/0.66  fof(f1980,plain,(
% 2.11/0.66    spl5_58 | ~spl5_42 | ~spl5_44),
% 2.11/0.66    inference(avatar_split_clause,[],[f1955,f700,f611,f1977])).
% 2.11/0.66  fof(f1977,plain,(
% 2.11/0.66    spl5_58 <=> k2_xboole_0(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK3)) = k4_subset_1(k1_tops_1(sK0,u1_struct_0(sK0)),k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK3))),
% 2.11/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_58])])).
% 2.11/0.66  fof(f611,plain,(
% 2.11/0.66    spl5_42 <=> r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,u1_struct_0(sK0)))),
% 2.11/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_42])])).
% 2.11/0.66  fof(f700,plain,(
% 2.11/0.66    spl5_44 <=> r1_tarski(k1_tops_1(sK0,sK3),k1_tops_1(sK0,u1_struct_0(sK0)))),
% 2.11/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_44])])).
% 2.11/0.66  fof(f1955,plain,(
% 2.11/0.66    k2_xboole_0(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK3)) = k4_subset_1(k1_tops_1(sK0,u1_struct_0(sK0)),k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK3)) | (~spl5_42 | ~spl5_44)),
% 2.11/0.66    inference(resolution,[],[f1676,f613])).
% 2.11/0.66  fof(f613,plain,(
% 2.11/0.66    r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,u1_struct_0(sK0))) | ~spl5_42),
% 2.11/0.66    inference(avatar_component_clause,[],[f611])).
% 2.11/0.66  fof(f1676,plain,(
% 2.11/0.66    ( ! [X27] : (~r1_tarski(X27,k1_tops_1(sK0,u1_struct_0(sK0))) | k2_xboole_0(X27,k1_tops_1(sK0,sK3)) = k4_subset_1(k1_tops_1(sK0,u1_struct_0(sK0)),X27,k1_tops_1(sK0,sK3))) ) | ~spl5_44),
% 2.11/0.66    inference(resolution,[],[f451,f702])).
% 2.11/0.66  fof(f702,plain,(
% 2.11/0.66    r1_tarski(k1_tops_1(sK0,sK3),k1_tops_1(sK0,u1_struct_0(sK0))) | ~spl5_44),
% 2.11/0.66    inference(avatar_component_clause,[],[f700])).
% 2.11/0.66  fof(f1975,plain,(
% 2.11/0.66    spl5_57 | ~spl5_43 | ~spl5_44),
% 2.11/0.66    inference(avatar_split_clause,[],[f1965,f700,f654,f1972])).
% 2.11/0.66  fof(f1972,plain,(
% 2.11/0.66    spl5_57 <=> k1_tops_1(sK0,u1_struct_0(sK0)) = k4_subset_1(k1_tops_1(sK0,u1_struct_0(sK0)),k1_tops_1(sK0,u1_struct_0(sK0)),k1_tops_1(sK0,sK3))),
% 2.11/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_57])])).
% 2.11/0.66  fof(f654,plain,(
% 2.11/0.66    spl5_43 <=> k1_tops_1(sK0,u1_struct_0(sK0)) = k2_xboole_0(k1_tops_1(sK0,sK3),k1_tops_1(sK0,u1_struct_0(sK0)))),
% 2.11/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_43])])).
% 2.11/0.66  fof(f1965,plain,(
% 2.11/0.66    k1_tops_1(sK0,u1_struct_0(sK0)) = k4_subset_1(k1_tops_1(sK0,u1_struct_0(sK0)),k1_tops_1(sK0,u1_struct_0(sK0)),k1_tops_1(sK0,sK3)) | (~spl5_43 | ~spl5_44)),
% 2.11/0.66    inference(forward_demodulation,[],[f1964,f656])).
% 2.11/0.66  fof(f656,plain,(
% 2.11/0.66    k1_tops_1(sK0,u1_struct_0(sK0)) = k2_xboole_0(k1_tops_1(sK0,sK3),k1_tops_1(sK0,u1_struct_0(sK0))) | ~spl5_43),
% 2.11/0.66    inference(avatar_component_clause,[],[f654])).
% 2.11/0.66  fof(f1964,plain,(
% 2.11/0.66    k2_xboole_0(k1_tops_1(sK0,sK3),k1_tops_1(sK0,u1_struct_0(sK0))) = k4_subset_1(k1_tops_1(sK0,u1_struct_0(sK0)),k1_tops_1(sK0,u1_struct_0(sK0)),k1_tops_1(sK0,sK3)) | ~spl5_44),
% 2.11/0.66    inference(forward_demodulation,[],[f1959,f33])).
% 2.11/0.66  fof(f1959,plain,(
% 2.11/0.66    k2_xboole_0(k1_tops_1(sK0,u1_struct_0(sK0)),k1_tops_1(sK0,sK3)) = k4_subset_1(k1_tops_1(sK0,u1_struct_0(sK0)),k1_tops_1(sK0,u1_struct_0(sK0)),k1_tops_1(sK0,sK3)) | ~spl5_44),
% 2.11/0.66    inference(resolution,[],[f1676,f387])).
% 2.11/0.66  fof(f387,plain,(
% 2.11/0.66    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 2.11/0.66    inference(superposition,[],[f32,f377])).
% 2.11/0.66  fof(f377,plain,(
% 2.11/0.66    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 2.11/0.66    inference(subsumption_resolution,[],[f376,f40])).
% 2.11/0.66  fof(f376,plain,(
% 2.11/0.66    ( ! [X0] : (k2_xboole_0(X0,X0) = X0 | ~r2_hidden(sK4(X0,X0,X0),X0)) )),
% 2.11/0.66    inference(duplicate_literal_removal,[],[f370])).
% 2.11/0.66  fof(f370,plain,(
% 2.11/0.66    ( ! [X0] : (k2_xboole_0(X0,X0) = X0 | ~r2_hidden(sK4(X0,X0,X0),X0) | k2_xboole_0(X0,X0) = X0) )),
% 2.11/0.66    inference(resolution,[],[f280,f39])).
% 2.11/0.66  fof(f1970,plain,(
% 2.11/0.66    spl5_56 | ~spl5_44),
% 2.11/0.66    inference(avatar_split_clause,[],[f1960,f700,f1967])).
% 2.11/0.66  fof(f1967,plain,(
% 2.11/0.66    spl5_56 <=> k1_tops_1(sK0,sK3) = k4_subset_1(k1_tops_1(sK0,u1_struct_0(sK0)),k1_tops_1(sK0,sK3),k1_tops_1(sK0,sK3))),
% 2.11/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_56])])).
% 2.11/0.66  fof(f1960,plain,(
% 2.11/0.66    k1_tops_1(sK0,sK3) = k4_subset_1(k1_tops_1(sK0,u1_struct_0(sK0)),k1_tops_1(sK0,sK3),k1_tops_1(sK0,sK3)) | ~spl5_44),
% 2.11/0.66    inference(forward_demodulation,[],[f1957,f377])).
% 2.11/0.66  fof(f1957,plain,(
% 2.11/0.66    k2_xboole_0(k1_tops_1(sK0,sK3),k1_tops_1(sK0,sK3)) = k4_subset_1(k1_tops_1(sK0,u1_struct_0(sK0)),k1_tops_1(sK0,sK3),k1_tops_1(sK0,sK3)) | ~spl5_44),
% 2.11/0.66    inference(resolution,[],[f1676,f702])).
% 2.11/0.66  fof(f1954,plain,(
% 2.11/0.66    spl5_55 | ~spl5_42 | ~spl5_44),
% 2.11/0.66    inference(avatar_split_clause,[],[f1934,f700,f611,f1951])).
% 2.11/0.66  fof(f1951,plain,(
% 2.11/0.66    spl5_55 <=> k2_xboole_0(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK3)) = k4_subset_1(k1_tops_1(sK0,u1_struct_0(sK0)),k1_tops_1(sK0,sK3),k1_tops_1(sK0,sK2))),
% 2.11/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_55])])).
% 2.11/0.66  fof(f1934,plain,(
% 2.11/0.66    k2_xboole_0(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK3)) = k4_subset_1(k1_tops_1(sK0,u1_struct_0(sK0)),k1_tops_1(sK0,sK3),k1_tops_1(sK0,sK2)) | (~spl5_42 | ~spl5_44)),
% 2.11/0.66    inference(forward_demodulation,[],[f1927,f33])).
% 2.11/0.66  fof(f1927,plain,(
% 2.11/0.66    k2_xboole_0(k1_tops_1(sK0,sK3),k1_tops_1(sK0,sK2)) = k4_subset_1(k1_tops_1(sK0,u1_struct_0(sK0)),k1_tops_1(sK0,sK3),k1_tops_1(sK0,sK2)) | (~spl5_42 | ~spl5_44)),
% 2.11/0.66    inference(resolution,[],[f1674,f702])).
% 2.11/0.66  fof(f1674,plain,(
% 2.11/0.66    ( ! [X24] : (~r1_tarski(X24,k1_tops_1(sK0,u1_struct_0(sK0))) | k2_xboole_0(X24,k1_tops_1(sK0,sK2)) = k4_subset_1(k1_tops_1(sK0,u1_struct_0(sK0)),X24,k1_tops_1(sK0,sK2))) ) | ~spl5_42),
% 2.11/0.66    inference(resolution,[],[f451,f613])).
% 2.11/0.66  fof(f1949,plain,(
% 2.11/0.66    spl5_54 | ~spl5_41 | ~spl5_42),
% 2.11/0.66    inference(avatar_split_clause,[],[f1939,f611,f595,f1946])).
% 2.11/0.66  fof(f1946,plain,(
% 2.11/0.66    spl5_54 <=> k1_tops_1(sK0,u1_struct_0(sK0)) = k4_subset_1(k1_tops_1(sK0,u1_struct_0(sK0)),k1_tops_1(sK0,u1_struct_0(sK0)),k1_tops_1(sK0,sK2))),
% 2.11/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_54])])).
% 2.11/0.66  fof(f595,plain,(
% 2.11/0.66    spl5_41 <=> k1_tops_1(sK0,u1_struct_0(sK0)) = k2_xboole_0(k1_tops_1(sK0,sK2),k1_tops_1(sK0,u1_struct_0(sK0)))),
% 2.11/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_41])])).
% 2.11/0.66  fof(f1939,plain,(
% 2.11/0.66    k1_tops_1(sK0,u1_struct_0(sK0)) = k4_subset_1(k1_tops_1(sK0,u1_struct_0(sK0)),k1_tops_1(sK0,u1_struct_0(sK0)),k1_tops_1(sK0,sK2)) | (~spl5_41 | ~spl5_42)),
% 2.11/0.66    inference(forward_demodulation,[],[f1938,f597])).
% 2.11/0.66  fof(f597,plain,(
% 2.11/0.66    k1_tops_1(sK0,u1_struct_0(sK0)) = k2_xboole_0(k1_tops_1(sK0,sK2),k1_tops_1(sK0,u1_struct_0(sK0))) | ~spl5_41),
% 2.11/0.66    inference(avatar_component_clause,[],[f595])).
% 2.11/0.66  fof(f1938,plain,(
% 2.11/0.66    k2_xboole_0(k1_tops_1(sK0,sK2),k1_tops_1(sK0,u1_struct_0(sK0))) = k4_subset_1(k1_tops_1(sK0,u1_struct_0(sK0)),k1_tops_1(sK0,u1_struct_0(sK0)),k1_tops_1(sK0,sK2)) | ~spl5_42),
% 2.11/0.66    inference(forward_demodulation,[],[f1929,f33])).
% 2.11/0.66  fof(f1929,plain,(
% 2.11/0.66    k2_xboole_0(k1_tops_1(sK0,u1_struct_0(sK0)),k1_tops_1(sK0,sK2)) = k4_subset_1(k1_tops_1(sK0,u1_struct_0(sK0)),k1_tops_1(sK0,u1_struct_0(sK0)),k1_tops_1(sK0,sK2)) | ~spl5_42),
% 2.11/0.66    inference(resolution,[],[f1674,f387])).
% 2.11/0.66  fof(f1944,plain,(
% 2.11/0.66    spl5_53 | ~spl5_42),
% 2.11/0.66    inference(avatar_split_clause,[],[f1930,f611,f1941])).
% 2.11/0.66  fof(f1941,plain,(
% 2.11/0.66    spl5_53 <=> k1_tops_1(sK0,sK2) = k4_subset_1(k1_tops_1(sK0,u1_struct_0(sK0)),k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK2))),
% 2.11/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_53])])).
% 2.11/0.66  fof(f1930,plain,(
% 2.11/0.66    k1_tops_1(sK0,sK2) = k4_subset_1(k1_tops_1(sK0,u1_struct_0(sK0)),k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK2)) | ~spl5_42),
% 2.11/0.66    inference(forward_demodulation,[],[f1925,f377])).
% 2.11/0.66  fof(f1925,plain,(
% 2.11/0.66    k2_xboole_0(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK2)) = k4_subset_1(k1_tops_1(sK0,u1_struct_0(sK0)),k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK2)) | ~spl5_42),
% 2.11/0.66    inference(resolution,[],[f1674,f613])).
% 2.11/0.66  fof(f1880,plain,(
% 2.11/0.66    ~spl5_52 | spl5_50 | ~spl5_51),
% 2.11/0.66    inference(avatar_split_clause,[],[f1874,f1868,f1864,f1877])).
% 2.11/0.66  fof(f1877,plain,(
% 2.11/0.66    spl5_52 <=> r2_hidden(sK4(sK3,sK3,u1_struct_0(sK0)),sK3)),
% 2.11/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_52])])).
% 2.11/0.66  fof(f1864,plain,(
% 2.11/0.66    spl5_50 <=> sK3 = u1_struct_0(sK0)),
% 2.11/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_50])])).
% 2.11/0.66  fof(f1868,plain,(
% 2.11/0.66    spl5_51 <=> r2_hidden(sK4(sK3,sK3,u1_struct_0(sK0)),u1_struct_0(sK0))),
% 2.11/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_51])])).
% 2.11/0.66  fof(f1874,plain,(
% 2.11/0.66    sK3 = u1_struct_0(sK0) | ~r2_hidden(sK4(sK3,sK3,u1_struct_0(sK0)),sK3) | ~spl5_51),
% 2.11/0.66    inference(forward_demodulation,[],[f1872,f377])).
% 2.11/0.66  fof(f1872,plain,(
% 2.11/0.66    ~r2_hidden(sK4(sK3,sK3,u1_struct_0(sK0)),sK3) | u1_struct_0(sK0) = k2_xboole_0(sK3,sK3) | ~spl5_51),
% 2.11/0.66    inference(resolution,[],[f1870,f39])).
% 2.11/0.66  fof(f1870,plain,(
% 2.11/0.66    r2_hidden(sK4(sK3,sK3,u1_struct_0(sK0)),u1_struct_0(sK0)) | ~spl5_51),
% 2.11/0.66    inference(avatar_component_clause,[],[f1868])).
% 2.11/0.66  fof(f1871,plain,(
% 2.11/0.66    spl5_50 | spl5_51 | ~spl5_13 | ~spl5_15),
% 2.11/0.66    inference(avatar_split_clause,[],[f1853,f138,f119,f1868,f1864])).
% 2.11/0.66  fof(f138,plain,(
% 2.11/0.66    spl5_15 <=> u1_struct_0(sK0) = k2_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0))),
% 2.11/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 2.11/0.66  fof(f1853,plain,(
% 2.11/0.66    r2_hidden(sK4(sK3,sK3,u1_struct_0(sK0)),u1_struct_0(sK0)) | sK3 = u1_struct_0(sK0) | (~spl5_13 | ~spl5_15)),
% 2.11/0.66    inference(superposition,[],[f1501,f140])).
% 2.11/0.66  fof(f140,plain,(
% 2.11/0.66    u1_struct_0(sK0) = k2_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0)) | ~spl5_15),
% 2.11/0.66    inference(avatar_component_clause,[],[f138])).
% 2.11/0.66  fof(f1501,plain,(
% 2.11/0.66    ( ! [X12] : (r2_hidden(sK4(sK3,sK3,k2_xboole_0(u1_struct_0(sK0),X12)),k2_xboole_0(u1_struct_0(sK0),X12)) | sK3 = k2_xboole_0(u1_struct_0(sK0),X12)) ) | ~spl5_13),
% 2.11/0.66    inference(forward_demodulation,[],[f1500,f377])).
% 2.11/0.66  fof(f1500,plain,(
% 2.11/0.66    ( ! [X12] : (k2_xboole_0(sK3,sK3) = k2_xboole_0(u1_struct_0(sK0),X12) | r2_hidden(sK4(sK3,sK3,k2_xboole_0(u1_struct_0(sK0),X12)),k2_xboole_0(u1_struct_0(sK0),X12))) ) | ~spl5_13),
% 2.11/0.66    inference(subsumption_resolution,[],[f1489,f1499])).
% 2.11/0.66  fof(f1499,plain,(
% 2.11/0.66    ( ! [X10,X11] : (k2_xboole_0(u1_struct_0(sK0),X11) = k2_xboole_0(sK3,X10) | r2_hidden(sK4(sK3,X10,k2_xboole_0(u1_struct_0(sK0),X11)),k2_xboole_0(u1_struct_0(sK0),X11)) | r2_hidden(sK4(sK3,X10,k2_xboole_0(u1_struct_0(sK0),X11)),X10)) ) | ~spl5_13),
% 2.11/0.66    inference(subsumption_resolution,[],[f1490,f40])).
% 2.11/0.66  fof(f1490,plain,(
% 2.11/0.66    ( ! [X10,X11] : (~r2_hidden(sK4(sK3,X10,k2_xboole_0(u1_struct_0(sK0),X11)),sK3) | k2_xboole_0(u1_struct_0(sK0),X11) = k2_xboole_0(sK3,X10) | r2_hidden(sK4(sK3,X10,k2_xboole_0(u1_struct_0(sK0),X11)),k2_xboole_0(u1_struct_0(sK0),X11)) | r2_hidden(sK4(sK3,X10,k2_xboole_0(u1_struct_0(sK0),X11)),X10)) ) | ~spl5_13),
% 2.11/0.66    inference(duplicate_literal_removal,[],[f1467])).
% 2.11/0.66  fof(f1467,plain,(
% 2.11/0.66    ( ! [X10,X11] : (~r2_hidden(sK4(sK3,X10,k2_xboole_0(u1_struct_0(sK0),X11)),sK3) | k2_xboole_0(u1_struct_0(sK0),X11) = k2_xboole_0(sK3,X10) | r2_hidden(sK4(sK3,X10,k2_xboole_0(u1_struct_0(sK0),X11)),k2_xboole_0(u1_struct_0(sK0),X11)) | r2_hidden(sK4(sK3,X10,k2_xboole_0(u1_struct_0(sK0),X11)),X10) | k2_xboole_0(u1_struct_0(sK0),X11) = k2_xboole_0(sK3,X10)) ) | ~spl5_13),
% 2.11/0.66    inference(resolution,[],[f529,f40])).
% 2.11/0.66  fof(f1489,plain,(
% 2.11/0.66    ( ! [X12] : (~r2_hidden(sK4(sK3,sK3,k2_xboole_0(u1_struct_0(sK0),X12)),sK3) | k2_xboole_0(sK3,sK3) = k2_xboole_0(u1_struct_0(sK0),X12) | r2_hidden(sK4(sK3,sK3,k2_xboole_0(u1_struct_0(sK0),X12)),k2_xboole_0(u1_struct_0(sK0),X12))) ) | ~spl5_13),
% 2.11/0.66    inference(duplicate_literal_removal,[],[f1468])).
% 2.11/0.66  fof(f1468,plain,(
% 2.11/0.66    ( ! [X12] : (~r2_hidden(sK4(sK3,sK3,k2_xboole_0(u1_struct_0(sK0),X12)),sK3) | k2_xboole_0(sK3,sK3) = k2_xboole_0(u1_struct_0(sK0),X12) | r2_hidden(sK4(sK3,sK3,k2_xboole_0(u1_struct_0(sK0),X12)),k2_xboole_0(u1_struct_0(sK0),X12)) | k2_xboole_0(sK3,sK3) = k2_xboole_0(u1_struct_0(sK0),X12)) ) | ~spl5_13),
% 2.11/0.66    inference(resolution,[],[f529,f273])).
% 2.11/0.66  fof(f273,plain,(
% 2.11/0.66    ( ! [X4,X5] : (r2_hidden(sK4(X4,X4,X5),X5) | r2_hidden(sK4(X4,X4,X5),X4) | k2_xboole_0(X4,X4) = X5) )),
% 2.11/0.66    inference(factoring,[],[f40])).
% 2.11/0.66  fof(f1750,plain,(
% 2.11/0.66    spl5_49 | ~spl5_13 | ~spl5_15),
% 2.11/0.66    inference(avatar_split_clause,[],[f1738,f138,f119,f1747])).
% 2.11/0.66  fof(f1747,plain,(
% 2.11/0.66    spl5_49 <=> sK3 = k4_subset_1(u1_struct_0(sK0),sK3,sK3)),
% 2.11/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_49])])).
% 2.11/0.66  fof(f1738,plain,(
% 2.11/0.66    sK3 = k4_subset_1(u1_struct_0(sK0),sK3,sK3) | (~spl5_13 | ~spl5_15)),
% 2.11/0.66    inference(superposition,[],[f1734,f140])).
% 2.11/0.66  fof(f1734,plain,(
% 2.11/0.66    ( ! [X3] : (sK3 = k4_subset_1(k2_xboole_0(u1_struct_0(sK0),X3),sK3,sK3)) ) | ~spl5_13),
% 2.11/0.66    inference(forward_demodulation,[],[f1719,f377])).
% 2.11/0.66  fof(f1719,plain,(
% 2.11/0.66    ( ! [X3] : (k2_xboole_0(sK3,sK3) = k4_subset_1(k2_xboole_0(u1_struct_0(sK0),X3),sK3,sK3)) ) | ~spl5_13),
% 2.11/0.66    inference(resolution,[],[f1666,f1513])).
% 2.11/0.66  fof(f1175,plain,(
% 2.11/0.66    spl5_48 | ~spl5_43),
% 2.11/0.66    inference(avatar_split_clause,[],[f966,f654,f1172])).
% 2.11/0.66  fof(f1172,plain,(
% 2.11/0.66    spl5_48 <=> k1_tops_1(sK0,u1_struct_0(sK0)) = k2_xboole_0(k1_tops_1(sK0,u1_struct_0(sK0)),k1_tops_1(sK0,sK3))),
% 2.11/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_48])])).
% 2.11/0.66  fof(f966,plain,(
% 2.11/0.66    k1_tops_1(sK0,u1_struct_0(sK0)) = k2_xboole_0(k1_tops_1(sK0,u1_struct_0(sK0)),k1_tops_1(sK0,sK3)) | ~spl5_43),
% 2.11/0.66    inference(superposition,[],[f641,f656])).
% 2.11/0.66  fof(f994,plain,(
% 2.11/0.66    spl5_47 | ~spl5_41),
% 2.11/0.66    inference(avatar_split_clause,[],[f965,f595,f991])).
% 2.11/0.66  fof(f991,plain,(
% 2.11/0.66    spl5_47 <=> k1_tops_1(sK0,u1_struct_0(sK0)) = k2_xboole_0(k1_tops_1(sK0,u1_struct_0(sK0)),k1_tops_1(sK0,sK2))),
% 2.11/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_47])])).
% 2.11/0.66  fof(f965,plain,(
% 2.11/0.66    k1_tops_1(sK0,u1_struct_0(sK0)) = k2_xboole_0(k1_tops_1(sK0,u1_struct_0(sK0)),k1_tops_1(sK0,sK2)) | ~spl5_41),
% 2.11/0.66    inference(superposition,[],[f641,f597])).
% 2.11/0.66  fof(f770,plain,(
% 2.11/0.66    spl5_46 | spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_6 | ~spl5_14 | ~spl5_45),
% 2.11/0.66    inference(avatar_split_clause,[],[f765,f744,f129,f73,f58,f53,f48,f767])).
% 2.11/0.66  fof(f767,plain,(
% 2.11/0.66    spl5_46 <=> r2_hidden(sK1,k1_tops_1(sK0,u1_struct_0(sK0)))),
% 2.11/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_46])])).
% 2.11/0.66  fof(f129,plain,(
% 2.11/0.66    spl5_14 <=> r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0))),
% 2.11/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 2.11/0.66  fof(f744,plain,(
% 2.11/0.66    spl5_45 <=> m1_connsp_2(u1_struct_0(sK0),sK0,sK1)),
% 2.11/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_45])])).
% 2.11/0.66  fof(f765,plain,(
% 2.11/0.66    r2_hidden(sK1,k1_tops_1(sK0,u1_struct_0(sK0))) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_6 | ~spl5_14 | ~spl5_45)),
% 2.11/0.66    inference(subsumption_resolution,[],[f764,f131])).
% 2.11/0.66  fof(f131,plain,(
% 2.11/0.66    r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0)) | ~spl5_14),
% 2.11/0.66    inference(avatar_component_clause,[],[f129])).
% 2.11/0.66  fof(f764,plain,(
% 2.11/0.66    r2_hidden(sK1,k1_tops_1(sK0,u1_struct_0(sK0))) | ~r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0)) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_6 | ~spl5_45)),
% 2.11/0.66    inference(subsumption_resolution,[],[f763,f55])).
% 2.11/0.66  fof(f763,plain,(
% 2.11/0.66    r2_hidden(sK1,k1_tops_1(sK0,u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | ~r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0)) | (spl5_1 | ~spl5_3 | ~spl5_6 | ~spl5_45)),
% 2.11/0.66    inference(subsumption_resolution,[],[f762,f50])).
% 2.11/0.66  fof(f762,plain,(
% 2.11/0.66    v2_struct_0(sK0) | r2_hidden(sK1,k1_tops_1(sK0,u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | ~r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0)) | (~spl5_3 | ~spl5_6 | ~spl5_45)),
% 2.11/0.66    inference(subsumption_resolution,[],[f761,f75])).
% 2.11/0.66  fof(f761,plain,(
% 2.11/0.66    ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | r2_hidden(sK1,k1_tops_1(sK0,u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | ~r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0)) | (~spl5_3 | ~spl5_45)),
% 2.11/0.66    inference(subsumption_resolution,[],[f760,f60])).
% 2.11/0.66  fof(f760,plain,(
% 2.11/0.66    ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | r2_hidden(sK1,k1_tops_1(sK0,u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | ~r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0)) | ~spl5_45),
% 2.11/0.66    inference(resolution,[],[f312,f746])).
% 2.11/0.66  fof(f746,plain,(
% 2.11/0.66    m1_connsp_2(u1_struct_0(sK0),sK0,sK1) | ~spl5_45),
% 2.11/0.66    inference(avatar_component_clause,[],[f744])).
% 2.11/0.66  fof(f312,plain,(
% 2.11/0.66    ( ! [X2,X0,X1] : (~m1_connsp_2(X2,X0,X1) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0) | r2_hidden(X1,k1_tops_1(X0,X2)) | ~v2_pre_topc(X0) | ~r1_tarski(X2,u1_struct_0(X0))) )),
% 2.11/0.66    inference(resolution,[],[f31,f35])).
% 2.11/0.66  fof(f31,plain,(
% 2.11/0.66    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0) | r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1)) )),
% 2.11/0.66    inference(cnf_transformation,[],[f16])).
% 2.11/0.66  fof(f747,plain,(
% 2.11/0.66    spl5_45 | spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_6 | ~spl5_14 | ~spl5_24 | ~spl5_43),
% 2.11/0.66    inference(avatar_split_clause,[],[f742,f654,f335,f129,f73,f58,f53,f48,f744])).
% 2.11/0.66  fof(f335,plain,(
% 2.11/0.66    spl5_24 <=> r2_hidden(sK1,k1_tops_1(sK0,sK3))),
% 2.11/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 2.11/0.66  fof(f742,plain,(
% 2.11/0.66    m1_connsp_2(u1_struct_0(sK0),sK0,sK1) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_6 | ~spl5_14 | ~spl5_24 | ~spl5_43)),
% 2.11/0.66    inference(subsumption_resolution,[],[f739,f75])).
% 2.11/0.66  fof(f739,plain,(
% 2.11/0.66    m1_connsp_2(u1_struct_0(sK0),sK0,sK1) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_14 | ~spl5_24 | ~spl5_43)),
% 2.11/0.66    inference(resolution,[],[f725,f337])).
% 2.11/0.66  fof(f337,plain,(
% 2.11/0.66    r2_hidden(sK1,k1_tops_1(sK0,sK3)) | ~spl5_24),
% 2.11/0.66    inference(avatar_component_clause,[],[f335])).
% 2.11/0.66  fof(f725,plain,(
% 2.11/0.66    ( ! [X0] : (~r2_hidden(X0,k1_tops_1(sK0,sK3)) | m1_connsp_2(u1_struct_0(sK0),sK0,X0) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_14 | ~spl5_43)),
% 2.11/0.66    inference(subsumption_resolution,[],[f724,f131])).
% 2.11/0.66  fof(f724,plain,(
% 2.11/0.66    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | m1_connsp_2(u1_struct_0(sK0),sK0,X0) | ~r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0)) | ~r2_hidden(X0,k1_tops_1(sK0,sK3))) ) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_43)),
% 2.11/0.66    inference(subsumption_resolution,[],[f723,f55])).
% 2.11/0.66  fof(f723,plain,(
% 2.11/0.66    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~v2_pre_topc(sK0) | m1_connsp_2(u1_struct_0(sK0),sK0,X0) | ~r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0)) | ~r2_hidden(X0,k1_tops_1(sK0,sK3))) ) | (spl5_1 | ~spl5_3 | ~spl5_43)),
% 2.11/0.66    inference(subsumption_resolution,[],[f722,f50])).
% 2.11/0.66  fof(f722,plain,(
% 2.11/0.66    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | m1_connsp_2(u1_struct_0(sK0),sK0,X0) | ~r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0)) | ~r2_hidden(X0,k1_tops_1(sK0,sK3))) ) | (~spl5_3 | ~spl5_43)),
% 2.11/0.66    inference(subsumption_resolution,[],[f711,f60])).
% 2.11/0.66  fof(f711,plain,(
% 2.11/0.66    ( ! [X0] : (~l1_pre_topc(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | m1_connsp_2(u1_struct_0(sK0),sK0,X0) | ~r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0)) | ~r2_hidden(X0,k1_tops_1(sK0,sK3))) ) | ~spl5_43),
% 2.11/0.66    inference(resolution,[],[f292,f688])).
% 2.11/0.66  fof(f688,plain,(
% 2.11/0.66    ( ! [X1] : (r2_hidden(X1,k1_tops_1(sK0,u1_struct_0(sK0))) | ~r2_hidden(X1,k1_tops_1(sK0,sK3))) ) | ~spl5_43),
% 2.11/0.66    inference(superposition,[],[f45,f656])).
% 2.11/0.66  fof(f703,plain,(
% 2.11/0.66    spl5_44 | ~spl5_43),
% 2.11/0.66    inference(avatar_split_clause,[],[f686,f654,f700])).
% 2.11/0.66  fof(f686,plain,(
% 2.11/0.66    r1_tarski(k1_tops_1(sK0,sK3),k1_tops_1(sK0,u1_struct_0(sK0))) | ~spl5_43),
% 2.11/0.66    inference(superposition,[],[f32,f656])).
% 2.11/0.66  fof(f657,plain,(
% 2.11/0.66    spl5_43 | ~spl5_3 | ~spl5_7 | ~spl5_11 | ~spl5_14),
% 2.11/0.66    inference(avatar_split_clause,[],[f652,f129,f105,f78,f58,f654])).
% 2.11/0.66  fof(f105,plain,(
% 2.11/0.66    spl5_11 <=> r1_tarski(sK3,u1_struct_0(sK0))),
% 2.11/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 2.11/0.66  fof(f652,plain,(
% 2.11/0.66    k1_tops_1(sK0,u1_struct_0(sK0)) = k2_xboole_0(k1_tops_1(sK0,sK3),k1_tops_1(sK0,u1_struct_0(sK0))) | (~spl5_3 | ~spl5_7 | ~spl5_11 | ~spl5_14)),
% 2.11/0.66    inference(subsumption_resolution,[],[f650,f107])).
% 2.11/0.66  fof(f107,plain,(
% 2.11/0.66    r1_tarski(sK3,u1_struct_0(sK0)) | ~spl5_11),
% 2.11/0.66    inference(avatar_component_clause,[],[f105])).
% 2.11/0.66  fof(f650,plain,(
% 2.11/0.66    ~r1_tarski(sK3,u1_struct_0(sK0)) | k1_tops_1(sK0,u1_struct_0(sK0)) = k2_xboole_0(k1_tops_1(sK0,sK3),k1_tops_1(sK0,u1_struct_0(sK0))) | (~spl5_3 | ~spl5_7 | ~spl5_14)),
% 2.11/0.66    inference(resolution,[],[f506,f131])).
% 2.11/0.66  fof(f614,plain,(
% 2.11/0.66    spl5_42 | ~spl5_41),
% 2.11/0.66    inference(avatar_split_clause,[],[f599,f595,f611])).
% 2.11/0.66  fof(f599,plain,(
% 2.11/0.66    r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,u1_struct_0(sK0))) | ~spl5_41),
% 2.11/0.66    inference(superposition,[],[f32,f597])).
% 2.11/0.66  fof(f598,plain,(
% 2.11/0.66    spl5_41 | ~spl5_3 | ~spl5_8 | ~spl5_10 | ~spl5_14),
% 2.11/0.66    inference(avatar_split_clause,[],[f593,f129,f100,f83,f58,f595])).
% 2.11/0.66  fof(f100,plain,(
% 2.11/0.66    spl5_10 <=> r1_tarski(sK2,u1_struct_0(sK0))),
% 2.11/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 2.11/0.66  fof(f593,plain,(
% 2.11/0.66    k1_tops_1(sK0,u1_struct_0(sK0)) = k2_xboole_0(k1_tops_1(sK0,sK2),k1_tops_1(sK0,u1_struct_0(sK0))) | (~spl5_3 | ~spl5_8 | ~spl5_10 | ~spl5_14)),
% 2.11/0.66    inference(subsumption_resolution,[],[f591,f102])).
% 2.11/0.66  fof(f102,plain,(
% 2.11/0.66    r1_tarski(sK2,u1_struct_0(sK0)) | ~spl5_10),
% 2.11/0.66    inference(avatar_component_clause,[],[f100])).
% 2.11/0.66  fof(f591,plain,(
% 2.11/0.66    ~r1_tarski(sK2,u1_struct_0(sK0)) | k1_tops_1(sK0,u1_struct_0(sK0)) = k2_xboole_0(k1_tops_1(sK0,sK2),k1_tops_1(sK0,u1_struct_0(sK0))) | (~spl5_3 | ~spl5_8 | ~spl5_14)),
% 2.11/0.66    inference(resolution,[],[f505,f131])).
% 2.11/0.66  fof(f562,plain,(
% 2.11/0.66    ~spl5_39 | spl5_40 | ~spl5_3 | ~spl5_7 | ~spl5_14),
% 2.11/0.66    inference(avatar_split_clause,[],[f552,f129,f78,f58,f559,f555])).
% 2.11/0.66  fof(f555,plain,(
% 2.11/0.66    spl5_39 <=> r1_tarski(u1_struct_0(sK0),sK3)),
% 2.11/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_39])])).
% 2.11/0.66  fof(f559,plain,(
% 2.11/0.66    spl5_40 <=> k1_tops_1(sK0,sK3) = k2_xboole_0(k1_tops_1(sK0,sK3),k1_tops_1(sK0,u1_struct_0(sK0)))),
% 2.11/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_40])])).
% 2.11/0.66  fof(f552,plain,(
% 2.11/0.66    k1_tops_1(sK0,sK3) = k2_xboole_0(k1_tops_1(sK0,sK3),k1_tops_1(sK0,u1_struct_0(sK0))) | ~r1_tarski(u1_struct_0(sK0),sK3) | (~spl5_3 | ~spl5_7 | ~spl5_14)),
% 2.11/0.66    inference(forward_demodulation,[],[f550,f33])).
% 2.11/0.66  fof(f550,plain,(
% 2.11/0.66    ~r1_tarski(u1_struct_0(sK0),sK3) | k1_tops_1(sK0,sK3) = k2_xboole_0(k1_tops_1(sK0,u1_struct_0(sK0)),k1_tops_1(sK0,sK3)) | (~spl5_3 | ~spl5_7 | ~spl5_14)),
% 2.11/0.66    inference(resolution,[],[f499,f131])).
% 2.11/0.66  fof(f499,plain,(
% 2.11/0.66    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK0)) | ~r1_tarski(X0,sK3) | k1_tops_1(sK0,sK3) = k2_xboole_0(k1_tops_1(sK0,X0),k1_tops_1(sK0,sK3))) ) | (~spl5_3 | ~spl5_7)),
% 2.11/0.66    inference(resolution,[],[f349,f34])).
% 2.11/0.66  fof(f349,plain,(
% 2.11/0.66    ( ! [X0] : (r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,sK3)) | ~r1_tarski(X0,sK3) | ~r1_tarski(X0,u1_struct_0(sK0))) ) | (~spl5_3 | ~spl5_7)),
% 2.11/0.66    inference(resolution,[],[f247,f35])).
% 2.11/0.66  fof(f247,plain,(
% 2.11/0.66    ( ! [X4] : (~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X4,sK3) | r1_tarski(k1_tops_1(sK0,X4),k1_tops_1(sK0,sK3))) ) | (~spl5_3 | ~spl5_7)),
% 2.11/0.66    inference(subsumption_resolution,[],[f245,f60])).
% 2.11/0.66  fof(f245,plain,(
% 2.11/0.66    ( ! [X4] : (~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~r1_tarski(X4,sK3) | r1_tarski(k1_tops_1(sK0,X4),k1_tops_1(sK0,sK3))) ) | ~spl5_7),
% 2.11/0.66    inference(resolution,[],[f29,f80])).
% 2.11/0.66  fof(f521,plain,(
% 2.11/0.66    ~spl5_37 | spl5_38 | ~spl5_3 | ~spl5_8 | ~spl5_14),
% 2.11/0.66    inference(avatar_split_clause,[],[f511,f129,f83,f58,f518,f514])).
% 2.11/0.66  fof(f514,plain,(
% 2.11/0.66    spl5_37 <=> r1_tarski(u1_struct_0(sK0),sK2)),
% 2.11/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).
% 2.11/0.66  fof(f518,plain,(
% 2.11/0.66    spl5_38 <=> k1_tops_1(sK0,sK2) = k2_xboole_0(k1_tops_1(sK0,sK2),k1_tops_1(sK0,u1_struct_0(sK0)))),
% 2.11/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).
% 2.11/0.66  fof(f511,plain,(
% 2.11/0.66    k1_tops_1(sK0,sK2) = k2_xboole_0(k1_tops_1(sK0,sK2),k1_tops_1(sK0,u1_struct_0(sK0))) | ~r1_tarski(u1_struct_0(sK0),sK2) | (~spl5_3 | ~spl5_8 | ~spl5_14)),
% 2.11/0.66    inference(forward_demodulation,[],[f509,f33])).
% 2.11/0.66  fof(f509,plain,(
% 2.11/0.66    ~r1_tarski(u1_struct_0(sK0),sK2) | k1_tops_1(sK0,sK2) = k2_xboole_0(k1_tops_1(sK0,u1_struct_0(sK0)),k1_tops_1(sK0,sK2)) | (~spl5_3 | ~spl5_8 | ~spl5_14)),
% 2.11/0.66    inference(resolution,[],[f498,f131])).
% 2.11/0.66  fof(f498,plain,(
% 2.11/0.66    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK0)) | ~r1_tarski(X0,sK2) | k1_tops_1(sK0,sK2) = k2_xboole_0(k1_tops_1(sK0,X0),k1_tops_1(sK0,sK2))) ) | (~spl5_3 | ~spl5_8)),
% 2.11/0.66    inference(resolution,[],[f331,f34])).
% 2.11/0.66  fof(f331,plain,(
% 2.11/0.66    ( ! [X0] : (r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,sK2)) | ~r1_tarski(X0,sK2) | ~r1_tarski(X0,u1_struct_0(sK0))) ) | (~spl5_3 | ~spl5_8)),
% 2.11/0.66    inference(resolution,[],[f246,f35])).
% 2.11/0.66  fof(f246,plain,(
% 2.11/0.66    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X3,sK2) | r1_tarski(k1_tops_1(sK0,X3),k1_tops_1(sK0,sK2))) ) | (~spl5_3 | ~spl5_8)),
% 2.11/0.66    inference(subsumption_resolution,[],[f244,f60])).
% 2.11/0.66  fof(f244,plain,(
% 2.11/0.66    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~r1_tarski(X3,sK2) | r1_tarski(k1_tops_1(sK0,X3),k1_tops_1(sK0,sK2))) ) | ~spl5_8),
% 2.11/0.66    inference(resolution,[],[f29,f85])).
% 2.11/0.66  fof(f497,plain,(
% 2.11/0.66    spl5_36 | ~spl5_7 | ~spl5_13 | ~spl5_14),
% 2.11/0.66    inference(avatar_split_clause,[],[f470,f129,f119,f78,f494])).
% 2.11/0.66  fof(f494,plain,(
% 2.11/0.66    spl5_36 <=> u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK3,u1_struct_0(sK0))),
% 2.11/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).
% 2.11/0.66  fof(f470,plain,(
% 2.11/0.66    u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK3,u1_struct_0(sK0)) | (~spl5_7 | ~spl5_13 | ~spl5_14)),
% 2.11/0.66    inference(forward_demodulation,[],[f467,f121])).
% 2.11/0.66  fof(f467,plain,(
% 2.11/0.66    k2_xboole_0(sK3,u1_struct_0(sK0)) = k4_subset_1(u1_struct_0(sK0),sK3,u1_struct_0(sK0)) | (~spl5_7 | ~spl5_14)),
% 2.11/0.66    inference(resolution,[],[f453,f131])).
% 2.11/0.66  fof(f464,plain,(
% 2.11/0.66    spl5_35 | ~spl5_8 | ~spl5_12 | ~spl5_14),
% 2.11/0.66    inference(avatar_split_clause,[],[f458,f129,f114,f83,f461])).
% 2.11/0.66  fof(f461,plain,(
% 2.11/0.66    spl5_35 <=> u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0))),
% 2.11/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).
% 2.11/0.66  fof(f458,plain,(
% 2.11/0.66    u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)) | (~spl5_8 | ~spl5_12 | ~spl5_14)),
% 2.11/0.66    inference(forward_demodulation,[],[f456,f116])).
% 2.11/0.66  fof(f456,plain,(
% 2.11/0.66    k2_xboole_0(sK2,u1_struct_0(sK0)) = k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)) | (~spl5_8 | ~spl5_14)),
% 2.11/0.66    inference(resolution,[],[f452,f131])).
% 2.11/0.66  fof(f424,plain,(
% 2.11/0.66    spl5_34 | ~spl5_8 | ~spl5_18),
% 2.11/0.66    inference(avatar_split_clause,[],[f407,f239,f83,f421])).
% 2.11/0.66  fof(f421,plain,(
% 2.11/0.66    spl5_34 <=> u1_struct_0(sK0) = k2_xboole_0(u1_struct_0(sK0),sK2)),
% 2.11/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).
% 2.11/0.66  fof(f239,plain,(
% 2.11/0.66    spl5_18 <=> u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2)),
% 2.11/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 2.11/0.66  fof(f407,plain,(
% 2.11/0.66    u1_struct_0(sK0) = k2_xboole_0(u1_struct_0(sK0),sK2) | (~spl5_8 | ~spl5_18)),
% 2.11/0.66    inference(forward_demodulation,[],[f400,f241])).
% 2.11/0.66  fof(f241,plain,(
% 2.11/0.66    u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) | ~spl5_18),
% 2.11/0.66    inference(avatar_component_clause,[],[f239])).
% 2.11/0.66  fof(f400,plain,(
% 2.11/0.66    k2_xboole_0(u1_struct_0(sK0),sK2) = k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) | ~spl5_8),
% 2.11/0.66    inference(resolution,[],[f387,f214])).
% 2.11/0.66  fof(f419,plain,(
% 2.11/0.66    spl5_33 | ~spl5_7 | ~spl5_22),
% 2.11/0.66    inference(avatar_split_clause,[],[f406,f302,f78,f416])).
% 2.11/0.66  fof(f416,plain,(
% 2.11/0.66    spl5_33 <=> u1_struct_0(sK0) = k2_xboole_0(u1_struct_0(sK0),sK3)),
% 2.11/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).
% 2.11/0.66  fof(f302,plain,(
% 2.11/0.66    spl5_22 <=> u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK3)),
% 2.11/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 2.11/0.66  fof(f406,plain,(
% 2.11/0.66    u1_struct_0(sK0) = k2_xboole_0(u1_struct_0(sK0),sK3) | (~spl5_7 | ~spl5_22)),
% 2.11/0.66    inference(forward_demodulation,[],[f399,f304])).
% 2.11/0.66  fof(f304,plain,(
% 2.11/0.66    u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK3) | ~spl5_22),
% 2.11/0.66    inference(avatar_component_clause,[],[f302])).
% 2.11/0.66  fof(f399,plain,(
% 2.11/0.66    k2_xboole_0(u1_struct_0(sK0),sK3) = k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK3) | ~spl5_7),
% 2.11/0.66    inference(resolution,[],[f387,f248])).
% 2.11/0.66  fof(f248,plain,(
% 2.11/0.66    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK0)) | k4_subset_1(u1_struct_0(sK0),X0,sK3) = k2_xboole_0(X0,sK3)) ) | ~spl5_7),
% 2.11/0.66    inference(resolution,[],[f209,f35])).
% 2.11/0.66  fof(f209,plain,(
% 2.11/0.66    ( ! [X4] : (~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),X4,sK3) = k2_xboole_0(X4,sK3)) ) | ~spl5_7),
% 2.11/0.66    inference(resolution,[],[f37,f80])).
% 2.11/0.66  fof(f405,plain,(
% 2.11/0.66    spl5_26),
% 2.11/0.66    inference(avatar_contradiction_clause,[],[f397])).
% 2.11/0.66  fof(f397,plain,(
% 2.11/0.66    $false | spl5_26),
% 2.11/0.66    inference(unit_resulting_resolution,[],[f347,f387])).
% 2.11/0.66  fof(f347,plain,(
% 2.11/0.66    ~r1_tarski(sK2,sK2) | spl5_26),
% 2.11/0.66    inference(avatar_component_clause,[],[f345])).
% 2.11/0.66  fof(f345,plain,(
% 2.11/0.66    spl5_26 <=> r1_tarski(sK2,sK2)),
% 2.11/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).
% 2.11/0.66  fof(f404,plain,(
% 2.11/0.66    spl5_26),
% 2.11/0.66    inference(avatar_contradiction_clause,[],[f401])).
% 2.11/0.66  fof(f401,plain,(
% 2.11/0.66    $false | spl5_26),
% 2.11/0.66    inference(resolution,[],[f387,f347])).
% 2.11/0.66  fof(f403,plain,(
% 2.11/0.66    spl5_32),
% 2.11/0.66    inference(avatar_contradiction_clause,[],[f402])).
% 2.11/0.66  fof(f402,plain,(
% 2.11/0.66    $false | spl5_32),
% 2.11/0.66    inference(resolution,[],[f387,f385])).
% 2.11/0.66  fof(f385,plain,(
% 2.11/0.66    ~r1_tarski(sK3,sK3) | spl5_32),
% 2.11/0.66    inference(avatar_component_clause,[],[f383])).
% 2.11/0.66  fof(f383,plain,(
% 2.11/0.66    spl5_32 <=> r1_tarski(sK3,sK3)),
% 2.11/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).
% 2.11/0.66  fof(f386,plain,(
% 2.11/0.66    spl5_31 | ~spl5_32 | ~spl5_3 | ~spl5_7),
% 2.11/0.66    inference(avatar_split_clause,[],[f351,f78,f58,f383,f379])).
% 2.11/0.66  fof(f379,plain,(
% 2.11/0.66    spl5_31 <=> r1_tarski(k1_tops_1(sK0,sK3),k1_tops_1(sK0,sK3))),
% 2.11/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).
% 2.11/0.66  fof(f351,plain,(
% 2.11/0.66    ~r1_tarski(sK3,sK3) | r1_tarski(k1_tops_1(sK0,sK3),k1_tops_1(sK0,sK3)) | (~spl5_3 | ~spl5_7)),
% 2.11/0.66    inference(resolution,[],[f247,f80])).
% 2.11/0.66  fof(f369,plain,(
% 2.11/0.66    spl5_29 | ~spl5_30 | ~spl5_3 | ~spl5_7 | ~spl5_8),
% 2.11/0.66    inference(avatar_split_clause,[],[f350,f83,f78,f58,f366,f362])).
% 2.11/0.66  fof(f362,plain,(
% 2.11/0.66    spl5_29 <=> r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK3))),
% 2.11/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).
% 2.11/0.66  fof(f366,plain,(
% 2.11/0.66    spl5_30 <=> r1_tarski(sK2,sK3)),
% 2.11/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).
% 2.11/0.66  fof(f350,plain,(
% 2.11/0.66    ~r1_tarski(sK2,sK3) | r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK3)) | (~spl5_3 | ~spl5_7 | ~spl5_8)),
% 2.11/0.66    inference(resolution,[],[f247,f85])).
% 2.11/0.66  fof(f360,plain,(
% 2.11/0.66    spl5_27 | ~spl5_28 | ~spl5_3 | ~spl5_7 | ~spl5_8),
% 2.11/0.66    inference(avatar_split_clause,[],[f333,f83,f78,f58,f357,f353])).
% 2.11/0.66  fof(f353,plain,(
% 2.11/0.66    spl5_27 <=> r1_tarski(k1_tops_1(sK0,sK3),k1_tops_1(sK0,sK2))),
% 2.11/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).
% 2.11/0.66  fof(f357,plain,(
% 2.11/0.66    spl5_28 <=> r1_tarski(sK3,sK2)),
% 2.11/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).
% 2.11/0.66  fof(f333,plain,(
% 2.11/0.66    ~r1_tarski(sK3,sK2) | r1_tarski(k1_tops_1(sK0,sK3),k1_tops_1(sK0,sK2)) | (~spl5_3 | ~spl5_7 | ~spl5_8)),
% 2.11/0.66    inference(resolution,[],[f246,f80])).
% 2.11/0.66  fof(f348,plain,(
% 2.11/0.66    spl5_25 | ~spl5_26 | ~spl5_3 | ~spl5_8),
% 2.11/0.66    inference(avatar_split_clause,[],[f332,f83,f58,f345,f341])).
% 2.11/0.66  fof(f341,plain,(
% 2.11/0.66    spl5_25 <=> r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK2))),
% 2.11/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).
% 2.11/0.66  fof(f332,plain,(
% 2.11/0.66    ~r1_tarski(sK2,sK2) | r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK2)) | (~spl5_3 | ~spl5_8)),
% 2.11/0.66    inference(resolution,[],[f246,f85])).
% 2.11/0.66  fof(f338,plain,(
% 2.11/0.66    spl5_24 | spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_5 | ~spl5_6 | ~spl5_7),
% 2.11/0.66    inference(avatar_split_clause,[],[f330,f78,f73,f68,f58,f53,f48,f335])).
% 2.11/0.66  fof(f68,plain,(
% 2.11/0.66    spl5_5 <=> m1_connsp_2(sK3,sK0,sK1)),
% 2.11/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 2.11/0.66  fof(f330,plain,(
% 2.11/0.66    r2_hidden(sK1,k1_tops_1(sK0,sK3)) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_5 | ~spl5_6 | ~spl5_7)),
% 2.11/0.66    inference(subsumption_resolution,[],[f329,f75])).
% 2.11/0.66  fof(f329,plain,(
% 2.11/0.66    r2_hidden(sK1,k1_tops_1(sK0,sK3)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_5 | ~spl5_7)),
% 2.11/0.66    inference(resolution,[],[f320,f70])).
% 2.11/0.66  fof(f70,plain,(
% 2.11/0.66    m1_connsp_2(sK3,sK0,sK1) | ~spl5_5),
% 2.11/0.66    inference(avatar_component_clause,[],[f68])).
% 2.11/0.66  fof(f320,plain,(
% 2.11/0.66    ( ! [X4] : (~m1_connsp_2(sK3,sK0,X4) | r2_hidden(X4,k1_tops_1(sK0,sK3)) | ~m1_subset_1(X4,u1_struct_0(sK0))) ) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_7)),
% 2.11/0.66    inference(subsumption_resolution,[],[f319,f50])).
% 2.11/0.66  fof(f319,plain,(
% 2.11/0.66    ( ! [X4] : (~m1_subset_1(X4,u1_struct_0(sK0)) | v2_struct_0(sK0) | r2_hidden(X4,k1_tops_1(sK0,sK3)) | ~m1_connsp_2(sK3,sK0,X4)) ) | (~spl5_2 | ~spl5_3 | ~spl5_7)),
% 2.11/0.66    inference(subsumption_resolution,[],[f318,f60])).
% 2.11/0.66  fof(f318,plain,(
% 2.11/0.66    ( ! [X4] : (~l1_pre_topc(sK0) | ~m1_subset_1(X4,u1_struct_0(sK0)) | v2_struct_0(sK0) | r2_hidden(X4,k1_tops_1(sK0,sK3)) | ~m1_connsp_2(sK3,sK0,X4)) ) | (~spl5_2 | ~spl5_7)),
% 2.11/0.66    inference(subsumption_resolution,[],[f314,f55])).
% 2.11/0.66  fof(f314,plain,(
% 2.11/0.66    ( ! [X4] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X4,u1_struct_0(sK0)) | v2_struct_0(sK0) | r2_hidden(X4,k1_tops_1(sK0,sK3)) | ~m1_connsp_2(sK3,sK0,X4)) ) | ~spl5_7),
% 2.11/0.66    inference(resolution,[],[f31,f80])).
% 2.11/0.66  fof(f327,plain,(
% 2.11/0.66    spl5_23 | spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_6 | ~spl5_8),
% 2.11/0.66    inference(avatar_split_clause,[],[f322,f83,f73,f63,f58,f53,f48,f324])).
% 2.11/0.66  fof(f63,plain,(
% 2.11/0.66    spl5_4 <=> m1_connsp_2(sK2,sK0,sK1)),
% 2.11/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 2.11/0.66  fof(f322,plain,(
% 2.11/0.66    r2_hidden(sK1,k1_tops_1(sK0,sK2)) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_6 | ~spl5_8)),
% 2.11/0.66    inference(subsumption_resolution,[],[f321,f75])).
% 2.11/0.66  fof(f321,plain,(
% 2.11/0.66    r2_hidden(sK1,k1_tops_1(sK0,sK2)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_8)),
% 2.11/0.66    inference(resolution,[],[f317,f65])).
% 2.11/0.66  fof(f65,plain,(
% 2.11/0.66    m1_connsp_2(sK2,sK0,sK1) | ~spl5_4),
% 2.11/0.66    inference(avatar_component_clause,[],[f63])).
% 2.11/0.66  fof(f317,plain,(
% 2.11/0.66    ( ! [X3] : (~m1_connsp_2(sK2,sK0,X3) | r2_hidden(X3,k1_tops_1(sK0,sK2)) | ~m1_subset_1(X3,u1_struct_0(sK0))) ) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_8)),
% 2.11/0.66    inference(subsumption_resolution,[],[f316,f50])).
% 2.11/0.66  fof(f316,plain,(
% 2.11/0.66    ( ! [X3] : (~m1_subset_1(X3,u1_struct_0(sK0)) | v2_struct_0(sK0) | r2_hidden(X3,k1_tops_1(sK0,sK2)) | ~m1_connsp_2(sK2,sK0,X3)) ) | (~spl5_2 | ~spl5_3 | ~spl5_8)),
% 2.11/0.66    inference(subsumption_resolution,[],[f315,f60])).
% 2.11/0.66  fof(f315,plain,(
% 2.11/0.66    ( ! [X3] : (~l1_pre_topc(sK0) | ~m1_subset_1(X3,u1_struct_0(sK0)) | v2_struct_0(sK0) | r2_hidden(X3,k1_tops_1(sK0,sK2)) | ~m1_connsp_2(sK2,sK0,X3)) ) | (~spl5_2 | ~spl5_8)),
% 2.11/0.66    inference(subsumption_resolution,[],[f313,f55])).
% 2.11/0.66  fof(f313,plain,(
% 2.11/0.66    ( ! [X3] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X3,u1_struct_0(sK0)) | v2_struct_0(sK0) | r2_hidden(X3,k1_tops_1(sK0,sK2)) | ~m1_connsp_2(sK2,sK0,X3)) ) | ~spl5_8),
% 2.11/0.66    inference(resolution,[],[f31,f85])).
% 2.11/0.66  fof(f305,plain,(
% 2.11/0.66    spl5_22 | ~spl5_7 | ~spl5_13 | ~spl5_14),
% 2.11/0.66    inference(avatar_split_clause,[],[f291,f129,f119,f78,f302])).
% 2.11/0.66  fof(f291,plain,(
% 2.11/0.66    u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK3) | (~spl5_7 | ~spl5_13 | ~spl5_14)),
% 2.11/0.66    inference(forward_demodulation,[],[f290,f121])).
% 2.11/0.66  fof(f290,plain,(
% 2.11/0.66    k2_xboole_0(sK3,u1_struct_0(sK0)) = k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK3) | (~spl5_7 | ~spl5_14)),
% 2.11/0.66    inference(forward_demodulation,[],[f289,f33])).
% 2.11/0.66  fof(f289,plain,(
% 2.11/0.66    k2_xboole_0(u1_struct_0(sK0),sK3) = k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK3) | (~spl5_7 | ~spl5_14)),
% 2.11/0.66    inference(resolution,[],[f248,f131])).
% 2.11/0.66  fof(f286,plain,(
% 2.11/0.66    ~spl5_21 | spl5_9 | ~spl5_19),
% 2.11/0.66    inference(avatar_split_clause,[],[f261,f252,f88,f283])).
% 2.11/0.66  fof(f88,plain,(
% 2.11/0.66    spl5_9 <=> m1_connsp_2(k4_subset_1(u1_struct_0(sK0),sK2,sK3),sK0,sK1)),
% 2.11/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 2.11/0.66  fof(f252,plain,(
% 2.11/0.66    spl5_19 <=> k4_subset_1(u1_struct_0(sK0),sK2,sK3) = k2_xboole_0(sK2,sK3)),
% 2.11/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 2.11/0.66  fof(f261,plain,(
% 2.11/0.66    ~m1_connsp_2(k2_xboole_0(sK2,sK3),sK0,sK1) | (spl5_9 | ~spl5_19)),
% 2.11/0.66    inference(superposition,[],[f90,f254])).
% 2.11/0.66  fof(f254,plain,(
% 2.11/0.66    k4_subset_1(u1_struct_0(sK0),sK2,sK3) = k2_xboole_0(sK2,sK3) | ~spl5_19),
% 2.11/0.66    inference(avatar_component_clause,[],[f252])).
% 2.11/0.66  fof(f90,plain,(
% 2.11/0.66    ~m1_connsp_2(k4_subset_1(u1_struct_0(sK0),sK2,sK3),sK0,sK1) | spl5_9),
% 2.11/0.66    inference(avatar_component_clause,[],[f88])).
% 2.11/0.66  fof(f260,plain,(
% 2.11/0.66    spl5_20 | ~spl5_7),
% 2.11/0.66    inference(avatar_split_clause,[],[f250,f78,f257])).
% 2.11/0.66  fof(f257,plain,(
% 2.11/0.66    spl5_20 <=> k4_subset_1(u1_struct_0(sK0),sK3,sK3) = k2_xboole_0(sK3,sK3)),
% 2.11/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 2.11/0.66  fof(f250,plain,(
% 2.11/0.66    k4_subset_1(u1_struct_0(sK0),sK3,sK3) = k2_xboole_0(sK3,sK3) | ~spl5_7),
% 2.11/0.66    inference(resolution,[],[f209,f80])).
% 2.11/0.66  fof(f255,plain,(
% 2.11/0.66    spl5_19 | ~spl5_7 | ~spl5_8),
% 2.11/0.66    inference(avatar_split_clause,[],[f249,f83,f78,f252])).
% 2.11/0.66  fof(f249,plain,(
% 2.11/0.66    k4_subset_1(u1_struct_0(sK0),sK2,sK3) = k2_xboole_0(sK2,sK3) | (~spl5_7 | ~spl5_8)),
% 2.11/0.66    inference(resolution,[],[f209,f85])).
% 2.11/0.66  fof(f242,plain,(
% 2.11/0.66    spl5_18 | ~spl5_8 | ~spl5_12 | ~spl5_14),
% 2.11/0.66    inference(avatar_split_clause,[],[f237,f129,f114,f83,f239])).
% 2.11/0.66  fof(f237,plain,(
% 2.11/0.66    u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) | (~spl5_8 | ~spl5_12 | ~spl5_14)),
% 2.11/0.66    inference(forward_demodulation,[],[f236,f116])).
% 2.11/0.66  fof(f236,plain,(
% 2.11/0.66    k2_xboole_0(sK2,u1_struct_0(sK0)) = k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) | (~spl5_8 | ~spl5_14)),
% 2.11/0.66    inference(forward_demodulation,[],[f234,f33])).
% 2.11/0.66  fof(f234,plain,(
% 2.11/0.66    k2_xboole_0(u1_struct_0(sK0),sK2) = k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) | (~spl5_8 | ~spl5_14)),
% 2.11/0.66    inference(resolution,[],[f214,f131])).
% 2.11/0.66  fof(f227,plain,(
% 2.11/0.66    spl5_17 | ~spl5_7 | ~spl5_8),
% 2.11/0.66    inference(avatar_split_clause,[],[f217,f83,f78,f224])).
% 2.11/0.66  fof(f224,plain,(
% 2.11/0.66    spl5_17 <=> k4_subset_1(u1_struct_0(sK0),sK3,sK2) = k2_xboole_0(sK2,sK3)),
% 2.11/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 2.11/0.66  fof(f217,plain,(
% 2.11/0.66    k4_subset_1(u1_struct_0(sK0),sK3,sK2) = k2_xboole_0(sK2,sK3) | (~spl5_7 | ~spl5_8)),
% 2.11/0.66    inference(forward_demodulation,[],[f216,f33])).
% 2.11/0.66  fof(f216,plain,(
% 2.11/0.66    k4_subset_1(u1_struct_0(sK0),sK3,sK2) = k2_xboole_0(sK3,sK2) | (~spl5_7 | ~spl5_8)),
% 2.11/0.66    inference(resolution,[],[f208,f80])).
% 2.11/0.66  fof(f222,plain,(
% 2.11/0.66    spl5_16 | ~spl5_8),
% 2.11/0.66    inference(avatar_split_clause,[],[f215,f83,f219])).
% 2.11/0.66  fof(f219,plain,(
% 2.11/0.66    spl5_16 <=> k4_subset_1(u1_struct_0(sK0),sK2,sK2) = k2_xboole_0(sK2,sK2)),
% 2.11/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 2.11/0.66  fof(f215,plain,(
% 2.11/0.66    k4_subset_1(u1_struct_0(sK0),sK2,sK2) = k2_xboole_0(sK2,sK2) | ~spl5_8),
% 2.11/0.66    inference(resolution,[],[f208,f85])).
% 2.11/0.66  fof(f141,plain,(
% 2.11/0.66    spl5_15 | ~spl5_14),
% 2.11/0.66    inference(avatar_split_clause,[],[f133,f129,f138])).
% 2.11/0.66  fof(f133,plain,(
% 2.11/0.66    u1_struct_0(sK0) = k2_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0)) | ~spl5_14),
% 2.11/0.66    inference(resolution,[],[f131,f34])).
% 2.11/0.66  fof(f132,plain,(
% 2.11/0.66    spl5_14 | ~spl5_12),
% 2.11/0.66    inference(avatar_split_clause,[],[f123,f114,f129])).
% 2.11/0.66  fof(f123,plain,(
% 2.11/0.66    r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0)) | ~spl5_12),
% 2.11/0.66    inference(superposition,[],[f92,f116])).
% 2.11/0.66  fof(f122,plain,(
% 2.11/0.66    spl5_13 | ~spl5_11),
% 2.11/0.66    inference(avatar_split_clause,[],[f112,f105,f119])).
% 2.11/0.66  fof(f112,plain,(
% 2.11/0.66    u1_struct_0(sK0) = k2_xboole_0(sK3,u1_struct_0(sK0)) | ~spl5_11),
% 2.11/0.66    inference(resolution,[],[f107,f34])).
% 2.11/0.66  fof(f117,plain,(
% 2.11/0.66    spl5_12 | ~spl5_10),
% 2.11/0.66    inference(avatar_split_clause,[],[f111,f100,f114])).
% 2.11/0.66  fof(f111,plain,(
% 2.11/0.66    u1_struct_0(sK0) = k2_xboole_0(sK2,u1_struct_0(sK0)) | ~spl5_10),
% 2.11/0.66    inference(resolution,[],[f34,f102])).
% 2.11/0.66  fof(f108,plain,(
% 2.11/0.66    spl5_11 | ~spl5_7),
% 2.11/0.66    inference(avatar_split_clause,[],[f98,f78,f105])).
% 2.11/0.66  fof(f98,plain,(
% 2.11/0.66    r1_tarski(sK3,u1_struct_0(sK0)) | ~spl5_7),
% 2.11/0.66    inference(resolution,[],[f36,f80])).
% 2.11/0.66  fof(f36,plain,(
% 2.11/0.66    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 2.11/0.66    inference(cnf_transformation,[],[f6])).
% 2.11/0.66  fof(f103,plain,(
% 2.11/0.66    spl5_10 | ~spl5_8),
% 2.11/0.66    inference(avatar_split_clause,[],[f97,f83,f100])).
% 2.11/0.66  fof(f97,plain,(
% 2.11/0.66    r1_tarski(sK2,u1_struct_0(sK0)) | ~spl5_8),
% 2.11/0.66    inference(resolution,[],[f36,f85])).
% 2.11/0.66  fof(f91,plain,(
% 2.11/0.66    ~spl5_9),
% 2.11/0.66    inference(avatar_split_clause,[],[f23,f88])).
% 2.11/0.66  fof(f23,plain,(
% 2.11/0.66    ~m1_connsp_2(k4_subset_1(u1_struct_0(sK0),sK2,sK3),sK0,sK1)),
% 2.11/0.66    inference(cnf_transformation,[],[f12])).
% 2.11/0.66  fof(f12,plain,(
% 2.11/0.66    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1) & m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.11/0.66    inference(flattening,[],[f11])).
% 2.11/0.66  fof(f11,plain,(
% 2.11/0.66    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1) & (m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.11/0.66    inference(ennf_transformation,[],[f10])).
% 2.11/0.66  fof(f10,negated_conjecture,(
% 2.11/0.66    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ((m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1)) => m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1))))))),
% 2.11/0.66    inference(negated_conjecture,[],[f9])).
% 2.11/0.66  fof(f9,conjecture,(
% 2.11/0.66    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ((m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1)) => m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1))))))),
% 2.11/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_connsp_2)).
% 2.11/0.66  fof(f86,plain,(
% 2.11/0.66    spl5_8),
% 2.11/0.66    inference(avatar_split_clause,[],[f24,f83])).
% 2.11/0.66  fof(f24,plain,(
% 2.11/0.66    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.11/0.66    inference(cnf_transformation,[],[f12])).
% 2.11/0.66  fof(f81,plain,(
% 2.11/0.66    spl5_7),
% 2.11/0.66    inference(avatar_split_clause,[],[f20,f78])).
% 2.11/0.66  fof(f20,plain,(
% 2.11/0.66    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.11/0.66    inference(cnf_transformation,[],[f12])).
% 2.11/0.66  fof(f76,plain,(
% 2.11/0.66    spl5_6),
% 2.11/0.66    inference(avatar_split_clause,[],[f25,f73])).
% 2.11/0.66  fof(f25,plain,(
% 2.11/0.66    m1_subset_1(sK1,u1_struct_0(sK0))),
% 2.11/0.66    inference(cnf_transformation,[],[f12])).
% 2.11/0.66  fof(f71,plain,(
% 2.11/0.66    spl5_5),
% 2.11/0.66    inference(avatar_split_clause,[],[f22,f68])).
% 2.11/0.66  fof(f22,plain,(
% 2.11/0.66    m1_connsp_2(sK3,sK0,sK1)),
% 2.11/0.66    inference(cnf_transformation,[],[f12])).
% 2.11/0.66  fof(f66,plain,(
% 2.11/0.66    spl5_4),
% 2.11/0.66    inference(avatar_split_clause,[],[f21,f63])).
% 2.11/0.66  fof(f21,plain,(
% 2.11/0.66    m1_connsp_2(sK2,sK0,sK1)),
% 2.11/0.66    inference(cnf_transformation,[],[f12])).
% 2.11/0.66  fof(f61,plain,(
% 2.11/0.66    spl5_3),
% 2.11/0.66    inference(avatar_split_clause,[],[f28,f58])).
% 2.11/0.66  fof(f28,plain,(
% 2.11/0.66    l1_pre_topc(sK0)),
% 2.11/0.66    inference(cnf_transformation,[],[f12])).
% 2.11/0.66  fof(f56,plain,(
% 2.11/0.66    spl5_2),
% 2.11/0.66    inference(avatar_split_clause,[],[f27,f53])).
% 2.11/0.66  fof(f27,plain,(
% 2.11/0.66    v2_pre_topc(sK0)),
% 2.11/0.66    inference(cnf_transformation,[],[f12])).
% 2.11/0.66  fof(f51,plain,(
% 2.11/0.66    ~spl5_1),
% 2.11/0.66    inference(avatar_split_clause,[],[f26,f48])).
% 2.11/0.66  fof(f26,plain,(
% 2.11/0.66    ~v2_struct_0(sK0)),
% 2.11/0.66    inference(cnf_transformation,[],[f12])).
% 2.11/0.66  % SZS output end Proof for theBenchmark
% 2.11/0.66  % (4879)------------------------------
% 2.11/0.66  % (4879)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.11/0.66  % (4879)Termination reason: Refutation
% 2.11/0.66  
% 2.11/0.66  % (4879)Memory used [KB]: 8187
% 2.11/0.66  % (4879)Time elapsed: 0.251 s
% 2.11/0.66  % (4879)------------------------------
% 2.11/0.66  % (4879)------------------------------
% 2.11/0.67  % (4870)Success in time 0.304 s
%------------------------------------------------------------------------------
