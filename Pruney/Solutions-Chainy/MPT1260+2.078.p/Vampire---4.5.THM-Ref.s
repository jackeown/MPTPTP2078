%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:46 EST 2020

% Result     : Theorem 2.95s
% Output     : Refutation 2.95s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 269 expanded)
%              Number of leaves         :   23 (  97 expanded)
%              Depth                    :   14
%              Number of atoms          :  508 (1262 expanded)
%              Number of equality atoms :   88 ( 233 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f960,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f78,f79,f84,f89,f94,f101,f108,f113,f122,f146,f553,f556,f563,f573,f905,f947,f959])).

fof(f959,plain,
    ( spl4_1
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_7
    | ~ spl4_20 ),
    inference(avatar_contradiction_clause,[],[f958])).

fof(f958,plain,
    ( $false
    | spl4_1
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_7
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f957,f73])).

fof(f73,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl4_1
  <=> v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f957,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_7
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f956,f83])).

fof(f83,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl4_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f956,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(sK1,sK0)
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_7
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f955,f88])).

fof(f88,plain,
    ( l1_pre_topc(sK0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl4_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f955,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(sK1,sK0)
    | ~ spl4_5
    | ~ spl4_7
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f953,f93])).

fof(f93,plain,
    ( v2_pre_topc(sK0)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl4_5
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f953,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(sK1,sK0)
    | ~ spl4_7
    | ~ spl4_20 ),
    inference(trivial_inequality_removal,[],[f952])).

fof(f952,plain,
    ( sK1 != sK1
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(sK1,sK0)
    | ~ spl4_7
    | ~ spl4_20 ),
    inference(superposition,[],[f100,f552])).

fof(f552,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f550])).

fof(f550,plain,
    ( spl4_20
  <=> sK1 = k1_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f100,plain,
    ( ! [X2,X0] :
        ( k1_tops_1(X0,X2) != X2
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | v3_pre_topc(X2,X0) )
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl4_7
  <=> ! [X0,X2] :
        ( v3_pre_topc(X2,X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | k1_tops_1(X0,X2) != X2 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f947,plain,
    ( spl4_20
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_25 ),
    inference(avatar_split_clause,[],[f946,f902,f86,f81,f550])).

fof(f902,plain,
    ( spl4_25
  <=> sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f946,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_25 ),
    inference(subsumption_resolution,[],[f945,f88])).

fof(f945,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl4_3
    | ~ spl4_25 ),
    inference(subsumption_resolution,[],[f928,f83])).

fof(f928,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_25 ),
    inference(superposition,[],[f188,f904])).

fof(f904,plain,
    ( sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f902])).

fof(f188,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f187])).

fof(f187,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(superposition,[],[f55,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f905,plain,
    ( spl4_25
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f900,f136,f902])).

fof(f136,plain,
    ( spl4_11
  <=> k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f900,plain,
    ( sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl4_11 ),
    inference(duplicate_literal_removal,[],[f891])).

fof(f891,plain,
    ( sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl4_11 ),
    inference(resolution,[],[f787,f175])).

fof(f175,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1,X0),X0)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(factoring,[],[f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X2)
      | r2_hidden(sK3(X0,X1,X2),X0)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK3(X0,X1,X2),X1)
            | ~ r2_hidden(sK3(X0,X1,X2),X0)
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
              & r2_hidden(sK3(X0,X1,X2),X0) )
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f35,f36])).

fof(f36,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK3(X0,X1,X2),X1)
          | ~ r2_hidden(sK3(X0,X1,X2),X0)
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
            & r2_hidden(sK3(X0,X1,X2),X0) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f787,plain,
    ( ! [X23] :
        ( ~ r2_hidden(sK3(X23,k2_tops_1(sK0,sK1),X23),sK1)
        | k4_xboole_0(X23,k2_tops_1(sK0,sK1)) = X23 )
    | ~ spl4_11 ),
    inference(resolution,[],[f241,f575])).

fof(f575,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k2_tops_1(sK0,sK1))
        | ~ r2_hidden(X1,sK1) )
    | ~ spl4_11 ),
    inference(superposition,[],[f68,f138])).

fof(f138,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f136])).

fof(f68,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f241,plain,(
    ! [X2,X1] :
      ( r2_hidden(sK3(X1,X2,X1),X2)
      | k4_xboole_0(X1,X2) = X1 ) ),
    inference(subsumption_resolution,[],[f239,f52])).

fof(f239,plain,(
    ! [X2,X1] :
      ( k4_xboole_0(X1,X2) = X1
      | r2_hidden(sK3(X1,X2,X1),X2)
      | ~ r2_hidden(sK3(X1,X2,X1),X1) ) ),
    inference(duplicate_literal_removal,[],[f231])).

fof(f231,plain,(
    ! [X2,X1] :
      ( k4_xboole_0(X1,X2) = X1
      | r2_hidden(sK3(X1,X2,X1),X2)
      | ~ r2_hidden(sK3(X1,X2,X1),X1)
      | k4_xboole_0(X1,X2) = X1 ) ),
    inference(resolution,[],[f175,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1,X2),X2)
      | r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X0)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f573,plain,
    ( spl4_11
    | ~ spl4_2
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f572,f132,f75,f136])).

fof(f75,plain,
    ( spl4_2
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f132,plain,
    ( spl4_10
  <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f572,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl4_2
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f569,f133])).

fof(f133,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f132])).

fof(f569,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_2 ),
    inference(superposition,[],[f55,f76])).

fof(f76,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f75])).

fof(f563,plain,
    ( spl4_11
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f562,f550,f86,f81,f136])).

fof(f562,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f561,f88])).

fof(f561,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl4_3
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f557,f83])).

fof(f557,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_20 ),
    inference(superposition,[],[f195,f552])).

fof(f195,plain,(
    ! [X2,X3] :
      ( k2_tops_1(X2,X3) = k4_xboole_0(k2_pre_topc(X2,X3),k1_tops_1(X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2) ) ),
    inference(subsumption_resolution,[],[f193,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f193,plain,(
    ! [X2,X3] :
      ( k2_tops_1(X2,X3) = k4_xboole_0(k2_pre_topc(X2,X3),k1_tops_1(X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(k2_pre_topc(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) ) ),
    inference(superposition,[],[f59,f55])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

fof(f556,plain,
    ( ~ spl4_11
    | spl4_2
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f555,f132,f75,f136])).

fof(f555,plain,
    ( k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | spl4_2
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f554,f133])).

fof(f554,plain,
    ( k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_2 ),
    inference(superposition,[],[f77,f55])).

fof(f77,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f75])).

fof(f553,plain,
    ( ~ spl4_1
    | spl4_20
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f548,f106,f86,f81,f550,f71])).

fof(f106,plain,
    ( spl4_9
  <=> ! [X1,X3] :
        ( k1_tops_1(X1,X3) = X3
        | ~ l1_pre_topc(X1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ v3_pre_topc(X3,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f548,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ v3_pre_topc(sK1,sK0)
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f147,f88])).

fof(f147,plain,
    ( ~ l1_pre_topc(sK0)
    | sK1 = k1_tops_1(sK0,sK1)
    | ~ v3_pre_topc(sK1,sK0)
    | ~ spl4_3
    | ~ spl4_9 ),
    inference(resolution,[],[f107,f83])).

fof(f107,plain,
    ( ! [X3,X1] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ l1_pre_topc(X1)
        | k1_tops_1(X1,X3) = X3
        | ~ v3_pre_topc(X3,X1) )
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f106])).

fof(f146,plain,
    ( ~ spl4_3
    | ~ spl4_4
    | spl4_10 ),
    inference(avatar_contradiction_clause,[],[f145])).

fof(f145,plain,
    ( $false
    | ~ spl4_3
    | ~ spl4_4
    | spl4_10 ),
    inference(subsumption_resolution,[],[f144,f88])).

fof(f144,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl4_3
    | spl4_10 ),
    inference(subsumption_resolution,[],[f142,f83])).

fof(f142,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl4_10 ),
    inference(resolution,[],[f61,f134])).

fof(f134,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_10 ),
    inference(avatar_component_clause,[],[f132])).

fof(f122,plain,
    ( ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_8 ),
    inference(avatar_contradiction_clause,[],[f121])).

fof(f121,plain,
    ( $false
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f120,f88])).

fof(f120,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f118,f93])).

fof(f118,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl4_3
    | ~ spl4_8 ),
    inference(resolution,[],[f104,f83])).

fof(f104,plain,
    ( ! [X2,X0] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl4_8
  <=> ! [X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f113,plain,
    ( ~ spl4_3
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(avatar_contradiction_clause,[],[f112])).

fof(f112,plain,
    ( $false
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f110,f88])).

fof(f110,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl4_3
    | ~ spl4_6 ),
    inference(resolution,[],[f97,f83])).

fof(f97,plain,
    ( ! [X3,X1] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ l1_pre_topc(X1) )
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl4_6
  <=> ! [X1,X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ l1_pre_topc(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f108,plain,
    ( spl4_8
    | spl4_9 ),
    inference(avatar_split_clause,[],[f57,f106,f103])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_tops_1(X1,X3) = X3
      | ~ v3_pre_topc(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v3_pre_topc(X2,X0)
                      | k1_tops_1(X0,X2) != X2 )
                    & ( k1_tops_1(X1,X3) = X3
                      | ~ v3_pre_topc(X3,X1) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v3_pre_topc(X2,X0)
                      | k1_tops_1(X0,X2) != X2 )
                    & ( k1_tops_1(X1,X3) = X3
                      | ~ v3_pre_topc(X3,X1) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( k1_tops_1(X0,X2) = X2
                     => v3_pre_topc(X2,X0) )
                    & ( v3_pre_topc(X3,X1)
                     => k1_tops_1(X1,X3) = X3 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tops_1)).

fof(f101,plain,
    ( spl4_6
    | spl4_7 ),
    inference(avatar_split_clause,[],[f58,f99,f96])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( v3_pre_topc(X2,X0)
      | k1_tops_1(X0,X2) != X2
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f94,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f38,f91])).

fof(f38,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
      | ~ v3_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
      | v3_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f26,f25])).

fof(f25,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
              | ~ v3_pre_topc(X1,X0) )
            & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
              | v3_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ( k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
            | ~ v3_pre_topc(X1,sK0) )
          & ( k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
            | v3_pre_topc(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X1] :
        ( ( k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
          | ~ v3_pre_topc(X1,sK0) )
        & ( k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
          | v3_pre_topc(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
        | ~ v3_pre_topc(sK1,sK0) )
      & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
        | v3_pre_topc(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_1)).

fof(f89,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f39,f86])).

fof(f39,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f84,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f40,f81])).

fof(f40,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f27])).

fof(f79,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f41,f75,f71])).

fof(f41,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f78,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f42,f75,f71])).

fof(f42,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:57:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.47  % (1947)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.48  % (1936)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.52  % (1933)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.54  % (1951)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.54  % (1931)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.54  % (1943)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.54  % (1929)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.55  % (1930)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.55  % (1935)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.55  % (1954)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.55  % (1953)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.55  % (1951)Refutation not found, incomplete strategy% (1951)------------------------------
% 0.22/0.55  % (1951)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (1951)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (1951)Memory used [KB]: 10746
% 0.22/0.55  % (1951)Time elapsed: 0.088 s
% 0.22/0.55  % (1951)------------------------------
% 0.22/0.55  % (1951)------------------------------
% 0.22/0.55  % (1955)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.55  % (1939)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.55  % (1934)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.55  % (1932)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.55  % (1958)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.55  % (1957)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.56  % (1956)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.56  % (1950)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.56  % (1950)Refutation not found, incomplete strategy% (1950)------------------------------
% 0.22/0.56  % (1950)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (1950)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (1950)Memory used [KB]: 1791
% 0.22/0.56  % (1950)Time elapsed: 0.142 s
% 0.22/0.56  % (1950)------------------------------
% 0.22/0.56  % (1950)------------------------------
% 0.22/0.56  % (1941)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.56  % (1946)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.56  % (1949)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.56  % (1945)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.56  % (1942)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.56  % (1948)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.56  % (1940)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.56  % (1946)Refutation not found, incomplete strategy% (1946)------------------------------
% 0.22/0.56  % (1946)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (1938)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.57  % (1952)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.49/0.57  % (1937)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.49/0.58  % (1946)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.58  
% 1.49/0.58  % (1946)Memory used [KB]: 10618
% 1.49/0.58  % (1946)Time elapsed: 0.148 s
% 1.49/0.58  % (1946)------------------------------
% 1.49/0.58  % (1946)------------------------------
% 1.49/0.58  % (1944)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.71/0.59  % (1949)Refutation not found, incomplete strategy% (1949)------------------------------
% 1.71/0.59  % (1949)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.71/0.59  % (1944)Refutation not found, incomplete strategy% (1944)------------------------------
% 1.71/0.59  % (1944)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.71/0.59  % (1944)Termination reason: Refutation not found, incomplete strategy
% 1.71/0.59  
% 1.71/0.59  % (1944)Memory used [KB]: 6140
% 1.71/0.59  % (1944)Time elapsed: 0.004 s
% 1.71/0.59  % (1944)------------------------------
% 1.71/0.59  % (1944)------------------------------
% 1.71/0.61  % (1949)Termination reason: Refutation not found, incomplete strategy
% 1.71/0.61  
% 1.71/0.61  % (1949)Memory used [KB]: 11129
% 1.71/0.61  % (1949)Time elapsed: 0.172 s
% 1.71/0.61  % (1949)------------------------------
% 1.71/0.61  % (1949)------------------------------
% 2.12/0.68  % (1960)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.57/0.72  % (1961)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.57/0.72  % (1959)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.57/0.74  % (1962)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.57/0.75  % (1963)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 2.95/0.79  % (1961)Refutation found. Thanks to Tanya!
% 2.95/0.79  % SZS status Theorem for theBenchmark
% 2.95/0.80  % SZS output start Proof for theBenchmark
% 2.95/0.80  fof(f960,plain,(
% 2.95/0.80    $false),
% 2.95/0.80    inference(avatar_sat_refutation,[],[f78,f79,f84,f89,f94,f101,f108,f113,f122,f146,f553,f556,f563,f573,f905,f947,f959])).
% 2.95/0.80  fof(f959,plain,(
% 2.95/0.80    spl4_1 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_7 | ~spl4_20),
% 2.95/0.80    inference(avatar_contradiction_clause,[],[f958])).
% 2.95/0.80  fof(f958,plain,(
% 2.95/0.80    $false | (spl4_1 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_7 | ~spl4_20)),
% 2.95/0.80    inference(subsumption_resolution,[],[f957,f73])).
% 2.95/0.80  fof(f73,plain,(
% 2.95/0.80    ~v3_pre_topc(sK1,sK0) | spl4_1),
% 2.95/0.80    inference(avatar_component_clause,[],[f71])).
% 2.95/0.80  fof(f71,plain,(
% 2.95/0.80    spl4_1 <=> v3_pre_topc(sK1,sK0)),
% 2.95/0.80    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 2.95/0.80  fof(f957,plain,(
% 2.95/0.80    v3_pre_topc(sK1,sK0) | (~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_7 | ~spl4_20)),
% 2.95/0.80    inference(subsumption_resolution,[],[f956,f83])).
% 2.95/0.80  fof(f83,plain,(
% 2.95/0.80    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_3),
% 2.95/0.80    inference(avatar_component_clause,[],[f81])).
% 2.95/0.80  fof(f81,plain,(
% 2.95/0.80    spl4_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.95/0.80    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 2.95/0.80  fof(f956,plain,(
% 2.95/0.80    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(sK1,sK0) | (~spl4_4 | ~spl4_5 | ~spl4_7 | ~spl4_20)),
% 2.95/0.80    inference(subsumption_resolution,[],[f955,f88])).
% 2.95/0.80  fof(f88,plain,(
% 2.95/0.80    l1_pre_topc(sK0) | ~spl4_4),
% 2.95/0.80    inference(avatar_component_clause,[],[f86])).
% 2.95/0.80  fof(f86,plain,(
% 2.95/0.80    spl4_4 <=> l1_pre_topc(sK0)),
% 2.95/0.80    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 2.95/0.80  fof(f955,plain,(
% 2.95/0.80    ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(sK1,sK0) | (~spl4_5 | ~spl4_7 | ~spl4_20)),
% 2.95/0.80    inference(subsumption_resolution,[],[f953,f93])).
% 2.95/0.80  fof(f93,plain,(
% 2.95/0.80    v2_pre_topc(sK0) | ~spl4_5),
% 2.95/0.80    inference(avatar_component_clause,[],[f91])).
% 2.95/0.80  fof(f91,plain,(
% 2.95/0.80    spl4_5 <=> v2_pre_topc(sK0)),
% 2.95/0.80    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 2.95/0.80  fof(f953,plain,(
% 2.95/0.80    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(sK1,sK0) | (~spl4_7 | ~spl4_20)),
% 2.95/0.80    inference(trivial_inequality_removal,[],[f952])).
% 2.95/0.80  fof(f952,plain,(
% 2.95/0.80    sK1 != sK1 | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(sK1,sK0) | (~spl4_7 | ~spl4_20)),
% 2.95/0.80    inference(superposition,[],[f100,f552])).
% 2.95/0.80  fof(f552,plain,(
% 2.95/0.80    sK1 = k1_tops_1(sK0,sK1) | ~spl4_20),
% 2.95/0.80    inference(avatar_component_clause,[],[f550])).
% 2.95/0.80  fof(f550,plain,(
% 2.95/0.80    spl4_20 <=> sK1 = k1_tops_1(sK0,sK1)),
% 2.95/0.80    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 2.95/0.80  fof(f100,plain,(
% 2.95/0.80    ( ! [X2,X0] : (k1_tops_1(X0,X2) != X2 | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(X2,X0)) ) | ~spl4_7),
% 2.95/0.80    inference(avatar_component_clause,[],[f99])).
% 2.95/0.80  fof(f99,plain,(
% 2.95/0.80    spl4_7 <=> ! [X0,X2] : (v3_pre_topc(X2,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,X2) != X2)),
% 2.95/0.80    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 2.95/0.80  fof(f947,plain,(
% 2.95/0.80    spl4_20 | ~spl4_3 | ~spl4_4 | ~spl4_25),
% 2.95/0.80    inference(avatar_split_clause,[],[f946,f902,f86,f81,f550])).
% 2.95/0.80  fof(f902,plain,(
% 2.95/0.80    spl4_25 <=> sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 2.95/0.80    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 2.95/0.80  fof(f946,plain,(
% 2.95/0.80    sK1 = k1_tops_1(sK0,sK1) | (~spl4_3 | ~spl4_4 | ~spl4_25)),
% 2.95/0.80    inference(subsumption_resolution,[],[f945,f88])).
% 2.95/0.80  fof(f945,plain,(
% 2.95/0.80    sK1 = k1_tops_1(sK0,sK1) | ~l1_pre_topc(sK0) | (~spl4_3 | ~spl4_25)),
% 2.95/0.80    inference(subsumption_resolution,[],[f928,f83])).
% 2.95/0.80  fof(f928,plain,(
% 2.95/0.80    sK1 = k1_tops_1(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl4_25),
% 2.95/0.80    inference(superposition,[],[f188,f904])).
% 2.95/0.80  fof(f904,plain,(
% 2.95/0.80    sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl4_25),
% 2.95/0.80    inference(avatar_component_clause,[],[f902])).
% 2.95/0.80  fof(f188,plain,(
% 2.95/0.80    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.95/0.80    inference(duplicate_literal_removal,[],[f187])).
% 2.95/0.80  fof(f187,plain,(
% 2.95/0.80    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.95/0.80    inference(superposition,[],[f55,f60])).
% 2.95/0.80  fof(f60,plain,(
% 2.95/0.80    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.95/0.80    inference(cnf_transformation,[],[f20])).
% 2.95/0.80  fof(f20,plain,(
% 2.95/0.80    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.95/0.80    inference(ennf_transformation,[],[f10])).
% 2.95/0.80  fof(f10,axiom,(
% 2.95/0.80    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 2.95/0.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).
% 2.95/0.80  fof(f55,plain,(
% 2.95/0.80    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.95/0.80    inference(cnf_transformation,[],[f16])).
% 2.95/0.80  fof(f16,plain,(
% 2.95/0.80    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.95/0.80    inference(ennf_transformation,[],[f5])).
% 2.95/0.80  fof(f5,axiom,(
% 2.95/0.80    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 2.95/0.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 2.95/0.80  fof(f905,plain,(
% 2.95/0.80    spl4_25 | ~spl4_11),
% 2.95/0.80    inference(avatar_split_clause,[],[f900,f136,f902])).
% 2.95/0.80  fof(f136,plain,(
% 2.95/0.80    spl4_11 <=> k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)),
% 2.95/0.80    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 2.95/0.80  fof(f900,plain,(
% 2.95/0.80    sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl4_11),
% 2.95/0.80    inference(duplicate_literal_removal,[],[f891])).
% 2.95/0.80  fof(f891,plain,(
% 2.95/0.80    sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl4_11),
% 2.95/0.80    inference(resolution,[],[f787,f175])).
% 2.95/0.80  fof(f175,plain,(
% 2.95/0.80    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1,X0),X0) | k4_xboole_0(X0,X1) = X0) )),
% 2.95/0.80    inference(factoring,[],[f52])).
% 2.95/0.80  fof(f52,plain,(
% 2.95/0.80    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),X2) | r2_hidden(sK3(X0,X1,X2),X0) | k4_xboole_0(X0,X1) = X2) )),
% 2.95/0.80    inference(cnf_transformation,[],[f37])).
% 2.95/0.80  fof(f37,plain,(
% 2.95/0.80    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.95/0.80    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f35,f36])).
% 2.95/0.80  fof(f36,plain,(
% 2.95/0.80    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 2.95/0.80    introduced(choice_axiom,[])).
% 2.95/0.80  fof(f35,plain,(
% 2.95/0.80    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.95/0.80    inference(rectify,[],[f34])).
% 2.95/0.81  fof(f34,plain,(
% 2.95/0.81    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.95/0.81    inference(flattening,[],[f33])).
% 2.95/0.81  fof(f33,plain,(
% 2.95/0.81    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.95/0.81    inference(nnf_transformation,[],[f2])).
% 2.95/0.81  fof(f2,axiom,(
% 2.95/0.81    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.95/0.81    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 2.95/0.81  fof(f787,plain,(
% 2.95/0.81    ( ! [X23] : (~r2_hidden(sK3(X23,k2_tops_1(sK0,sK1),X23),sK1) | k4_xboole_0(X23,k2_tops_1(sK0,sK1)) = X23) ) | ~spl4_11),
% 2.95/0.81    inference(resolution,[],[f241,f575])).
% 2.95/0.81  fof(f575,plain,(
% 2.95/0.81    ( ! [X1] : (~r2_hidden(X1,k2_tops_1(sK0,sK1)) | ~r2_hidden(X1,sK1)) ) | ~spl4_11),
% 2.95/0.81    inference(superposition,[],[f68,f138])).
% 2.95/0.81  fof(f138,plain,(
% 2.95/0.81    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~spl4_11),
% 2.95/0.81    inference(avatar_component_clause,[],[f136])).
% 2.95/0.81  fof(f68,plain,(
% 2.95/0.81    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 2.95/0.81    inference(equality_resolution,[],[f50])).
% 2.95/0.81  fof(f50,plain,(
% 2.95/0.81    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.95/0.81    inference(cnf_transformation,[],[f37])).
% 2.95/0.81  fof(f241,plain,(
% 2.95/0.81    ( ! [X2,X1] : (r2_hidden(sK3(X1,X2,X1),X2) | k4_xboole_0(X1,X2) = X1) )),
% 2.95/0.81    inference(subsumption_resolution,[],[f239,f52])).
% 2.95/0.81  fof(f239,plain,(
% 2.95/0.81    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = X1 | r2_hidden(sK3(X1,X2,X1),X2) | ~r2_hidden(sK3(X1,X2,X1),X1)) )),
% 2.95/0.81    inference(duplicate_literal_removal,[],[f231])).
% 2.95/0.81  fof(f231,plain,(
% 2.95/0.81    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = X1 | r2_hidden(sK3(X1,X2,X1),X2) | ~r2_hidden(sK3(X1,X2,X1),X1) | k4_xboole_0(X1,X2) = X1) )),
% 2.95/0.81    inference(resolution,[],[f175,f54])).
% 2.95/0.81  fof(f54,plain,(
% 2.95/0.81    ( ! [X2,X0,X1] : (~r2_hidden(sK3(X0,X1,X2),X2) | r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | k4_xboole_0(X0,X1) = X2) )),
% 2.95/0.81    inference(cnf_transformation,[],[f37])).
% 2.95/0.81  fof(f573,plain,(
% 2.95/0.81    spl4_11 | ~spl4_2 | ~spl4_10),
% 2.95/0.81    inference(avatar_split_clause,[],[f572,f132,f75,f136])).
% 2.95/0.81  fof(f75,plain,(
% 2.95/0.81    spl4_2 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)),
% 2.95/0.81    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 2.95/0.81  fof(f132,plain,(
% 2.95/0.81    spl4_10 <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.95/0.81    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 2.95/0.81  fof(f572,plain,(
% 2.95/0.81    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | (~spl4_2 | ~spl4_10)),
% 2.95/0.81    inference(subsumption_resolution,[],[f569,f133])).
% 2.95/0.81  fof(f133,plain,(
% 2.95/0.81    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_10),
% 2.95/0.81    inference(avatar_component_clause,[],[f132])).
% 2.95/0.81  fof(f569,plain,(
% 2.95/0.81    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_2),
% 2.95/0.81    inference(superposition,[],[f55,f76])).
% 2.95/0.81  fof(f76,plain,(
% 2.95/0.81    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~spl4_2),
% 2.95/0.81    inference(avatar_component_clause,[],[f75])).
% 2.95/0.81  fof(f563,plain,(
% 2.95/0.81    spl4_11 | ~spl4_3 | ~spl4_4 | ~spl4_20),
% 2.95/0.81    inference(avatar_split_clause,[],[f562,f550,f86,f81,f136])).
% 2.95/0.81  fof(f562,plain,(
% 2.95/0.81    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | (~spl4_3 | ~spl4_4 | ~spl4_20)),
% 2.95/0.81    inference(subsumption_resolution,[],[f561,f88])).
% 2.95/0.81  fof(f561,plain,(
% 2.95/0.81    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~l1_pre_topc(sK0) | (~spl4_3 | ~spl4_20)),
% 2.95/0.81    inference(subsumption_resolution,[],[f557,f83])).
% 2.95/0.81  fof(f557,plain,(
% 2.95/0.81    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl4_20),
% 2.95/0.81    inference(superposition,[],[f195,f552])).
% 2.95/0.81  fof(f195,plain,(
% 2.95/0.81    ( ! [X2,X3] : (k2_tops_1(X2,X3) = k4_xboole_0(k2_pre_topc(X2,X3),k1_tops_1(X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2)) )),
% 2.95/0.81    inference(subsumption_resolution,[],[f193,f61])).
% 2.95/0.81  fof(f61,plain,(
% 2.95/0.81    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.95/0.81    inference(cnf_transformation,[],[f22])).
% 2.95/0.81  fof(f22,plain,(
% 2.95/0.81    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 2.95/0.81    inference(flattening,[],[f21])).
% 2.95/0.81  fof(f21,plain,(
% 2.95/0.81    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 2.95/0.81    inference(ennf_transformation,[],[f7])).
% 2.95/0.81  fof(f7,axiom,(
% 2.95/0.81    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.95/0.81    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 2.95/0.81  fof(f193,plain,(
% 2.95/0.81    ( ! [X2,X3] : (k2_tops_1(X2,X3) = k4_xboole_0(k2_pre_topc(X2,X3),k1_tops_1(X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2) | ~m1_subset_1(k2_pre_topc(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))) )),
% 2.95/0.81    inference(superposition,[],[f59,f55])).
% 2.95/0.81  fof(f59,plain,(
% 2.95/0.81    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.95/0.81    inference(cnf_transformation,[],[f19])).
% 2.95/0.81  fof(f19,plain,(
% 2.95/0.81    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.95/0.81    inference(ennf_transformation,[],[f8])).
% 2.95/0.81  fof(f8,axiom,(
% 2.95/0.81    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 2.95/0.81    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).
% 2.95/0.81  fof(f556,plain,(
% 2.95/0.81    ~spl4_11 | spl4_2 | ~spl4_10),
% 2.95/0.81    inference(avatar_split_clause,[],[f555,f132,f75,f136])).
% 2.95/0.81  fof(f555,plain,(
% 2.95/0.81    k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | (spl4_2 | ~spl4_10)),
% 2.95/0.81    inference(subsumption_resolution,[],[f554,f133])).
% 2.95/0.81  fof(f554,plain,(
% 2.95/0.81    k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl4_2),
% 2.95/0.81    inference(superposition,[],[f77,f55])).
% 2.95/0.81  fof(f77,plain,(
% 2.95/0.81    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | spl4_2),
% 2.95/0.81    inference(avatar_component_clause,[],[f75])).
% 2.95/0.81  fof(f553,plain,(
% 2.95/0.81    ~spl4_1 | spl4_20 | ~spl4_3 | ~spl4_4 | ~spl4_9),
% 2.95/0.81    inference(avatar_split_clause,[],[f548,f106,f86,f81,f550,f71])).
% 2.95/0.81  fof(f106,plain,(
% 2.95/0.81    spl4_9 <=> ! [X1,X3] : (k1_tops_1(X1,X3) = X3 | ~l1_pre_topc(X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~v3_pre_topc(X3,X1))),
% 2.95/0.81    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 2.95/0.81  fof(f548,plain,(
% 2.95/0.81    sK1 = k1_tops_1(sK0,sK1) | ~v3_pre_topc(sK1,sK0) | (~spl4_3 | ~spl4_4 | ~spl4_9)),
% 2.95/0.81    inference(subsumption_resolution,[],[f147,f88])).
% 2.95/0.81  fof(f147,plain,(
% 2.95/0.81    ~l1_pre_topc(sK0) | sK1 = k1_tops_1(sK0,sK1) | ~v3_pre_topc(sK1,sK0) | (~spl4_3 | ~spl4_9)),
% 2.95/0.81    inference(resolution,[],[f107,f83])).
% 2.95/0.81  fof(f107,plain,(
% 2.95/0.81    ( ! [X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1)) ) | ~spl4_9),
% 2.95/0.81    inference(avatar_component_clause,[],[f106])).
% 2.95/0.81  fof(f146,plain,(
% 2.95/0.81    ~spl4_3 | ~spl4_4 | spl4_10),
% 2.95/0.81    inference(avatar_contradiction_clause,[],[f145])).
% 2.95/0.81  fof(f145,plain,(
% 2.95/0.81    $false | (~spl4_3 | ~spl4_4 | spl4_10)),
% 2.95/0.81    inference(subsumption_resolution,[],[f144,f88])).
% 2.95/0.81  fof(f144,plain,(
% 2.95/0.81    ~l1_pre_topc(sK0) | (~spl4_3 | spl4_10)),
% 2.95/0.81    inference(subsumption_resolution,[],[f142,f83])).
% 2.95/0.81  fof(f142,plain,(
% 2.95/0.81    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl4_10),
% 2.95/0.81    inference(resolution,[],[f61,f134])).
% 2.95/0.81  fof(f134,plain,(
% 2.95/0.81    ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl4_10),
% 2.95/0.81    inference(avatar_component_clause,[],[f132])).
% 2.95/0.81  fof(f122,plain,(
% 2.95/0.81    ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_8),
% 2.95/0.81    inference(avatar_contradiction_clause,[],[f121])).
% 2.95/0.81  fof(f121,plain,(
% 2.95/0.81    $false | (~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_8)),
% 2.95/0.81    inference(subsumption_resolution,[],[f120,f88])).
% 2.95/0.81  fof(f120,plain,(
% 2.95/0.81    ~l1_pre_topc(sK0) | (~spl4_3 | ~spl4_5 | ~spl4_8)),
% 2.95/0.81    inference(subsumption_resolution,[],[f118,f93])).
% 2.95/0.81  fof(f118,plain,(
% 2.95/0.81    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | (~spl4_3 | ~spl4_8)),
% 2.95/0.81    inference(resolution,[],[f104,f83])).
% 2.95/0.81  fof(f104,plain,(
% 2.95/0.81    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0)) ) | ~spl4_8),
% 2.95/0.81    inference(avatar_component_clause,[],[f103])).
% 2.95/0.81  fof(f103,plain,(
% 2.95/0.81    spl4_8 <=> ! [X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0))),
% 2.95/0.81    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 2.95/0.81  fof(f113,plain,(
% 2.95/0.81    ~spl4_3 | ~spl4_4 | ~spl4_6),
% 2.95/0.81    inference(avatar_contradiction_clause,[],[f112])).
% 2.95/0.81  fof(f112,plain,(
% 2.95/0.81    $false | (~spl4_3 | ~spl4_4 | ~spl4_6)),
% 2.95/0.81    inference(subsumption_resolution,[],[f110,f88])).
% 2.95/0.81  fof(f110,plain,(
% 2.95/0.81    ~l1_pre_topc(sK0) | (~spl4_3 | ~spl4_6)),
% 2.95/0.81    inference(resolution,[],[f97,f83])).
% 2.95/0.81  fof(f97,plain,(
% 2.95/0.81    ( ! [X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1)) ) | ~spl4_6),
% 2.95/0.81    inference(avatar_component_clause,[],[f96])).
% 2.95/0.81  fof(f96,plain,(
% 2.95/0.81    spl4_6 <=> ! [X1,X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1))),
% 2.95/0.81    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 2.95/0.81  fof(f108,plain,(
% 2.95/0.81    spl4_8 | spl4_9),
% 2.95/0.81    inference(avatar_split_clause,[],[f57,f106,f103])).
% 2.95/0.81  fof(f57,plain,(
% 2.95/0.81    ( ! [X2,X0,X3,X1] : (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.95/0.81    inference(cnf_transformation,[],[f18])).
% 2.95/0.81  fof(f18,plain,(
% 2.95/0.81    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.95/0.81    inference(flattening,[],[f17])).
% 2.95/0.81  fof(f17,plain,(
% 2.95/0.81    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.95/0.81    inference(ennf_transformation,[],[f9])).
% 2.95/0.81  fof(f9,axiom,(
% 2.95/0.81    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((k1_tops_1(X0,X2) = X2 => v3_pre_topc(X2,X0)) & (v3_pre_topc(X3,X1) => k1_tops_1(X1,X3) = X3))))))),
% 2.95/0.81    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tops_1)).
% 2.95/0.81  fof(f101,plain,(
% 2.95/0.81    spl4_6 | spl4_7),
% 2.95/0.81    inference(avatar_split_clause,[],[f58,f99,f96])).
% 2.95/0.81  fof(f58,plain,(
% 2.95/0.81    ( ! [X2,X0,X3,X1] : (v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.95/0.81    inference(cnf_transformation,[],[f18])).
% 2.95/0.81  fof(f94,plain,(
% 2.95/0.81    spl4_5),
% 2.95/0.81    inference(avatar_split_clause,[],[f38,f91])).
% 2.95/0.81  fof(f38,plain,(
% 2.95/0.81    v2_pre_topc(sK0)),
% 2.95/0.81    inference(cnf_transformation,[],[f27])).
% 2.95/0.81  fof(f27,plain,(
% 2.95/0.81    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 2.95/0.81    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f26,f25])).
% 2.95/0.81  fof(f25,plain,(
% 2.95/0.81    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | ~v3_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 2.95/0.81    introduced(choice_axiom,[])).
% 2.95/0.81  fof(f26,plain,(
% 2.95/0.81    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | ~v3_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.95/0.81    introduced(choice_axiom,[])).
% 2.95/0.81  fof(f24,plain,(
% 2.95/0.81    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.95/0.81    inference(flattening,[],[f23])).
% 2.95/0.81  fof(f23,plain,(
% 2.95/0.81    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.95/0.81    inference(nnf_transformation,[],[f15])).
% 2.95/0.81  fof(f15,plain,(
% 2.95/0.81    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.95/0.81    inference(flattening,[],[f14])).
% 2.95/0.81  fof(f14,plain,(
% 2.95/0.81    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 2.95/0.81    inference(ennf_transformation,[],[f12])).
% 2.95/0.81  fof(f12,negated_conjecture,(
% 2.95/0.81    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 2.95/0.81    inference(negated_conjecture,[],[f11])).
% 2.95/0.81  fof(f11,conjecture,(
% 2.95/0.81    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 2.95/0.81    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_1)).
% 2.95/0.81  fof(f89,plain,(
% 2.95/0.81    spl4_4),
% 2.95/0.81    inference(avatar_split_clause,[],[f39,f86])).
% 2.95/0.81  fof(f39,plain,(
% 2.95/0.81    l1_pre_topc(sK0)),
% 2.95/0.81    inference(cnf_transformation,[],[f27])).
% 2.95/0.81  fof(f84,plain,(
% 2.95/0.81    spl4_3),
% 2.95/0.81    inference(avatar_split_clause,[],[f40,f81])).
% 2.95/0.81  fof(f40,plain,(
% 2.95/0.81    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.95/0.81    inference(cnf_transformation,[],[f27])).
% 2.95/0.81  fof(f79,plain,(
% 2.95/0.81    spl4_1 | spl4_2),
% 2.95/0.81    inference(avatar_split_clause,[],[f41,f75,f71])).
% 2.95/0.81  fof(f41,plain,(
% 2.95/0.81    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)),
% 2.95/0.81    inference(cnf_transformation,[],[f27])).
% 2.95/0.81  fof(f78,plain,(
% 2.95/0.81    ~spl4_1 | ~spl4_2),
% 2.95/0.81    inference(avatar_split_clause,[],[f42,f75,f71])).
% 2.95/0.81  fof(f42,plain,(
% 2.95/0.81    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)),
% 2.95/0.81    inference(cnf_transformation,[],[f27])).
% 2.95/0.81  % SZS output end Proof for theBenchmark
% 2.95/0.81  % (1961)------------------------------
% 2.95/0.81  % (1961)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.95/0.81  % (1961)Termination reason: Refutation
% 2.95/0.81  
% 2.95/0.81  % (1961)Memory used [KB]: 6908
% 2.95/0.81  % (1961)Time elapsed: 0.185 s
% 2.95/0.81  % (1961)------------------------------
% 2.95/0.81  % (1961)------------------------------
% 2.95/0.81  % (1928)Success in time 0.443 s
%------------------------------------------------------------------------------
