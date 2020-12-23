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
% DateTime   : Thu Dec  3 13:15:24 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 176 expanded)
%              Number of leaves         :   20 (  63 expanded)
%              Depth                    :   11
%              Number of atoms          :  342 ( 552 expanded)
%              Number of equality atoms :   26 (  30 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f246,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f62,f67,f81,f86,f92,f108,f129,f154,f157,f164,f228,f245])).

fof(f245,plain,
    ( ~ spl5_4
    | spl5_5
    | ~ spl5_11
    | ~ spl5_16 ),
    inference(avatar_contradiction_clause,[],[f244])).

fof(f244,plain,
    ( $false
    | ~ spl5_4
    | spl5_5
    | ~ spl5_11
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f243,f80])).

fof(f80,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl5_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f243,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl5_5
    | ~ spl5_11
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f242,f85])).

fof(f85,plain,
    ( ~ m2_connsp_2(k2_struct_0(sK0),sK0,sK1)
    | spl5_5 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl5_5
  <=> m2_connsp_2(k2_struct_0(sK0),sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f242,plain,
    ( m2_connsp_2(k2_struct_0(sK0),sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_11
    | ~ spl5_16 ),
    inference(resolution,[],[f227,f153])).

fof(f153,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k2_struct_0(sK0))
        | m2_connsp_2(k2_struct_0(sK0),sK0,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f152])).

fof(f152,plain,
    ( spl5_11
  <=> ! [X0] :
        ( ~ r1_tarski(X0,k2_struct_0(sK0))
        | m2_connsp_2(k2_struct_0(sK0),sK0,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f227,plain,
    ( r1_tarski(sK1,k2_struct_0(sK0))
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f225])).

fof(f225,plain,
    ( spl5_16
  <=> r1_tarski(sK1,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f228,plain,
    ( spl5_16
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_7
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f223,f161,f105,f78,f64,f225])).

fof(f64,plain,
    ( spl5_3
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f105,plain,
    ( spl5_7
  <=> l1_pre_topc(k1_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f161,plain,
    ( spl5_12
  <=> sK1 = k2_struct_0(k1_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f223,plain,
    ( r1_tarski(sK1,k2_struct_0(sK0))
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_7
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f222,f80])).

fof(f222,plain,
    ( r1_tarski(sK1,k2_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_3
    | ~ spl5_7
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f221,f66])).

fof(f66,plain,
    ( l1_pre_topc(sK0)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f64])).

fof(f221,plain,
    ( ~ l1_pre_topc(sK0)
    | r1_tarski(sK1,k2_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_3
    | ~ spl5_7
    | ~ spl5_12 ),
    inference(resolution,[],[f175,f72])).

fof(f72,plain,
    ( ! [X1] :
        ( m1_pre_topc(k1_pre_topc(sK0,X1),sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_3 ),
    inference(resolution,[],[f66,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_pre_topc(k1_pre_topc(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
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

fof(f175,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(k1_pre_topc(sK0,sK1),X1)
        | ~ l1_pre_topc(X1)
        | r1_tarski(sK1,k2_struct_0(X1)) )
    | ~ spl5_7
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f170,f107])).

fof(f107,plain,
    ( l1_pre_topc(k1_pre_topc(sK0,sK1))
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f105])).

fof(f170,plain,
    ( ! [X1] :
        ( r1_tarski(sK1,k2_struct_0(X1))
        | ~ l1_pre_topc(k1_pre_topc(sK0,sK1))
        | ~ l1_pre_topc(X1)
        | ~ m1_pre_topc(k1_pre_topc(sK0,sK1),X1) )
    | ~ spl5_12 ),
    inference(superposition,[],[f41,f163])).

fof(f163,plain,
    ( sK1 = k2_struct_0(k1_pre_topc(sK0,sK1))
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f161])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_struct_0(X1),k2_struct_0(X0))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X1,X0)
          <=> ( ! [X2] :
                  ( ( r2_hidden(X2,u1_pre_topc(X1))
                  <=> ? [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                        & r2_hidden(X3,u1_pre_topc(X0))
                        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
              & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X1,X0)
          <=> ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( r2_hidden(X2,u1_pre_topc(X1))
                  <=> ? [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                        & r2_hidden(X3,u1_pre_topc(X0))
                        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) )
              & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_pre_topc)).

fof(f164,plain,
    ( spl5_12
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f142,f78,f64,f161])).

fof(f142,plain,
    ( sK1 = k2_struct_0(k1_pre_topc(sK0,sK1))
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(resolution,[],[f140,f80])).

fof(f140,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_struct_0(k1_pre_topc(sK0,X0)) = X0 )
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f96,f72])).

fof(f96,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_pre_topc(k1_pre_topc(sK0,X0),sK0)
        | k2_struct_0(k1_pre_topc(sK0,X0)) = X0 )
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f95,f66])).

fof(f95,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ m1_pre_topc(k1_pre_topc(sK0,X0),sK0)
        | k2_struct_0(k1_pre_topc(sK0,X0)) = X0 )
    | ~ spl5_3 ),
    inference(duplicate_literal_removal,[],[f93])).

fof(f93,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ m1_pre_topc(k1_pre_topc(sK0,X0),sK0)
        | k2_struct_0(k1_pre_topc(sK0,X0)) = X0 )
    | ~ spl5_3 ),
    inference(resolution,[],[f71,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ v1_pre_topc(k1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | k2_struct_0(k1_pre_topc(X0,X1)) = X1 ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_pre_topc(X2)
      | ~ m1_pre_topc(X2,X0)
      | k2_struct_0(X2) = X1
      | k1_pre_topc(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & v1_pre_topc(X2) )
             => ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_pre_topc)).

fof(f71,plain,
    ( ! [X0] :
        ( v1_pre_topc(k1_pre_topc(sK0,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_3 ),
    inference(resolution,[],[f66,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_pre_topc(k1_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f157,plain,
    ( ~ spl5_8
    | spl5_10 ),
    inference(avatar_contradiction_clause,[],[f156])).

fof(f156,plain,
    ( $false
    | ~ spl5_8
    | spl5_10 ),
    inference(subsumption_resolution,[],[f155,f119])).

fof(f119,plain,
    ( l1_struct_0(sK0)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl5_8
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f155,plain,
    ( ~ l1_struct_0(sK0)
    | spl5_10 ),
    inference(resolution,[],[f150,f30])).

fof(f30,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_struct_0)).

fof(f150,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl5_10 ),
    inference(avatar_component_clause,[],[f148])).

fof(f148,plain,
    ( spl5_10
  <=> m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f154,plain,
    ( ~ spl5_10
    | spl5_11
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f130,f89,f64,f59,f152,f148])).

fof(f59,plain,
    ( spl5_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f89,plain,
    ( spl5_6
  <=> k2_struct_0(sK0) = k1_tops_1(sK0,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f130,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k2_struct_0(sK0))
        | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | m2_connsp_2(k2_struct_0(sK0),sK0,X0) )
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_6 ),
    inference(superposition,[],[f126,f91])).

fof(f91,plain,
    ( k2_struct_0(sK0) = k1_tops_1(sK0,k2_struct_0(sK0))
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f89])).

fof(f126,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,k1_tops_1(sK0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | m2_connsp_2(X1,sK0,X0) )
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f68,f66])).

fof(f68,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X0,k1_tops_1(sK0,X1))
        | m2_connsp_2(X1,sK0,X0) )
    | ~ spl5_2 ),
    inference(resolution,[],[f61,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X1,k1_tops_1(X0,X2))
      | m2_connsp_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m2_connsp_2(X2,X0,X1)
              <=> r1_tarski(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m2_connsp_2(X2,X0,X1)
              <=> r1_tarski(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m2_connsp_2(X2,X0,X1)
              <=> r1_tarski(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_connsp_2)).

fof(f61,plain,
    ( v2_pre_topc(sK0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f59])).

fof(f129,plain,
    ( ~ spl5_3
    | spl5_8 ),
    inference(avatar_contradiction_clause,[],[f128])).

fof(f128,plain,
    ( $false
    | ~ spl5_3
    | spl5_8 ),
    inference(subsumption_resolution,[],[f127,f66])).

fof(f127,plain,
    ( ~ l1_pre_topc(sK0)
    | spl5_8 ),
    inference(resolution,[],[f120,f31])).

fof(f31,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f120,plain,
    ( ~ l1_struct_0(sK0)
    | spl5_8 ),
    inference(avatar_component_clause,[],[f118])).

fof(f108,plain,
    ( spl5_7
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f99,f78,f64,f105])).

fof(f99,plain,
    ( l1_pre_topc(k1_pre_topc(sK0,sK1))
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(resolution,[],[f97,f80])).

fof(f97,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | l1_pre_topc(k1_pre_topc(sK0,X0)) )
    | ~ spl5_3 ),
    inference(resolution,[],[f72,f73])).

fof(f73,plain,
    ( ! [X2] :
        ( ~ m1_pre_topc(X2,sK0)
        | l1_pre_topc(X2) )
    | ~ spl5_3 ),
    inference(resolution,[],[f66,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f92,plain,
    ( spl5_6
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f87,f64,f59,f89])).

fof(f87,plain,
    ( k2_struct_0(sK0) = k1_tops_1(sK0,k2_struct_0(sK0))
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f70,f66])).

fof(f70,plain,
    ( ~ l1_pre_topc(sK0)
    | k2_struct_0(sK0) = k1_tops_1(sK0,k2_struct_0(sK0))
    | ~ spl5_2 ),
    inference(resolution,[],[f61,f45])).

fof(f45,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tops_1)).

fof(f86,plain,(
    ~ spl5_5 ),
    inference(avatar_split_clause,[],[f26,f83])).

fof(f26,plain,(
    ~ m2_connsp_2(k2_struct_0(sK0),sK0,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ m2_connsp_2(k2_struct_0(X0),X0,X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ m2_connsp_2(k2_struct_0(X0),X0,X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
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
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => m2_connsp_2(k2_struct_0(X0),X0,X1) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => m2_connsp_2(k2_struct_0(X0),X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_connsp_2)).

fof(f81,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f25,f78])).

fof(f25,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f12])).

fof(f67,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f29,f64])).

fof(f29,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f62,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f28,f59])).

fof(f28,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:03:02 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.47  % (30123)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.47  % (30123)Refutation not found, incomplete strategy% (30123)------------------------------
% 0.20/0.47  % (30123)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (30116)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.47  % (30131)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.47  % (30123)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (30123)Memory used [KB]: 6140
% 0.20/0.47  % (30123)Time elapsed: 0.061 s
% 0.20/0.47  % (30123)------------------------------
% 0.20/0.47  % (30123)------------------------------
% 0.20/0.47  % (30116)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f246,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(avatar_sat_refutation,[],[f62,f67,f81,f86,f92,f108,f129,f154,f157,f164,f228,f245])).
% 0.20/0.47  fof(f245,plain,(
% 0.20/0.47    ~spl5_4 | spl5_5 | ~spl5_11 | ~spl5_16),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f244])).
% 0.20/0.47  fof(f244,plain,(
% 0.20/0.47    $false | (~spl5_4 | spl5_5 | ~spl5_11 | ~spl5_16)),
% 0.20/0.47    inference(subsumption_resolution,[],[f243,f80])).
% 0.20/0.47  fof(f80,plain,(
% 0.20/0.47    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_4),
% 0.20/0.47    inference(avatar_component_clause,[],[f78])).
% 0.20/0.47  fof(f78,plain,(
% 0.20/0.47    spl5_4 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.20/0.47  fof(f243,plain,(
% 0.20/0.47    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (spl5_5 | ~spl5_11 | ~spl5_16)),
% 0.20/0.47    inference(subsumption_resolution,[],[f242,f85])).
% 0.20/0.47  fof(f85,plain,(
% 0.20/0.47    ~m2_connsp_2(k2_struct_0(sK0),sK0,sK1) | spl5_5),
% 0.20/0.47    inference(avatar_component_clause,[],[f83])).
% 0.20/0.47  fof(f83,plain,(
% 0.20/0.47    spl5_5 <=> m2_connsp_2(k2_struct_0(sK0),sK0,sK1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.20/0.47  fof(f242,plain,(
% 0.20/0.47    m2_connsp_2(k2_struct_0(sK0),sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl5_11 | ~spl5_16)),
% 0.20/0.47    inference(resolution,[],[f227,f153])).
% 0.20/0.47  fof(f153,plain,(
% 0.20/0.47    ( ! [X0] : (~r1_tarski(X0,k2_struct_0(sK0)) | m2_connsp_2(k2_struct_0(sK0),sK0,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl5_11),
% 0.20/0.47    inference(avatar_component_clause,[],[f152])).
% 0.20/0.47  fof(f152,plain,(
% 0.20/0.47    spl5_11 <=> ! [X0] : (~r1_tarski(X0,k2_struct_0(sK0)) | m2_connsp_2(k2_struct_0(sK0),sK0,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.20/0.47  fof(f227,plain,(
% 0.20/0.47    r1_tarski(sK1,k2_struct_0(sK0)) | ~spl5_16),
% 0.20/0.47    inference(avatar_component_clause,[],[f225])).
% 0.20/0.47  fof(f225,plain,(
% 0.20/0.47    spl5_16 <=> r1_tarski(sK1,k2_struct_0(sK0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.20/0.47  fof(f228,plain,(
% 0.20/0.47    spl5_16 | ~spl5_3 | ~spl5_4 | ~spl5_7 | ~spl5_12),
% 0.20/0.47    inference(avatar_split_clause,[],[f223,f161,f105,f78,f64,f225])).
% 0.20/0.47  fof(f64,plain,(
% 0.20/0.47    spl5_3 <=> l1_pre_topc(sK0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.20/0.47  fof(f105,plain,(
% 0.20/0.47    spl5_7 <=> l1_pre_topc(k1_pre_topc(sK0,sK1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.20/0.47  fof(f161,plain,(
% 0.20/0.47    spl5_12 <=> sK1 = k2_struct_0(k1_pre_topc(sK0,sK1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.20/0.47  fof(f223,plain,(
% 0.20/0.47    r1_tarski(sK1,k2_struct_0(sK0)) | (~spl5_3 | ~spl5_4 | ~spl5_7 | ~spl5_12)),
% 0.20/0.47    inference(subsumption_resolution,[],[f222,f80])).
% 0.20/0.47  fof(f222,plain,(
% 0.20/0.47    r1_tarski(sK1,k2_struct_0(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl5_3 | ~spl5_7 | ~spl5_12)),
% 0.20/0.47    inference(subsumption_resolution,[],[f221,f66])).
% 0.20/0.47  fof(f66,plain,(
% 0.20/0.47    l1_pre_topc(sK0) | ~spl5_3),
% 0.20/0.47    inference(avatar_component_clause,[],[f64])).
% 0.20/0.47  fof(f221,plain,(
% 0.20/0.47    ~l1_pre_topc(sK0) | r1_tarski(sK1,k2_struct_0(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl5_3 | ~spl5_7 | ~spl5_12)),
% 0.20/0.47    inference(resolution,[],[f175,f72])).
% 0.20/0.47  fof(f72,plain,(
% 0.20/0.47    ( ! [X1] : (m1_pre_topc(k1_pre_topc(sK0,X1),sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl5_3),
% 0.20/0.47    inference(resolution,[],[f66,f49])).
% 0.20/0.47  fof(f49,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_pre_topc(k1_pre_topc(X0,X1),X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f24])).
% 0.20/0.47  fof(f24,plain,(
% 0.20/0.47    ! [X0,X1] : ((m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.20/0.47    inference(flattening,[],[f23])).
% 0.20/0.47  fof(f23,plain,(
% 0.20/0.47    ! [X0,X1] : ((m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f3])).
% 0.20/0.47  fof(f3,axiom,(
% 0.20/0.47    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => (m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_pre_topc)).
% 0.20/0.47  fof(f175,plain,(
% 0.20/0.47    ( ! [X1] : (~m1_pre_topc(k1_pre_topc(sK0,sK1),X1) | ~l1_pre_topc(X1) | r1_tarski(sK1,k2_struct_0(X1))) ) | (~spl5_7 | ~spl5_12)),
% 0.20/0.47    inference(subsumption_resolution,[],[f170,f107])).
% 0.20/0.47  fof(f107,plain,(
% 0.20/0.47    l1_pre_topc(k1_pre_topc(sK0,sK1)) | ~spl5_7),
% 0.20/0.47    inference(avatar_component_clause,[],[f105])).
% 0.20/0.47  fof(f170,plain,(
% 0.20/0.47    ( ! [X1] : (r1_tarski(sK1,k2_struct_0(X1)) | ~l1_pre_topc(k1_pre_topc(sK0,sK1)) | ~l1_pre_topc(X1) | ~m1_pre_topc(k1_pre_topc(sK0,sK1),X1)) ) | ~spl5_12),
% 0.20/0.47    inference(superposition,[],[f41,f163])).
% 0.20/0.47  fof(f163,plain,(
% 0.20/0.47    sK1 = k2_struct_0(k1_pre_topc(sK0,sK1)) | ~spl5_12),
% 0.20/0.47    inference(avatar_component_clause,[],[f161])).
% 0.20/0.47  fof(f41,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f15])).
% 0.20/0.47  fof(f15,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : ((m1_pre_topc(X1,X0) <=> (! [X2] : ((r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f2])).
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => (r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))))))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_pre_topc)).
% 0.20/0.47  fof(f164,plain,(
% 0.20/0.47    spl5_12 | ~spl5_3 | ~spl5_4),
% 0.20/0.47    inference(avatar_split_clause,[],[f142,f78,f64,f161])).
% 0.20/0.47  fof(f142,plain,(
% 0.20/0.47    sK1 = k2_struct_0(k1_pre_topc(sK0,sK1)) | (~spl5_3 | ~spl5_4)),
% 0.20/0.47    inference(resolution,[],[f140,f80])).
% 0.20/0.47  fof(f140,plain,(
% 0.20/0.47    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_struct_0(k1_pre_topc(sK0,X0)) = X0) ) | ~spl5_3),
% 0.20/0.47    inference(subsumption_resolution,[],[f96,f72])).
% 0.20/0.47  fof(f96,plain,(
% 0.20/0.47    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_pre_topc(k1_pre_topc(sK0,X0),sK0) | k2_struct_0(k1_pre_topc(sK0,X0)) = X0) ) | ~spl5_3),
% 0.20/0.47    inference(subsumption_resolution,[],[f95,f66])).
% 0.20/0.47  fof(f95,plain,(
% 0.20/0.47    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~m1_pre_topc(k1_pre_topc(sK0,X0),sK0) | k2_struct_0(k1_pre_topc(sK0,X0)) = X0) ) | ~spl5_3),
% 0.20/0.47    inference(duplicate_literal_removal,[],[f93])).
% 0.20/0.47  fof(f93,plain,(
% 0.20/0.47    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~m1_pre_topc(k1_pre_topc(sK0,X0),sK0) | k2_struct_0(k1_pre_topc(sK0,X0)) = X0) ) | ~spl5_3),
% 0.20/0.47    inference(resolution,[],[f71,f51])).
% 0.20/0.47  fof(f51,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~v1_pre_topc(k1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~m1_pre_topc(k1_pre_topc(X0,X1),X0) | k2_struct_0(k1_pre_topc(X0,X1)) = X1) )),
% 0.20/0.47    inference(equality_resolution,[],[f44])).
% 0.20/0.47  fof(f44,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_pre_topc(X2) | ~m1_pre_topc(X2,X0) | k2_struct_0(X2) = X1 | k1_pre_topc(X0,X1) != X2) )),
% 0.20/0.47    inference(cnf_transformation,[],[f18])).
% 0.20/0.47  fof(f18,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (! [X2] : ((k1_pre_topc(X0,X1) = X2 <=> k2_struct_0(X2) = X1) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.47    inference(flattening,[],[f17])).
% 0.20/0.47  fof(f17,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (! [X2] : ((k1_pre_topc(X0,X1) = X2 <=> k2_struct_0(X2) = X1) | (~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f1])).
% 0.20/0.47  fof(f1,axiom,(
% 0.20/0.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : ((m1_pre_topc(X2,X0) & v1_pre_topc(X2)) => (k1_pre_topc(X0,X1) = X2 <=> k2_struct_0(X2) = X1))))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_pre_topc)).
% 0.20/0.47  fof(f71,plain,(
% 0.20/0.47    ( ! [X0] : (v1_pre_topc(k1_pre_topc(sK0,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl5_3),
% 0.20/0.47    inference(resolution,[],[f66,f48])).
% 0.20/0.47  fof(f48,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_pre_topc(k1_pre_topc(X0,X1))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f24])).
% 0.20/0.47  fof(f157,plain,(
% 0.20/0.47    ~spl5_8 | spl5_10),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f156])).
% 0.20/0.47  fof(f156,plain,(
% 0.20/0.47    $false | (~spl5_8 | spl5_10)),
% 0.20/0.47    inference(subsumption_resolution,[],[f155,f119])).
% 0.20/0.47  fof(f119,plain,(
% 0.20/0.47    l1_struct_0(sK0) | ~spl5_8),
% 0.20/0.47    inference(avatar_component_clause,[],[f118])).
% 0.20/0.47  fof(f118,plain,(
% 0.20/0.47    spl5_8 <=> l1_struct_0(sK0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.20/0.47  fof(f155,plain,(
% 0.20/0.47    ~l1_struct_0(sK0) | spl5_10),
% 0.20/0.47    inference(resolution,[],[f150,f30])).
% 0.20/0.47  fof(f30,plain,(
% 0.20/0.47    ( ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f13])).
% 0.20/0.47  fof(f13,plain,(
% 0.20/0.47    ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f4])).
% 0.20/0.47  fof(f4,axiom,(
% 0.20/0.47    ! [X0] : (l1_struct_0(X0) => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_struct_0)).
% 0.20/0.47  fof(f150,plain,(
% 0.20/0.47    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | spl5_10),
% 0.20/0.47    inference(avatar_component_clause,[],[f148])).
% 0.20/0.47  fof(f148,plain,(
% 0.20/0.47    spl5_10 <=> m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.20/0.47  fof(f154,plain,(
% 0.20/0.47    ~spl5_10 | spl5_11 | ~spl5_2 | ~spl5_3 | ~spl5_6),
% 0.20/0.47    inference(avatar_split_clause,[],[f130,f89,f64,f59,f152,f148])).
% 0.20/0.47  fof(f59,plain,(
% 0.20/0.47    spl5_2 <=> v2_pre_topc(sK0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.20/0.47  fof(f89,plain,(
% 0.20/0.47    spl5_6 <=> k2_struct_0(sK0) = k1_tops_1(sK0,k2_struct_0(sK0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.20/0.47  fof(f130,plain,(
% 0.20/0.47    ( ! [X0] : (~r1_tarski(X0,k2_struct_0(sK0)) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | m2_connsp_2(k2_struct_0(sK0),sK0,X0)) ) | (~spl5_2 | ~spl5_3 | ~spl5_6)),
% 0.20/0.47    inference(superposition,[],[f126,f91])).
% 0.20/0.47  fof(f91,plain,(
% 0.20/0.47    k2_struct_0(sK0) = k1_tops_1(sK0,k2_struct_0(sK0)) | ~spl5_6),
% 0.20/0.47    inference(avatar_component_clause,[],[f89])).
% 0.20/0.47  fof(f126,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r1_tarski(X0,k1_tops_1(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | m2_connsp_2(X1,sK0,X0)) ) | (~spl5_2 | ~spl5_3)),
% 0.20/0.47    inference(subsumption_resolution,[],[f68,f66])).
% 0.20/0.47  fof(f68,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~l1_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,k1_tops_1(sK0,X1)) | m2_connsp_2(X1,sK0,X0)) ) | ~spl5_2),
% 0.20/0.47    inference(resolution,[],[f61,f46])).
% 0.20/0.47  fof(f46,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X1,k1_tops_1(X0,X2)) | m2_connsp_2(X2,X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f22])).
% 0.20/0.47  fof(f22,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (! [X2] : ((m2_connsp_2(X2,X0,X1) <=> r1_tarski(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.47    inference(flattening,[],[f21])).
% 0.20/0.47  fof(f21,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (! [X2] : ((m2_connsp_2(X2,X0,X1) <=> r1_tarski(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f8])).
% 0.20/0.47  fof(f8,axiom,(
% 0.20/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m2_connsp_2(X2,X0,X1) <=> r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_connsp_2)).
% 0.20/0.47  fof(f61,plain,(
% 0.20/0.47    v2_pre_topc(sK0) | ~spl5_2),
% 0.20/0.47    inference(avatar_component_clause,[],[f59])).
% 0.20/0.47  fof(f129,plain,(
% 0.20/0.47    ~spl5_3 | spl5_8),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f128])).
% 0.20/0.47  fof(f128,plain,(
% 0.20/0.47    $false | (~spl5_3 | spl5_8)),
% 0.20/0.47    inference(subsumption_resolution,[],[f127,f66])).
% 0.20/0.47  fof(f127,plain,(
% 0.20/0.47    ~l1_pre_topc(sK0) | spl5_8),
% 0.20/0.47    inference(resolution,[],[f120,f31])).
% 0.20/0.47  fof(f31,plain,(
% 0.20/0.47    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f14])).
% 0.20/0.47  fof(f14,plain,(
% 0.20/0.47    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f5])).
% 0.20/0.47  fof(f5,axiom,(
% 0.20/0.47    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.20/0.47  fof(f120,plain,(
% 0.20/0.47    ~l1_struct_0(sK0) | spl5_8),
% 0.20/0.47    inference(avatar_component_clause,[],[f118])).
% 0.20/0.47  fof(f108,plain,(
% 0.20/0.47    spl5_7 | ~spl5_3 | ~spl5_4),
% 0.20/0.47    inference(avatar_split_clause,[],[f99,f78,f64,f105])).
% 0.20/0.47  fof(f99,plain,(
% 0.20/0.47    l1_pre_topc(k1_pre_topc(sK0,sK1)) | (~spl5_3 | ~spl5_4)),
% 0.20/0.47    inference(resolution,[],[f97,f80])).
% 0.20/0.47  fof(f97,plain,(
% 0.20/0.47    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | l1_pre_topc(k1_pre_topc(sK0,X0))) ) | ~spl5_3),
% 0.20/0.47    inference(resolution,[],[f72,f73])).
% 0.20/0.47  fof(f73,plain,(
% 0.20/0.47    ( ! [X2] : (~m1_pre_topc(X2,sK0) | l1_pre_topc(X2)) ) | ~spl5_3),
% 0.20/0.47    inference(resolution,[],[f66,f42])).
% 0.20/0.47  fof(f42,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f16])).
% 0.20/0.47  fof(f16,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f6])).
% 0.20/0.47  fof(f6,axiom,(
% 0.20/0.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.20/0.47  fof(f92,plain,(
% 0.20/0.47    spl5_6 | ~spl5_2 | ~spl5_3),
% 0.20/0.47    inference(avatar_split_clause,[],[f87,f64,f59,f89])).
% 0.20/0.47  fof(f87,plain,(
% 0.20/0.47    k2_struct_0(sK0) = k1_tops_1(sK0,k2_struct_0(sK0)) | (~spl5_2 | ~spl5_3)),
% 0.20/0.47    inference(subsumption_resolution,[],[f70,f66])).
% 0.20/0.47  fof(f70,plain,(
% 0.20/0.47    ~l1_pre_topc(sK0) | k2_struct_0(sK0) = k1_tops_1(sK0,k2_struct_0(sK0)) | ~spl5_2),
% 0.20/0.47    inference(resolution,[],[f61,f45])).
% 0.20/0.47  fof(f45,plain,(
% 0.20/0.47    ( ! [X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f20])).
% 0.20/0.47  fof(f20,plain,(
% 0.20/0.47    ! [X0] : (k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.47    inference(flattening,[],[f19])).
% 0.20/0.47  fof(f19,plain,(
% 0.20/0.47    ! [X0] : (k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f7])).
% 0.20/0.47  fof(f7,axiom,(
% 0.20/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tops_1)).
% 0.20/0.47  fof(f86,plain,(
% 0.20/0.47    ~spl5_5),
% 0.20/0.47    inference(avatar_split_clause,[],[f26,f83])).
% 0.20/0.47  fof(f26,plain,(
% 0.20/0.47    ~m2_connsp_2(k2_struct_0(sK0),sK0,sK1)),
% 0.20/0.47    inference(cnf_transformation,[],[f12])).
% 0.20/0.47  fof(f12,plain,(
% 0.20/0.47    ? [X0] : (? [X1] : (~m2_connsp_2(k2_struct_0(X0),X0,X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.47    inference(flattening,[],[f11])).
% 0.20/0.47  fof(f11,plain,(
% 0.20/0.47    ? [X0] : (? [X1] : (~m2_connsp_2(k2_struct_0(X0),X0,X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f10])).
% 0.20/0.47  fof(f10,negated_conjecture,(
% 0.20/0.47    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => m2_connsp_2(k2_struct_0(X0),X0,X1)))),
% 0.20/0.47    inference(negated_conjecture,[],[f9])).
% 0.20/0.47  fof(f9,conjecture,(
% 0.20/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => m2_connsp_2(k2_struct_0(X0),X0,X1)))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_connsp_2)).
% 0.20/0.47  fof(f81,plain,(
% 0.20/0.47    spl5_4),
% 0.20/0.47    inference(avatar_split_clause,[],[f25,f78])).
% 0.20/0.47  fof(f25,plain,(
% 0.20/0.47    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.47    inference(cnf_transformation,[],[f12])).
% 0.20/0.47  fof(f67,plain,(
% 0.20/0.47    spl5_3),
% 0.20/0.47    inference(avatar_split_clause,[],[f29,f64])).
% 0.20/0.47  fof(f29,plain,(
% 0.20/0.47    l1_pre_topc(sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f12])).
% 0.20/0.47  fof(f62,plain,(
% 0.20/0.47    spl5_2),
% 0.20/0.47    inference(avatar_split_clause,[],[f28,f59])).
% 0.20/0.47  fof(f28,plain,(
% 0.20/0.47    v2_pre_topc(sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f12])).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (30116)------------------------------
% 0.20/0.47  % (30116)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (30116)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (30116)Memory used [KB]: 10746
% 0.20/0.47  % (30116)Time elapsed: 0.064 s
% 0.20/0.47  % (30116)------------------------------
% 0.20/0.47  % (30116)------------------------------
% 0.20/0.48  % (30112)Success in time 0.121 s
%------------------------------------------------------------------------------
