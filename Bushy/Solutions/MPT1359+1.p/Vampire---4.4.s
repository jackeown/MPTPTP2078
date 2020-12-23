%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : compts_1__t14_compts_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:35:49 EDT 2019

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  184 ( 461 expanded)
%              Number of leaves         :   27 ( 131 expanded)
%              Depth                    :   20
%              Number of atoms          :  907 (3257 expanded)
%              Number of equality atoms :  180 ( 853 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2086,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f103,f110,f117,f124,f128,f132,f136,f140,f144,f148,f205,f236,f245,f285,f300,f1116,f1160,f2085])).

fof(f2085,plain,
    ( spl8_1
    | ~ spl8_18
    | spl8_29
    | ~ spl8_30
    | ~ spl8_32
    | ~ spl8_34
    | ~ spl8_48
    | ~ spl8_168 ),
    inference(avatar_contradiction_clause,[],[f2084])).

fof(f2084,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_18
    | ~ spl8_29
    | ~ spl8_30
    | ~ spl8_32
    | ~ spl8_34
    | ~ spl8_48
    | ~ spl8_168 ),
    inference(subsumption_resolution,[],[f2083,f96])).

fof(f96,plain,
    ( ~ v1_compts_1(sK0)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl8_1
  <=> ~ v1_compts_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f2083,plain,
    ( v1_compts_1(sK0)
    | ~ spl8_1
    | ~ spl8_18
    | ~ spl8_29
    | ~ spl8_30
    | ~ spl8_32
    | ~ spl8_34
    | ~ spl8_48
    | ~ spl8_168 ),
    inference(subsumption_resolution,[],[f2082,f58])).

fof(f58,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ? [X0] :
      ( ( v1_compts_1(X0)
      <~> ! [X1] :
            ( ? [X2] :
                ( k1_xboole_0 = k6_setfam_1(u1_struct_0(X0),X2)
                & v1_finset_1(X2)
                & r1_tarski(X2,X1)
                & k1_xboole_0 != X2
                & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            | k1_xboole_0 != k6_setfam_1(u1_struct_0(X0),X1)
            | ~ v2_tops_2(X1,X0)
            | k1_xboole_0 = X1
            | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ? [X0] :
      ( ( v1_compts_1(X0)
      <~> ! [X1] :
            ( ? [X2] :
                ( k1_xboole_0 = k6_setfam_1(u1_struct_0(X0),X2)
                & v1_finset_1(X2)
                & r1_tarski(X2,X1)
                & k1_xboole_0 != X2
                & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            | k1_xboole_0 != k6_setfam_1(u1_struct_0(X0),X1)
            | ~ v2_tops_2(X1,X0)
            | k1_xboole_0 = X1
            | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ( v1_compts_1(X0)
        <=> ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ~ ( ! [X2] :
                      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
                     => ~ ( k1_xboole_0 = k6_setfam_1(u1_struct_0(X0),X2)
                          & v1_finset_1(X2)
                          & r1_tarski(X2,X1)
                          & k1_xboole_0 != X2 ) )
                  & k1_xboole_0 = k6_setfam_1(u1_struct_0(X0),X1)
                  & v2_tops_2(X1,X0)
                  & k1_xboole_0 != X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_compts_1(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ~ ( ! [X2] :
                    ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
                   => ~ ( k1_xboole_0 = k6_setfam_1(u1_struct_0(X0),X2)
                        & v1_finset_1(X2)
                        & r1_tarski(X2,X1)
                        & k1_xboole_0 != X2 ) )
                & k1_xboole_0 = k6_setfam_1(u1_struct_0(X0),X1)
                & v2_tops_2(X1,X0)
                & k1_xboole_0 != X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/compts_1__t14_compts_1.p',t14_compts_1)).

fof(f2082,plain,
    ( v2_struct_0(sK0)
    | v1_compts_1(sK0)
    | ~ spl8_1
    | ~ spl8_18
    | ~ spl8_29
    | ~ spl8_30
    | ~ spl8_32
    | ~ spl8_34
    | ~ spl8_48
    | ~ spl8_168 ),
    inference(subsumption_resolution,[],[f2081,f60])).

fof(f60,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f2081,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_compts_1(sK0)
    | ~ spl8_1
    | ~ spl8_18
    | ~ spl8_29
    | ~ spl8_30
    | ~ spl8_32
    | ~ spl8_34
    | ~ spl8_48
    | ~ spl8_168 ),
    inference(subsumption_resolution,[],[f2080,f59])).

fof(f59,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f2080,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_compts_1(sK0)
    | ~ spl8_1
    | ~ spl8_18
    | ~ spl8_29
    | ~ spl8_30
    | ~ spl8_32
    | ~ spl8_34
    | ~ spl8_48
    | ~ spl8_168 ),
    inference(resolution,[],[f1597,f66])).

fof(f66,plain,(
    ! [X0] :
      ( v3_finset_1(sK3(X0))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v1_compts_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( v1_compts_1(X0)
      <=> ! [X1] :
            ( k1_xboole_0 != k6_setfam_1(u1_struct_0(X0),X1)
            | ~ v2_tops_2(X1,X0)
            | ~ v3_finset_1(X1)
            | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( v1_compts_1(X0)
      <=> ! [X1] :
            ( k1_xboole_0 != k6_setfam_1(u1_struct_0(X0),X1)
            | ~ v2_tops_2(X1,X0)
            | ~ v3_finset_1(X1)
            | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_compts_1(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ~ ( k1_xboole_0 = k6_setfam_1(u1_struct_0(X0),X1)
                & v2_tops_2(X1,X0)
                & v3_finset_1(X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/compts_1__t14_compts_1.p',t13_compts_1)).

fof(f1597,plain,
    ( ~ v3_finset_1(sK3(sK0))
    | ~ spl8_1
    | ~ spl8_18
    | ~ spl8_29
    | ~ spl8_30
    | ~ spl8_32
    | ~ spl8_34
    | ~ spl8_48
    | ~ spl8_168 ),
    inference(resolution,[],[f1515,f295])).

fof(f295,plain,
    ( r1_tarski(sK2(sK3(sK0)),sK3(sK0))
    | ~ spl8_48 ),
    inference(avatar_component_clause,[],[f294])).

fof(f294,plain,
    ( spl8_48
  <=> r1_tarski(sK2(sK3(sK0)),sK3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_48])])).

fof(f1515,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK2(sK3(sK0)),X0)
        | ~ v3_finset_1(X0) )
    | ~ spl8_1
    | ~ spl8_18
    | ~ spl8_29
    | ~ spl8_30
    | ~ spl8_32
    | ~ spl8_34
    | ~ spl8_168 ),
    inference(subsumption_resolution,[],[f1514,f1400])).

fof(f1400,plain,
    ( k1_xboole_0 != sK2(sK3(sK0))
    | ~ spl8_1
    | ~ spl8_18
    | ~ spl8_29
    | ~ spl8_30
    | ~ spl8_32 ),
    inference(subsumption_resolution,[],[f1399,f96])).

fof(f1399,plain,
    ( k1_xboole_0 != sK2(sK3(sK0))
    | v1_compts_1(sK0)
    | ~ spl8_18
    | ~ spl8_29
    | ~ spl8_30
    | ~ spl8_32 ),
    inference(subsumption_resolution,[],[f1398,f58])).

fof(f1398,plain,
    ( k1_xboole_0 != sK2(sK3(sK0))
    | v2_struct_0(sK0)
    | v1_compts_1(sK0)
    | ~ spl8_18
    | ~ spl8_29
    | ~ spl8_30
    | ~ spl8_32 ),
    inference(subsumption_resolution,[],[f1397,f60])).

fof(f1397,plain,
    ( k1_xboole_0 != sK2(sK3(sK0))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_compts_1(sK0)
    | ~ spl8_18
    | ~ spl8_29
    | ~ spl8_30
    | ~ spl8_32 ),
    inference(subsumption_resolution,[],[f1396,f59])).

fof(f1396,plain,
    ( k1_xboole_0 != sK2(sK3(sK0))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_compts_1(sK0)
    | ~ spl8_18
    | ~ spl8_29
    | ~ spl8_30
    | ~ spl8_32 ),
    inference(subsumption_resolution,[],[f1395,f183])).

fof(f183,plain,
    ( k1_xboole_0 != sK3(sK0)
    | ~ spl8_29 ),
    inference(avatar_component_clause,[],[f182])).

fof(f182,plain,
    ( spl8_29
  <=> k1_xboole_0 != sK3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_29])])).

fof(f1395,plain,
    ( k1_xboole_0 != sK2(sK3(sK0))
    | k1_xboole_0 = sK3(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_compts_1(sK0)
    | ~ spl8_18
    | ~ spl8_30
    | ~ spl8_32 ),
    inference(subsumption_resolution,[],[f1394,f189])).

fof(f189,plain,
    ( v2_tops_2(sK3(sK0),sK0)
    | ~ spl8_30 ),
    inference(avatar_component_clause,[],[f188])).

fof(f188,plain,
    ( spl8_30
  <=> v2_tops_2(sK3(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).

fof(f1394,plain,
    ( k1_xboole_0 != sK2(sK3(sK0))
    | ~ v2_tops_2(sK3(sK0),sK0)
    | k1_xboole_0 = sK3(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_compts_1(sK0)
    | ~ spl8_18
    | ~ spl8_32 ),
    inference(subsumption_resolution,[],[f374,f195])).

fof(f195,plain,
    ( k1_xboole_0 = k6_setfam_1(u1_struct_0(sK0),sK3(sK0))
    | ~ spl8_32 ),
    inference(avatar_component_clause,[],[f194])).

fof(f194,plain,
    ( spl8_32
  <=> k1_xboole_0 = k6_setfam_1(u1_struct_0(sK0),sK3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_32])])).

fof(f374,plain,
    ( k1_xboole_0 != sK2(sK3(sK0))
    | k1_xboole_0 != k6_setfam_1(u1_struct_0(sK0),sK3(sK0))
    | ~ v2_tops_2(sK3(sK0),sK0)
    | k1_xboole_0 = sK3(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_compts_1(sK0)
    | ~ spl8_18 ),
    inference(resolution,[],[f143,f65])).

fof(f65,plain,(
    ! [X0] :
      ( m1_subset_1(sK3(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v1_compts_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f143,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | k1_xboole_0 != sK2(X1)
        | k1_xboole_0 != k6_setfam_1(u1_struct_0(sK0),X1)
        | ~ v2_tops_2(X1,sK0)
        | k1_xboole_0 = X1 )
    | ~ spl8_18 ),
    inference(avatar_component_clause,[],[f142])).

fof(f142,plain,
    ( spl8_18
  <=> ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | k1_xboole_0 != sK2(X1)
        | k1_xboole_0 != k6_setfam_1(u1_struct_0(sK0),X1)
        | ~ v2_tops_2(X1,sK0)
        | k1_xboole_0 = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f1514,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK2(sK3(sK0)),X0)
        | k1_xboole_0 = sK2(sK3(sK0))
        | ~ v3_finset_1(X0) )
    | ~ spl8_34
    | ~ spl8_168 ),
    inference(subsumption_resolution,[],[f1513,f204])).

fof(f204,plain,
    ( v1_finset_1(sK2(sK3(sK0)))
    | ~ spl8_34 ),
    inference(avatar_component_clause,[],[f203])).

fof(f203,plain,
    ( spl8_34
  <=> v1_finset_1(sK2(sK3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_34])])).

fof(f1513,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK2(sK3(sK0)),X0)
        | ~ v1_finset_1(sK2(sK3(sK0)))
        | k1_xboole_0 = sK2(sK3(sK0))
        | ~ v3_finset_1(X0) )
    | ~ spl8_168 ),
    inference(trivial_inequality_removal,[],[f1512])).

fof(f1512,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k1_xboole_0
        | ~ r1_tarski(sK2(sK3(sK0)),X0)
        | ~ v1_finset_1(sK2(sK3(sK0)))
        | k1_xboole_0 = sK2(sK3(sK0))
        | ~ v3_finset_1(X0) )
    | ~ spl8_168 ),
    inference(superposition,[],[f73,f1159])).

fof(f1159,plain,
    ( k1_xboole_0 = k1_setfam_1(sK2(sK3(sK0)))
    | ~ spl8_168 ),
    inference(avatar_component_clause,[],[f1158])).

fof(f1158,plain,
    ( spl8_168
  <=> k1_xboole_0 = k1_setfam_1(sK2(sK3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_168])])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k1_setfam_1(X1)
      | ~ r1_tarski(X1,X0)
      | ~ v1_finset_1(X1)
      | k1_xboole_0 = X1
      | ~ v3_finset_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( v3_finset_1(X0)
    <=> ( ! [X1] :
            ( k1_xboole_0 != k1_setfam_1(X1)
            | ~ v1_finset_1(X1)
            | ~ r1_tarski(X1,X0)
            | k1_xboole_0 = X1 )
        & k1_xboole_0 != X0 ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v3_finset_1(X0)
    <=> ( ! [X1] :
            ~ ( k1_xboole_0 = k1_setfam_1(X1)
              & v1_finset_1(X1)
              & r1_tarski(X1,X0)
              & k1_xboole_0 != X1 )
        & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/compts_1__t14_compts_1.p',d3_finset_1)).

fof(f1160,plain,
    ( spl8_0
    | spl8_168
    | ~ spl8_12
    | ~ spl8_20
    | spl8_29
    | ~ spl8_30
    | ~ spl8_32 ),
    inference(avatar_split_clause,[],[f1153,f194,f188,f182,f146,f130,f1158,f92])).

fof(f92,plain,
    ( spl8_0
  <=> v1_compts_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_0])])).

fof(f130,plain,
    ( spl8_12
  <=> ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | k1_xboole_0 = k6_setfam_1(u1_struct_0(sK0),sK2(X1))
        | k1_xboole_0 != k6_setfam_1(u1_struct_0(sK0),X1)
        | ~ v2_tops_2(X1,sK0)
        | k1_xboole_0 = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f146,plain,
    ( spl8_20
  <=> ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | m1_subset_1(sK2(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | k1_xboole_0 != k6_setfam_1(u1_struct_0(sK0),X1)
        | ~ v2_tops_2(X1,sK0)
        | k1_xboole_0 = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f1153,plain,
    ( k1_xboole_0 = k1_setfam_1(sK2(sK3(sK0)))
    | v1_compts_1(sK0)
    | ~ spl8_12
    | ~ spl8_20
    | ~ spl8_29
    | ~ spl8_30
    | ~ spl8_32 ),
    inference(subsumption_resolution,[],[f1152,f58])).

fof(f1152,plain,
    ( k1_xboole_0 = k1_setfam_1(sK2(sK3(sK0)))
    | v2_struct_0(sK0)
    | v1_compts_1(sK0)
    | ~ spl8_12
    | ~ spl8_20
    | ~ spl8_29
    | ~ spl8_30
    | ~ spl8_32 ),
    inference(subsumption_resolution,[],[f1151,f60])).

fof(f1151,plain,
    ( k1_xboole_0 = k1_setfam_1(sK2(sK3(sK0)))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_compts_1(sK0)
    | ~ spl8_12
    | ~ spl8_20
    | ~ spl8_29
    | ~ spl8_30
    | ~ spl8_32 ),
    inference(subsumption_resolution,[],[f1150,f59])).

fof(f1150,plain,
    ( k1_xboole_0 = k1_setfam_1(sK2(sK3(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_compts_1(sK0)
    | ~ spl8_12
    | ~ spl8_20
    | ~ spl8_29
    | ~ spl8_30
    | ~ spl8_32 ),
    inference(subsumption_resolution,[],[f1149,f183])).

fof(f1149,plain,
    ( k1_xboole_0 = k1_setfam_1(sK2(sK3(sK0)))
    | k1_xboole_0 = sK3(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_compts_1(sK0)
    | ~ spl8_12
    | ~ spl8_20
    | ~ spl8_30
    | ~ spl8_32 ),
    inference(subsumption_resolution,[],[f1148,f189])).

fof(f1148,plain,
    ( k1_xboole_0 = k1_setfam_1(sK2(sK3(sK0)))
    | ~ v2_tops_2(sK3(sK0),sK0)
    | k1_xboole_0 = sK3(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_compts_1(sK0)
    | ~ spl8_12
    | ~ spl8_20
    | ~ spl8_32 ),
    inference(subsumption_resolution,[],[f738,f195])).

fof(f738,plain,
    ( k1_xboole_0 = k1_setfam_1(sK2(sK3(sK0)))
    | k1_xboole_0 != k6_setfam_1(u1_struct_0(sK0),sK3(sK0))
    | ~ v2_tops_2(sK3(sK0),sK0)
    | k1_xboole_0 = sK3(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_compts_1(sK0)
    | ~ spl8_12
    | ~ spl8_20 ),
    inference(resolution,[],[f391,f65])).

fof(f391,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | k1_xboole_0 = k1_setfam_1(sK2(X1))
        | k1_xboole_0 != k6_setfam_1(u1_struct_0(sK0),X1)
        | ~ v2_tops_2(X1,sK0)
        | k1_xboole_0 = X1 )
    | ~ spl8_12
    | ~ spl8_20 ),
    inference(subsumption_resolution,[],[f388,f147])).

fof(f147,plain,
    ( ! [X1] :
        ( m1_subset_1(sK2(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | k1_xboole_0 != k6_setfam_1(u1_struct_0(sK0),X1)
        | ~ v2_tops_2(X1,sK0)
        | k1_xboole_0 = X1 )
    | ~ spl8_20 ),
    inference(avatar_component_clause,[],[f146])).

fof(f388,plain,
    ( ! [X1] :
        ( k1_xboole_0 = k1_setfam_1(sK2(X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | k1_xboole_0 != k6_setfam_1(u1_struct_0(sK0),X1)
        | ~ v2_tops_2(X1,sK0)
        | k1_xboole_0 = X1
        | ~ m1_subset_1(sK2(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
    | ~ spl8_12 ),
    inference(superposition,[],[f131,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/compts_1__t14_compts_1.p',redefinition_k6_setfam_1)).

fof(f131,plain,
    ( ! [X1] :
        ( k1_xboole_0 = k6_setfam_1(u1_struct_0(sK0),sK2(X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | k1_xboole_0 != k6_setfam_1(u1_struct_0(sK0),X1)
        | ~ v2_tops_2(X1,sK0)
        | k1_xboole_0 = X1 )
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f130])).

fof(f1116,plain,
    ( ~ spl8_0
    | ~ spl8_2
    | ~ spl8_4
    | spl8_7
    | ~ spl8_8
    | ~ spl8_10 ),
    inference(avatar_contradiction_clause,[],[f1115])).

fof(f1115,plain,
    ( $false
    | ~ spl8_0
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_10 ),
    inference(subsumption_resolution,[],[f1114,f351])).

fof(f351,plain,
    ( ~ v3_finset_1(sK1)
    | ~ spl8_0
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f350,f93])).

fof(f93,plain,
    ( v1_compts_1(sK0)
    | ~ spl8_0 ),
    inference(avatar_component_clause,[],[f92])).

fof(f350,plain,
    ( ~ v3_finset_1(sK1)
    | ~ v1_compts_1(sK0)
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f349,f102])).

fof(f102,plain,
    ( k1_xboole_0 = k6_setfam_1(u1_struct_0(sK0),sK1)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl8_2
  <=> k1_xboole_0 = k6_setfam_1(u1_struct_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f349,plain,
    ( ~ v3_finset_1(sK1)
    | k1_xboole_0 != k6_setfam_1(u1_struct_0(sK0),sK1)
    | ~ v1_compts_1(sK0)
    | ~ spl8_4
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f348,f109])).

fof(f109,plain,
    ( v2_tops_2(sK1,sK0)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl8_4
  <=> v2_tops_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f348,plain,
    ( ~ v3_finset_1(sK1)
    | ~ v2_tops_2(sK1,sK0)
    | k1_xboole_0 != k6_setfam_1(u1_struct_0(sK0),sK1)
    | ~ v1_compts_1(sK0)
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f347,f58])).

fof(f347,plain,
    ( v2_struct_0(sK0)
    | ~ v3_finset_1(sK1)
    | ~ v2_tops_2(sK1,sK0)
    | k1_xboole_0 != k6_setfam_1(u1_struct_0(sK0),sK1)
    | ~ v1_compts_1(sK0)
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f346,f60])).

fof(f346,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ v3_finset_1(sK1)
    | ~ v2_tops_2(sK1,sK0)
    | k1_xboole_0 != k6_setfam_1(u1_struct_0(sK0),sK1)
    | ~ v1_compts_1(sK0)
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f336,f59])).

fof(f336,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ v3_finset_1(sK1)
    | ~ v2_tops_2(sK1,sK0)
    | k1_xboole_0 != k6_setfam_1(u1_struct_0(sK0),sK1)
    | ~ v1_compts_1(sK0)
    | ~ spl8_8 ),
    inference(resolution,[],[f123,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ v3_finset_1(X1)
      | ~ v2_tops_2(X1,X0)
      | k1_xboole_0 != k6_setfam_1(u1_struct_0(X0),X1)
      | ~ v1_compts_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f123,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl8_8
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f1114,plain,
    ( v3_finset_1(sK1)
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_10 ),
    inference(subsumption_resolution,[],[f1113,f116])).

fof(f116,plain,
    ( k1_xboole_0 != sK1
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl8_7
  <=> k1_xboole_0 != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f1113,plain,
    ( k1_xboole_0 = sK1
    | v3_finset_1(sK1)
    | ~ spl8_8
    | ~ spl8_10 ),
    inference(duplicate_literal_removal,[],[f1111])).

fof(f1111,plain,
    ( k1_xboole_0 = sK1
    | v3_finset_1(sK1)
    | k1_xboole_0 = sK1
    | v3_finset_1(sK1)
    | ~ spl8_8
    | ~ spl8_10 ),
    inference(resolution,[],[f1110,f70])).

fof(f70,plain,(
    ! [X0] :
      ( r1_tarski(sK4(X0),X0)
      | k1_xboole_0 = X0
      | v3_finset_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f1110,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK4(X0),sK1)
        | k1_xboole_0 = X0
        | v3_finset_1(X0) )
    | ~ spl8_8
    | ~ spl8_10 ),
    inference(subsumption_resolution,[],[f1109,f71])).

fof(f71,plain,(
    ! [X0] :
      ( v1_finset_1(sK4(X0))
      | k1_xboole_0 = X0
      | v3_finset_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f1109,plain,
    ( ! [X0] :
        ( ~ v1_finset_1(sK4(X0))
        | ~ r1_tarski(sK4(X0),sK1)
        | k1_xboole_0 = X0
        | v3_finset_1(X0) )
    | ~ spl8_8
    | ~ spl8_10 ),
    inference(subsumption_resolution,[],[f1108,f69])).

fof(f69,plain,(
    ! [X0] :
      ( k1_xboole_0 != sK4(X0)
      | k1_xboole_0 = X0
      | v3_finset_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f1108,plain,
    ( ! [X0] :
        ( k1_xboole_0 = sK4(X0)
        | ~ v1_finset_1(sK4(X0))
        | ~ r1_tarski(sK4(X0),sK1)
        | k1_xboole_0 = X0
        | v3_finset_1(X0) )
    | ~ spl8_8
    | ~ spl8_10 ),
    inference(trivial_inequality_removal,[],[f1103])).

fof(f1103,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k1_xboole_0
        | k1_xboole_0 = sK4(X0)
        | ~ v1_finset_1(sK4(X0))
        | ~ r1_tarski(sK4(X0),sK1)
        | k1_xboole_0 = X0
        | v3_finset_1(X0) )
    | ~ spl8_8
    | ~ spl8_10 ),
    inference(superposition,[],[f1102,f72])).

fof(f72,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_setfam_1(sK4(X0))
      | k1_xboole_0 = X0
      | v3_finset_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f1102,plain,
    ( ! [X3] :
        ( k1_xboole_0 != k1_setfam_1(X3)
        | k1_xboole_0 = X3
        | ~ v1_finset_1(X3)
        | ~ r1_tarski(X3,sK1) )
    | ~ spl8_8
    | ~ spl8_10 ),
    inference(duplicate_literal_removal,[],[f1099])).

fof(f1099,plain,
    ( ! [X3] :
        ( k1_xboole_0 = X3
        | k1_xboole_0 != k1_setfam_1(X3)
        | ~ v1_finset_1(X3)
        | ~ r1_tarski(X3,sK1)
        | ~ r1_tarski(X3,sK1) )
    | ~ spl8_8
    | ~ spl8_10 ),
    inference(resolution,[],[f951,f339])).

fof(f339,plain,
    ( r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_8 ),
    inference(resolution,[],[f123,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/compts_1__t14_compts_1.p',t3_subset)).

fof(f951,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X0
        | k1_xboole_0 != k1_setfam_1(X0)
        | ~ v1_finset_1(X0)
        | ~ r1_tarski(X0,sK1)
        | ~ r1_tarski(X0,X1) )
    | ~ spl8_10 ),
    inference(resolution,[],[f945,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/compts_1__t14_compts_1.p',t1_xboole_1)).

fof(f945,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X0,sK1)
        | k1_xboole_0 = X0
        | k1_xboole_0 != k1_setfam_1(X0)
        | ~ v1_finset_1(X0) )
    | ~ spl8_10 ),
    inference(resolution,[],[f545,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f545,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ v1_finset_1(X1)
        | ~ r1_tarski(X1,sK1)
        | k1_xboole_0 = X1
        | k1_xboole_0 != k1_setfam_1(X1) )
    | ~ spl8_10 ),
    inference(subsumption_resolution,[],[f540,f82])).

fof(f540,plain,
    ( ! [X1] :
        ( k1_xboole_0 != k1_setfam_1(X1)
        | ~ v1_finset_1(X1)
        | ~ r1_tarski(X1,sK1)
        | k1_xboole_0 = X1
        | ~ r1_tarski(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
    | ~ spl8_10 ),
    inference(superposition,[],[f362,f79])).

fof(f362,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k6_setfam_1(u1_struct_0(sK0),X0)
        | ~ v1_finset_1(X0)
        | ~ r1_tarski(X0,sK1)
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl8_10 ),
    inference(resolution,[],[f127,f81])).

fof(f127,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | k1_xboole_0 != k6_setfam_1(u1_struct_0(sK0),X2)
        | ~ v1_finset_1(X2)
        | ~ r1_tarski(X2,sK1)
        | k1_xboole_0 = X2 )
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f126])).

fof(f126,plain,
    ( spl8_10
  <=> ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | k1_xboole_0 != k6_setfam_1(u1_struct_0(sK0),X2)
        | ~ v1_finset_1(X2)
        | ~ r1_tarski(X2,sK1)
        | k1_xboole_0 = X2 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f300,plain,
    ( spl8_0
    | spl8_48
    | ~ spl8_16
    | spl8_29
    | ~ spl8_30
    | ~ spl8_32 ),
    inference(avatar_split_clause,[],[f299,f194,f188,f182,f138,f294,f92])).

fof(f138,plain,
    ( spl8_16
  <=> ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | r1_tarski(sK2(X1),X1)
        | k1_xboole_0 != k6_setfam_1(u1_struct_0(sK0),X1)
        | ~ v2_tops_2(X1,sK0)
        | k1_xboole_0 = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f299,plain,
    ( r1_tarski(sK2(sK3(sK0)),sK3(sK0))
    | v1_compts_1(sK0)
    | ~ spl8_16
    | ~ spl8_29
    | ~ spl8_30
    | ~ spl8_32 ),
    inference(subsumption_resolution,[],[f298,f183])).

fof(f298,plain,
    ( r1_tarski(sK2(sK3(sK0)),sK3(sK0))
    | k1_xboole_0 = sK3(sK0)
    | v1_compts_1(sK0)
    | ~ spl8_16
    | ~ spl8_30
    | ~ spl8_32 ),
    inference(subsumption_resolution,[],[f297,f189])).

fof(f297,plain,
    ( r1_tarski(sK2(sK3(sK0)),sK3(sK0))
    | ~ v2_tops_2(sK3(sK0),sK0)
    | k1_xboole_0 = sK3(sK0)
    | v1_compts_1(sK0)
    | ~ spl8_16
    | ~ spl8_32 ),
    inference(subsumption_resolution,[],[f288,f195])).

fof(f288,plain,
    ( r1_tarski(sK2(sK3(sK0)),sK3(sK0))
    | k1_xboole_0 != k6_setfam_1(u1_struct_0(sK0),sK3(sK0))
    | ~ v2_tops_2(sK3(sK0),sK0)
    | k1_xboole_0 = sK3(sK0)
    | v1_compts_1(sK0)
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f287,f58])).

fof(f287,plain,
    ( r1_tarski(sK2(sK3(sK0)),sK3(sK0))
    | k1_xboole_0 != k6_setfam_1(u1_struct_0(sK0),sK3(sK0))
    | ~ v2_tops_2(sK3(sK0),sK0)
    | k1_xboole_0 = sK3(sK0)
    | v2_struct_0(sK0)
    | v1_compts_1(sK0)
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f286,f60])).

fof(f286,plain,
    ( r1_tarski(sK2(sK3(sK0)),sK3(sK0))
    | k1_xboole_0 != k6_setfam_1(u1_struct_0(sK0),sK3(sK0))
    | ~ v2_tops_2(sK3(sK0),sK0)
    | k1_xboole_0 = sK3(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_compts_1(sK0)
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f266,f59])).

fof(f266,plain,
    ( r1_tarski(sK2(sK3(sK0)),sK3(sK0))
    | k1_xboole_0 != k6_setfam_1(u1_struct_0(sK0),sK3(sK0))
    | ~ v2_tops_2(sK3(sK0),sK0)
    | k1_xboole_0 = sK3(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_compts_1(sK0)
    | ~ spl8_16 ),
    inference(resolution,[],[f139,f65])).

fof(f139,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | r1_tarski(sK2(X1),X1)
        | k1_xboole_0 != k6_setfam_1(u1_struct_0(sK0),X1)
        | ~ v2_tops_2(X1,sK0)
        | k1_xboole_0 = X1 )
    | ~ spl8_16 ),
    inference(avatar_component_clause,[],[f138])).

fof(f285,plain,
    ( spl8_1
    | ~ spl8_28 ),
    inference(avatar_contradiction_clause,[],[f284])).

fof(f284,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_28 ),
    inference(subsumption_resolution,[],[f283,f96])).

fof(f283,plain,
    ( v1_compts_1(sK0)
    | ~ spl8_28 ),
    inference(subsumption_resolution,[],[f282,f58])).

fof(f282,plain,
    ( v2_struct_0(sK0)
    | v1_compts_1(sK0)
    | ~ spl8_28 ),
    inference(subsumption_resolution,[],[f281,f60])).

fof(f281,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_compts_1(sK0)
    | ~ spl8_28 ),
    inference(subsumption_resolution,[],[f280,f59])).

fof(f280,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_compts_1(sK0)
    | ~ spl8_28 ),
    inference(subsumption_resolution,[],[f271,f90])).

fof(f90,plain,(
    ~ v3_finset_1(k1_xboole_0) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | ~ v3_finset_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f271,plain,
    ( v3_finset_1(k1_xboole_0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_compts_1(sK0)
    | ~ spl8_28 ),
    inference(superposition,[],[f66,f186])).

fof(f186,plain,
    ( k1_xboole_0 = sK3(sK0)
    | ~ spl8_28 ),
    inference(avatar_component_clause,[],[f185])).

fof(f185,plain,
    ( spl8_28
  <=> k1_xboole_0 = sK3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).

fof(f245,plain,
    ( spl8_1
    | spl8_33 ),
    inference(avatar_contradiction_clause,[],[f244])).

fof(f244,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_33 ),
    inference(subsumption_resolution,[],[f243,f96])).

fof(f243,plain,
    ( v1_compts_1(sK0)
    | ~ spl8_33 ),
    inference(subsumption_resolution,[],[f242,f58])).

fof(f242,plain,
    ( v2_struct_0(sK0)
    | v1_compts_1(sK0)
    | ~ spl8_33 ),
    inference(subsumption_resolution,[],[f241,f60])).

fof(f241,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_compts_1(sK0)
    | ~ spl8_33 ),
    inference(subsumption_resolution,[],[f240,f59])).

fof(f240,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_compts_1(sK0)
    | ~ spl8_33 ),
    inference(trivial_inequality_removal,[],[f238])).

fof(f238,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_compts_1(sK0)
    | ~ spl8_33 ),
    inference(superposition,[],[f198,f68])).

fof(f68,plain,(
    ! [X0] :
      ( k1_xboole_0 = k6_setfam_1(u1_struct_0(X0),sK3(X0))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v1_compts_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f198,plain,
    ( k1_xboole_0 != k6_setfam_1(u1_struct_0(sK0),sK3(sK0))
    | ~ spl8_33 ),
    inference(avatar_component_clause,[],[f197])).

fof(f197,plain,
    ( spl8_33
  <=> k1_xboole_0 != k6_setfam_1(u1_struct_0(sK0),sK3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_33])])).

fof(f236,plain,
    ( spl8_1
    | spl8_31 ),
    inference(avatar_contradiction_clause,[],[f235])).

fof(f235,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_31 ),
    inference(subsumption_resolution,[],[f234,f96])).

fof(f234,plain,
    ( v1_compts_1(sK0)
    | ~ spl8_31 ),
    inference(subsumption_resolution,[],[f233,f58])).

fof(f233,plain,
    ( v2_struct_0(sK0)
    | v1_compts_1(sK0)
    | ~ spl8_31 ),
    inference(subsumption_resolution,[],[f232,f60])).

fof(f232,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_compts_1(sK0)
    | ~ spl8_31 ),
    inference(subsumption_resolution,[],[f231,f59])).

fof(f231,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_compts_1(sK0)
    | ~ spl8_31 ),
    inference(resolution,[],[f192,f67])).

fof(f67,plain,(
    ! [X0] :
      ( v2_tops_2(sK3(X0),X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v1_compts_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f192,plain,
    ( ~ v2_tops_2(sK3(sK0),sK0)
    | ~ spl8_31 ),
    inference(avatar_component_clause,[],[f191])).

fof(f191,plain,
    ( spl8_31
  <=> ~ v2_tops_2(sK3(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_31])])).

fof(f205,plain,
    ( spl8_28
    | ~ spl8_31
    | ~ spl8_33
    | spl8_34
    | spl8_1
    | ~ spl8_14 ),
    inference(avatar_split_clause,[],[f180,f134,f95,f203,f197,f191,f185])).

fof(f134,plain,
    ( spl8_14
  <=> ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | v1_finset_1(sK2(X1))
        | k1_xboole_0 != k6_setfam_1(u1_struct_0(sK0),X1)
        | ~ v2_tops_2(X1,sK0)
        | k1_xboole_0 = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f180,plain,
    ( v1_finset_1(sK2(sK3(sK0)))
    | k1_xboole_0 != k6_setfam_1(u1_struct_0(sK0),sK3(sK0))
    | ~ v2_tops_2(sK3(sK0),sK0)
    | k1_xboole_0 = sK3(sK0)
    | ~ spl8_1
    | ~ spl8_14 ),
    inference(subsumption_resolution,[],[f179,f96])).

fof(f179,plain,
    ( v1_finset_1(sK2(sK3(sK0)))
    | k1_xboole_0 != k6_setfam_1(u1_struct_0(sK0),sK3(sK0))
    | ~ v2_tops_2(sK3(sK0),sK0)
    | k1_xboole_0 = sK3(sK0)
    | v1_compts_1(sK0)
    | ~ spl8_14 ),
    inference(subsumption_resolution,[],[f178,f58])).

fof(f178,plain,
    ( v1_finset_1(sK2(sK3(sK0)))
    | k1_xboole_0 != k6_setfam_1(u1_struct_0(sK0),sK3(sK0))
    | ~ v2_tops_2(sK3(sK0),sK0)
    | k1_xboole_0 = sK3(sK0)
    | v2_struct_0(sK0)
    | v1_compts_1(sK0)
    | ~ spl8_14 ),
    inference(subsumption_resolution,[],[f177,f60])).

fof(f177,plain,
    ( v1_finset_1(sK2(sK3(sK0)))
    | k1_xboole_0 != k6_setfam_1(u1_struct_0(sK0),sK3(sK0))
    | ~ v2_tops_2(sK3(sK0),sK0)
    | k1_xboole_0 = sK3(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_compts_1(sK0)
    | ~ spl8_14 ),
    inference(subsumption_resolution,[],[f175,f59])).

fof(f175,plain,
    ( v1_finset_1(sK2(sK3(sK0)))
    | k1_xboole_0 != k6_setfam_1(u1_struct_0(sK0),sK3(sK0))
    | ~ v2_tops_2(sK3(sK0),sK0)
    | k1_xboole_0 = sK3(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_compts_1(sK0)
    | ~ spl8_14 ),
    inference(resolution,[],[f135,f65])).

fof(f135,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | v1_finset_1(sK2(X1))
        | k1_xboole_0 != k6_setfam_1(u1_struct_0(sK0),X1)
        | ~ v2_tops_2(X1,sK0)
        | k1_xboole_0 = X1 )
    | ~ spl8_14 ),
    inference(avatar_component_clause,[],[f134])).

fof(f148,plain,
    ( spl8_0
    | spl8_20 ),
    inference(avatar_split_clause,[],[f48,f146,f92])).

fof(f48,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | k1_xboole_0 = X1
      | ~ v2_tops_2(X1,sK0)
      | k1_xboole_0 != k6_setfam_1(u1_struct_0(sK0),X1)
      | m1_subset_1(sK2(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | v1_compts_1(sK0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f144,plain,
    ( spl8_0
    | spl8_18 ),
    inference(avatar_split_clause,[],[f49,f142,f92])).

fof(f49,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | k1_xboole_0 = X1
      | ~ v2_tops_2(X1,sK0)
      | k1_xboole_0 != k6_setfam_1(u1_struct_0(sK0),X1)
      | k1_xboole_0 != sK2(X1)
      | v1_compts_1(sK0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f140,plain,
    ( spl8_0
    | spl8_16 ),
    inference(avatar_split_clause,[],[f50,f138,f92])).

fof(f50,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | k1_xboole_0 = X1
      | ~ v2_tops_2(X1,sK0)
      | k1_xboole_0 != k6_setfam_1(u1_struct_0(sK0),X1)
      | r1_tarski(sK2(X1),X1)
      | v1_compts_1(sK0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f136,plain,
    ( spl8_0
    | spl8_14 ),
    inference(avatar_split_clause,[],[f51,f134,f92])).

fof(f51,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | k1_xboole_0 = X1
      | ~ v2_tops_2(X1,sK0)
      | k1_xboole_0 != k6_setfam_1(u1_struct_0(sK0),X1)
      | v1_finset_1(sK2(X1))
      | v1_compts_1(sK0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f132,plain,
    ( spl8_0
    | spl8_12 ),
    inference(avatar_split_clause,[],[f52,f130,f92])).

fof(f52,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | k1_xboole_0 = X1
      | ~ v2_tops_2(X1,sK0)
      | k1_xboole_0 != k6_setfam_1(u1_struct_0(sK0),X1)
      | k1_xboole_0 = k6_setfam_1(u1_struct_0(sK0),sK2(X1))
      | v1_compts_1(sK0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f128,plain,
    ( ~ spl8_1
    | spl8_10 ),
    inference(avatar_split_clause,[],[f53,f126,f95])).

fof(f53,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | k1_xboole_0 = X2
      | ~ r1_tarski(X2,sK1)
      | ~ v1_finset_1(X2)
      | k1_xboole_0 != k6_setfam_1(u1_struct_0(sK0),X2)
      | ~ v1_compts_1(sK0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f124,plain,
    ( ~ spl8_1
    | spl8_8 ),
    inference(avatar_split_clause,[],[f54,f122,f95])).

fof(f54,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ v1_compts_1(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f117,plain,
    ( ~ spl8_1
    | ~ spl8_7 ),
    inference(avatar_split_clause,[],[f55,f115,f95])).

fof(f55,plain,
    ( k1_xboole_0 != sK1
    | ~ v1_compts_1(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f110,plain,
    ( ~ spl8_1
    | spl8_4 ),
    inference(avatar_split_clause,[],[f56,f108,f95])).

fof(f56,plain,
    ( v2_tops_2(sK1,sK0)
    | ~ v1_compts_1(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f103,plain,
    ( ~ spl8_1
    | spl8_2 ),
    inference(avatar_split_clause,[],[f57,f101,f95])).

fof(f57,plain,
    ( k1_xboole_0 = k6_setfam_1(u1_struct_0(sK0),sK1)
    | ~ v1_compts_1(sK0) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
