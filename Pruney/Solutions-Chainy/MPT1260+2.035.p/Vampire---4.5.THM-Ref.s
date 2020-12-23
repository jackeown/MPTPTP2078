%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:38 EST 2020

% Result     : Theorem 5.93s
% Output     : Refutation 5.93s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 259 expanded)
%              Number of leaves         :   25 (  89 expanded)
%              Depth                    :   14
%              Number of atoms          :  534 (1250 expanded)
%              Number of equality atoms :   87 ( 224 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1482,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f109,f114,f119,f128,f130,f198,f608,f625,f732,f770,f988,f1091,f1284,f1307,f1353,f1481])).

fof(f1481,plain,
    ( ~ spl5_2
    | ~ spl5_3
    | spl5_5
    | ~ spl5_19 ),
    inference(avatar_contradiction_clause,[],[f1480])).

fof(f1480,plain,
    ( $false
    | ~ spl5_2
    | ~ spl5_3
    | spl5_5
    | ~ spl5_19 ),
    inference(subsumption_resolution,[],[f1393,f126])).

fof(f126,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | spl5_5 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl5_5
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f1393,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_19 ),
    inference(subsumption_resolution,[],[f1392,f113])).

fof(f113,plain,
    ( l1_pre_topc(sK0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl5_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f1392,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl5_3
    | ~ spl5_19 ),
    inference(subsumption_resolution,[],[f1346,f118])).

fof(f118,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl5_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f1346,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl5_19 ),
    inference(superposition,[],[f70,f458])).

fof(f458,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f456])).

fof(f456,plain,
    ( spl5_19
  <=> sK1 = k1_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

fof(f1353,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_4
    | ~ spl5_19
    | ~ spl5_38 ),
    inference(avatar_contradiction_clause,[],[f1352])).

fof(f1352,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_4
    | ~ spl5_19
    | ~ spl5_38 ),
    inference(subsumption_resolution,[],[f1351,f122])).

fof(f122,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | spl5_4 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl5_4
  <=> v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f1351,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_19
    | ~ spl5_38 ),
    inference(subsumption_resolution,[],[f1350,f118])).

fof(f1350,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(sK1,sK0)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_19
    | ~ spl5_38 ),
    inference(subsumption_resolution,[],[f1349,f113])).

fof(f1349,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(sK1,sK0)
    | ~ spl5_1
    | ~ spl5_19
    | ~ spl5_38 ),
    inference(subsumption_resolution,[],[f1347,f108])).

fof(f108,plain,
    ( v2_pre_topc(sK0)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl5_1
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f1347,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(sK1,sK0)
    | ~ spl5_19
    | ~ spl5_38 ),
    inference(trivial_inequality_removal,[],[f1345])).

fof(f1345,plain,
    ( sK1 != sK1
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(sK1,sK0)
    | ~ spl5_19
    | ~ spl5_38 ),
    inference(superposition,[],[f731,f458])).

fof(f731,plain,
    ( ! [X2,X0] :
        ( k1_tops_1(X0,X2) != X2
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | v3_pre_topc(X2,X0) )
    | ~ spl5_38 ),
    inference(avatar_component_clause,[],[f730])).

fof(f730,plain,
    ( spl5_38
  <=> ! [X0,X2] :
        ( v3_pre_topc(X2,X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | k1_tops_1(X0,X2) != X2 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).

fof(f1307,plain,
    ( spl5_19
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_67 ),
    inference(avatar_split_clause,[],[f1305,f1281,f116,f111,f456])).

fof(f1281,plain,
    ( spl5_67
  <=> sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_67])])).

fof(f1305,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_67 ),
    inference(subsumption_resolution,[],[f1304,f113])).

fof(f1304,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl5_3
    | ~ spl5_67 ),
    inference(subsumption_resolution,[],[f1285,f118])).

fof(f1285,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl5_67 ),
    inference(superposition,[],[f1283,f398])).

fof(f398,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f397])).

fof(f397,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(superposition,[],[f69,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f1283,plain,
    ( sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl5_67 ),
    inference(avatar_component_clause,[],[f1281])).

fof(f1284,plain,
    ( spl5_67
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f1278,f195,f1281])).

fof(f195,plain,
    ( spl5_8
  <=> k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f1278,plain,
    ( sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl5_8 ),
    inference(duplicate_literal_removal,[],[f1273])).

fof(f1273,plain,
    ( sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl5_8 ),
    inference(resolution,[],[f1119,f296])).

fof(f296,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1,X0),X0)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(factoring,[],[f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X2),X2)
      | r2_hidden(sK2(X0,X1,X2),X0)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK2(X0,X1,X2),X1)
            | ~ r2_hidden(sK2(X0,X1,X2),X0)
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
              & r2_hidden(sK2(X0,X1,X2),X0) )
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f52,f53])).

fof(f53,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK2(X0,X1,X2),X1)
          | ~ r2_hidden(sK2(X0,X1,X2),X0)
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
            & r2_hidden(sK2(X0,X1,X2),X0) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
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
    inference(rectify,[],[f51])).

fof(f51,plain,(
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
    inference(flattening,[],[f50])).

fof(f50,plain,(
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

fof(f1119,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK2(X1,k2_tops_1(sK0,sK1),X1),sK1)
        | k4_xboole_0(X1,k2_tops_1(sK0,sK1)) = X1 )
    | ~ spl5_8 ),
    inference(resolution,[],[f1107,f529])).

fof(f529,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1,X0),X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(subsumption_resolution,[],[f528,f80])).

fof(f528,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1,X0),X1)
      | ~ r2_hidden(sK2(X0,X1,X0),X0)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(duplicate_literal_removal,[],[f520])).

fof(f520,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1,X0),X1)
      | ~ r2_hidden(sK2(X0,X1,X0),X0)
      | k4_xboole_0(X0,X1) = X0
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(resolution,[],[f82,f296])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1,X2),X2)
      | r2_hidden(sK2(X0,X1,X2),X1)
      | ~ r2_hidden(sK2(X0,X1,X2),X0)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f54])).

fof(f1107,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k2_tops_1(sK0,sK1))
        | ~ r2_hidden(X1,sK1) )
    | ~ spl5_8 ),
    inference(superposition,[],[f100,f197])).

fof(f197,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f195])).

fof(f100,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f54])).

fof(f1091,plain,
    ( ~ spl5_2
    | ~ spl5_3
    | spl5_7 ),
    inference(avatar_contradiction_clause,[],[f1090])).

fof(f1090,plain,
    ( $false
    | ~ spl5_2
    | ~ spl5_3
    | spl5_7 ),
    inference(subsumption_resolution,[],[f1089,f113])).

fof(f1089,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl5_3
    | spl5_7 ),
    inference(subsumption_resolution,[],[f1079,f118])).

fof(f1079,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl5_7 ),
    inference(resolution,[],[f449,f193])).

fof(f193,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl5_7 ),
    inference(avatar_component_clause,[],[f191])).

fof(f191,plain,
    ( spl5_7
  <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f449,plain,(
    ! [X2,X3] :
      ( m1_subset_1(k2_pre_topc(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2) ) ),
    inference(subsumption_resolution,[],[f444,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f444,plain,(
    ! [X2,X3] :
      ( m1_subset_1(k2_pre_topc(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2) ) ),
    inference(duplicate_literal_removal,[],[f443])).

fof(f443,plain,(
    ! [X2,X3] :
      ( m1_subset_1(k2_pre_topc(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2) ) ),
    inference(superposition,[],[f85,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).

fof(f988,plain,
    ( spl5_19
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_32 ),
    inference(avatar_split_clause,[],[f987,f606,f121,f116,f111,f456])).

fof(f606,plain,
    ( spl5_32
  <=> ! [X1,X3] :
        ( k1_tops_1(X1,X3) = X3
        | ~ l1_pre_topc(X1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ v3_pre_topc(X3,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).

fof(f987,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_32 ),
    inference(subsumption_resolution,[],[f867,f123])).

fof(f123,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f121])).

fof(f867,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ v3_pre_topc(sK1,sK0)
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_32 ),
    inference(subsumption_resolution,[],[f688,f113])).

fof(f688,plain,
    ( ~ l1_pre_topc(sK0)
    | sK1 = k1_tops_1(sK0,sK1)
    | ~ v3_pre_topc(sK1,sK0)
    | ~ spl5_3
    | ~ spl5_32 ),
    inference(resolution,[],[f607,f118])).

fof(f607,plain,
    ( ! [X3,X1] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ l1_pre_topc(X1)
        | k1_tops_1(X1,X3) = X3
        | ~ v3_pre_topc(X3,X1) )
    | ~ spl5_32 ),
    inference(avatar_component_clause,[],[f606])).

fof(f770,plain,
    ( ~ spl5_2
    | ~ spl5_3
    | ~ spl5_37 ),
    inference(avatar_contradiction_clause,[],[f769])).

fof(f769,plain,
    ( $false
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_37 ),
    inference(subsumption_resolution,[],[f765,f113])).

fof(f765,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl5_3
    | ~ spl5_37 ),
    inference(resolution,[],[f728,f118])).

fof(f728,plain,
    ( ! [X3,X1] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ l1_pre_topc(X1) )
    | ~ spl5_37 ),
    inference(avatar_component_clause,[],[f727])).

fof(f727,plain,
    ( spl5_37
  <=> ! [X1,X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ l1_pre_topc(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).

fof(f732,plain,
    ( spl5_37
    | spl5_38 ),
    inference(avatar_split_clause,[],[f76,f730,f727])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( v3_pre_topc(X2,X0)
      | k1_tops_1(X0,X2) != X2
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f36,plain,(
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
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
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

fof(f625,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_31 ),
    inference(avatar_contradiction_clause,[],[f624])).

fof(f624,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_31 ),
    inference(subsumption_resolution,[],[f623,f113])).

fof(f623,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl5_1
    | ~ spl5_3
    | ~ spl5_31 ),
    inference(subsumption_resolution,[],[f619,f108])).

fof(f619,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl5_3
    | ~ spl5_31 ),
    inference(resolution,[],[f604,f118])).

fof(f604,plain,
    ( ! [X2,X0] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl5_31 ),
    inference(avatar_component_clause,[],[f603])).

fof(f603,plain,
    ( spl5_31
  <=> ! [X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).

fof(f608,plain,
    ( spl5_31
    | spl5_32 ),
    inference(avatar_split_clause,[],[f75,f606,f603])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_tops_1(X1,X3) = X3
      | ~ v3_pre_topc(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f198,plain,
    ( ~ spl5_7
    | spl5_8
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f188,f125,f195,f191])).

fof(f188,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_5 ),
    inference(superposition,[],[f69,f127])).

fof(f127,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f125])).

fof(f130,plain,
    ( ~ spl5_4
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f129,f125,f121])).

fof(f129,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f68,f127])).

fof(f68,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
      | ~ v3_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
      | v3_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f46,f48,f47])).

fof(f47,plain,
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

fof(f48,plain,
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

fof(f46,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    inference(negated_conjecture,[],[f25])).

fof(f25,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_1)).

fof(f128,plain,
    ( spl5_4
    | spl5_5 ),
    inference(avatar_split_clause,[],[f67,f125,f121])).

fof(f67,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f119,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f66,f116])).

fof(f66,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f49])).

fof(f114,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f65,f111])).

fof(f65,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f109,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f64,f106])).

fof(f64,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f49])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:28:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (27579)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.51  % (27597)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.51  % (27578)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (27577)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (27588)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.52  % (27573)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  % (27596)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (27587)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (27599)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.52  % (27580)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.53  % (27596)Refutation not found, incomplete strategy% (27596)------------------------------
% 0.21/0.53  % (27596)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (27575)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (27596)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (27596)Memory used [KB]: 10746
% 0.21/0.53  % (27596)Time elapsed: 0.115 s
% 0.21/0.53  % (27596)------------------------------
% 0.21/0.53  % (27596)------------------------------
% 0.21/0.53  % (27591)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.24/0.54  % (27585)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.24/0.54  % (27586)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.24/0.54  % (27574)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.24/0.54  % (27594)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.24/0.54  % (27603)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.24/0.54  % (27583)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.24/0.54  % (27576)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.24/0.55  % (27600)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.24/0.55  % (27601)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.24/0.55  % (27602)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.46/0.55  % (27592)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.46/0.55  % (27598)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.46/0.55  % (27593)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.46/0.55  % (27581)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.46/0.55  % (27589)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.46/0.55  % (27591)Refutation not found, incomplete strategy% (27591)------------------------------
% 1.46/0.55  % (27591)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.55  % (27591)Termination reason: Refutation not found, incomplete strategy
% 1.46/0.55  
% 1.46/0.55  % (27591)Memory used [KB]: 10618
% 1.46/0.55  % (27591)Time elapsed: 0.125 s
% 1.46/0.55  % (27591)------------------------------
% 1.46/0.55  % (27591)------------------------------
% 1.46/0.55  % (27582)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.46/0.55  % (27595)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.46/0.56  % (27584)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 2.06/0.64  % (27691)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.06/0.68  % (27699)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 3.31/0.83  % (27578)Time limit reached!
% 3.31/0.83  % (27578)------------------------------
% 3.31/0.83  % (27578)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.31/0.83  % (27578)Termination reason: Time limit
% 3.31/0.83  
% 3.31/0.83  % (27578)Memory used [KB]: 8955
% 3.31/0.83  % (27578)Time elapsed: 0.420 s
% 3.31/0.83  % (27578)------------------------------
% 3.31/0.83  % (27578)------------------------------
% 3.61/0.85  % (27699)Refutation not found, incomplete strategy% (27699)------------------------------
% 3.61/0.85  % (27699)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.61/0.85  % (27699)Termination reason: Refutation not found, incomplete strategy
% 3.61/0.85  
% 3.61/0.85  % (27699)Memory used [KB]: 6268
% 3.61/0.85  % (27699)Time elapsed: 0.268 s
% 3.61/0.85  % (27699)------------------------------
% 3.61/0.85  % (27699)------------------------------
% 3.61/0.91  % (27585)Time limit reached!
% 3.61/0.91  % (27585)------------------------------
% 3.61/0.91  % (27585)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.61/0.92  % (27574)Time limit reached!
% 3.61/0.92  % (27574)------------------------------
% 3.61/0.92  % (27574)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.61/0.92  % (27585)Termination reason: Time limit
% 3.61/0.92  
% 3.61/0.92  % (27585)Memory used [KB]: 9722
% 3.61/0.92  % (27585)Time elapsed: 0.506 s
% 3.61/0.92  % (27585)------------------------------
% 3.61/0.92  % (27585)------------------------------
% 4.27/0.94  % (27583)Time limit reached!
% 4.27/0.94  % (27583)------------------------------
% 4.27/0.94  % (27583)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.27/0.94  % (27583)Termination reason: Time limit
% 4.27/0.94  
% 4.27/0.94  % (27583)Memory used [KB]: 11897
% 4.27/0.94  % (27583)Time elapsed: 0.522 s
% 4.27/0.94  % (27583)------------------------------
% 4.27/0.94  % (27583)------------------------------
% 4.27/0.94  % (27574)Termination reason: Time limit
% 4.27/0.94  % (27574)Termination phase: Saturation
% 4.27/0.94  
% 4.27/0.94  % (27574)Memory used [KB]: 7291
% 4.27/0.94  % (27574)Time elapsed: 0.500 s
% 4.27/0.94  % (27574)------------------------------
% 4.27/0.94  % (27574)------------------------------
% 4.27/0.94  % (27573)Time limit reached!
% 4.27/0.94  % (27573)------------------------------
% 4.27/0.94  % (27573)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.27/0.94  % (27573)Termination reason: Time limit
% 4.27/0.94  
% 4.27/0.94  % (27573)Memory used [KB]: 3837
% 4.27/0.94  % (27573)Time elapsed: 0.527 s
% 4.27/0.94  % (27573)------------------------------
% 4.27/0.94  % (27573)------------------------------
% 4.27/0.96  % (27783)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 4.27/0.98  % (27784)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 4.63/1.02  % (27602)Time limit reached!
% 4.63/1.02  % (27602)------------------------------
% 4.63/1.02  % (27602)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.63/1.02  % (27602)Termination reason: Time limit
% 4.63/1.02  
% 4.63/1.02  % (27602)Memory used [KB]: 8315
% 4.63/1.02  % (27602)Time elapsed: 0.602 s
% 4.63/1.02  % (27602)------------------------------
% 4.63/1.02  % (27602)------------------------------
% 4.63/1.03  % (27589)Time limit reached!
% 4.63/1.03  % (27589)------------------------------
% 4.63/1.03  % (27589)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.63/1.03  % (27589)Termination reason: Time limit
% 4.63/1.03  % (27589)Termination phase: Saturation
% 4.63/1.03  
% 4.63/1.03  % (27589)Memory used [KB]: 16630
% 4.63/1.03  % (27589)Time elapsed: 0.600 s
% 4.63/1.03  % (27589)------------------------------
% 4.63/1.03  % (27589)------------------------------
% 4.63/1.03  % (27786)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 5.05/1.06  % (27785)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 5.05/1.07  % (27788)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 5.48/1.07  % (27787)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 5.48/1.07  % (27580)Time limit reached!
% 5.48/1.07  % (27580)------------------------------
% 5.48/1.07  % (27580)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.48/1.07  % (27580)Termination reason: Time limit
% 5.48/1.07  
% 5.48/1.07  % (27580)Memory used [KB]: 12665
% 5.48/1.07  % (27580)Time elapsed: 0.618 s
% 5.48/1.07  % (27580)------------------------------
% 5.48/1.07  % (27580)------------------------------
% 5.93/1.14  % (27790)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 5.93/1.14  % (27785)Refutation found. Thanks to Tanya!
% 5.93/1.14  % SZS status Theorem for theBenchmark
% 5.93/1.14  % SZS output start Proof for theBenchmark
% 5.93/1.14  fof(f1482,plain,(
% 5.93/1.14    $false),
% 5.93/1.14    inference(avatar_sat_refutation,[],[f109,f114,f119,f128,f130,f198,f608,f625,f732,f770,f988,f1091,f1284,f1307,f1353,f1481])).
% 5.93/1.14  fof(f1481,plain,(
% 5.93/1.14    ~spl5_2 | ~spl5_3 | spl5_5 | ~spl5_19),
% 5.93/1.14    inference(avatar_contradiction_clause,[],[f1480])).
% 5.93/1.14  fof(f1480,plain,(
% 5.93/1.14    $false | (~spl5_2 | ~spl5_3 | spl5_5 | ~spl5_19)),
% 5.93/1.14    inference(subsumption_resolution,[],[f1393,f126])).
% 5.93/1.14  fof(f126,plain,(
% 5.93/1.14    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | spl5_5),
% 5.93/1.14    inference(avatar_component_clause,[],[f125])).
% 5.93/1.14  fof(f125,plain,(
% 5.93/1.14    spl5_5 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)),
% 5.93/1.14    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 5.93/1.14  fof(f1393,plain,(
% 5.93/1.14    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | (~spl5_2 | ~spl5_3 | ~spl5_19)),
% 5.93/1.14    inference(subsumption_resolution,[],[f1392,f113])).
% 5.93/1.14  fof(f113,plain,(
% 5.93/1.14    l1_pre_topc(sK0) | ~spl5_2),
% 5.93/1.14    inference(avatar_component_clause,[],[f111])).
% 5.93/1.14  fof(f111,plain,(
% 5.93/1.14    spl5_2 <=> l1_pre_topc(sK0)),
% 5.93/1.14    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 5.93/1.14  fof(f1392,plain,(
% 5.93/1.14    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~l1_pre_topc(sK0) | (~spl5_3 | ~spl5_19)),
% 5.93/1.14    inference(subsumption_resolution,[],[f1346,f118])).
% 5.93/1.14  fof(f118,plain,(
% 5.93/1.14    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_3),
% 5.93/1.14    inference(avatar_component_clause,[],[f116])).
% 5.93/1.14  fof(f116,plain,(
% 5.93/1.14    spl5_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 5.93/1.14    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 5.93/1.14  fof(f1346,plain,(
% 5.93/1.14    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl5_19),
% 5.93/1.14    inference(superposition,[],[f70,f458])).
% 5.93/1.14  fof(f458,plain,(
% 5.93/1.14    sK1 = k1_tops_1(sK0,sK1) | ~spl5_19),
% 5.93/1.14    inference(avatar_component_clause,[],[f456])).
% 5.93/1.14  fof(f456,plain,(
% 5.93/1.14    spl5_19 <=> sK1 = k1_tops_1(sK0,sK1)),
% 5.93/1.14    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 5.93/1.14  fof(f70,plain,(
% 5.93/1.14    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 5.93/1.14    inference(cnf_transformation,[],[f30])).
% 5.93/1.14  fof(f30,plain,(
% 5.93/1.14    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 5.93/1.14    inference(ennf_transformation,[],[f20])).
% 5.93/1.14  fof(f20,axiom,(
% 5.93/1.14    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 5.93/1.14    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).
% 5.93/1.14  fof(f1353,plain,(
% 5.93/1.14    ~spl5_1 | ~spl5_2 | ~spl5_3 | spl5_4 | ~spl5_19 | ~spl5_38),
% 5.93/1.14    inference(avatar_contradiction_clause,[],[f1352])).
% 5.93/1.14  fof(f1352,plain,(
% 5.93/1.14    $false | (~spl5_1 | ~spl5_2 | ~spl5_3 | spl5_4 | ~spl5_19 | ~spl5_38)),
% 5.93/1.14    inference(subsumption_resolution,[],[f1351,f122])).
% 5.93/1.14  fof(f122,plain,(
% 5.93/1.14    ~v3_pre_topc(sK1,sK0) | spl5_4),
% 5.93/1.14    inference(avatar_component_clause,[],[f121])).
% 5.93/1.14  fof(f121,plain,(
% 5.93/1.14    spl5_4 <=> v3_pre_topc(sK1,sK0)),
% 5.93/1.14    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 5.93/1.14  fof(f1351,plain,(
% 5.93/1.14    v3_pre_topc(sK1,sK0) | (~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_19 | ~spl5_38)),
% 5.93/1.14    inference(subsumption_resolution,[],[f1350,f118])).
% 5.93/1.14  fof(f1350,plain,(
% 5.93/1.14    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(sK1,sK0) | (~spl5_1 | ~spl5_2 | ~spl5_19 | ~spl5_38)),
% 5.93/1.14    inference(subsumption_resolution,[],[f1349,f113])).
% 5.93/1.14  fof(f1349,plain,(
% 5.93/1.14    ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(sK1,sK0) | (~spl5_1 | ~spl5_19 | ~spl5_38)),
% 5.93/1.14    inference(subsumption_resolution,[],[f1347,f108])).
% 5.93/1.14  fof(f108,plain,(
% 5.93/1.14    v2_pre_topc(sK0) | ~spl5_1),
% 5.93/1.14    inference(avatar_component_clause,[],[f106])).
% 5.93/1.14  fof(f106,plain,(
% 5.93/1.14    spl5_1 <=> v2_pre_topc(sK0)),
% 5.93/1.14    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 5.93/1.14  fof(f1347,plain,(
% 5.93/1.14    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(sK1,sK0) | (~spl5_19 | ~spl5_38)),
% 5.93/1.14    inference(trivial_inequality_removal,[],[f1345])).
% 5.93/1.14  fof(f1345,plain,(
% 5.93/1.14    sK1 != sK1 | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(sK1,sK0) | (~spl5_19 | ~spl5_38)),
% 5.93/1.14    inference(superposition,[],[f731,f458])).
% 5.93/1.14  fof(f731,plain,(
% 5.93/1.14    ( ! [X2,X0] : (k1_tops_1(X0,X2) != X2 | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(X2,X0)) ) | ~spl5_38),
% 5.93/1.14    inference(avatar_component_clause,[],[f730])).
% 5.93/1.14  fof(f730,plain,(
% 5.93/1.14    spl5_38 <=> ! [X0,X2] : (v3_pre_topc(X2,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,X2) != X2)),
% 5.93/1.14    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).
% 5.93/1.14  fof(f1307,plain,(
% 5.93/1.14    spl5_19 | ~spl5_2 | ~spl5_3 | ~spl5_67),
% 5.93/1.14    inference(avatar_split_clause,[],[f1305,f1281,f116,f111,f456])).
% 5.93/1.14  fof(f1281,plain,(
% 5.93/1.14    spl5_67 <=> sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 5.93/1.14    introduced(avatar_definition,[new_symbols(naming,[spl5_67])])).
% 5.93/1.14  fof(f1305,plain,(
% 5.93/1.14    sK1 = k1_tops_1(sK0,sK1) | (~spl5_2 | ~spl5_3 | ~spl5_67)),
% 5.93/1.14    inference(subsumption_resolution,[],[f1304,f113])).
% 5.93/1.14  fof(f1304,plain,(
% 5.93/1.14    sK1 = k1_tops_1(sK0,sK1) | ~l1_pre_topc(sK0) | (~spl5_3 | ~spl5_67)),
% 5.93/1.14    inference(subsumption_resolution,[],[f1285,f118])).
% 5.93/1.14  fof(f1285,plain,(
% 5.93/1.14    sK1 = k1_tops_1(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl5_67),
% 5.93/1.14    inference(superposition,[],[f1283,f398])).
% 5.93/1.14  fof(f398,plain,(
% 5.93/1.14    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 5.93/1.14    inference(duplicate_literal_removal,[],[f397])).
% 5.93/1.14  fof(f397,plain,(
% 5.93/1.14    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 5.93/1.14    inference(superposition,[],[f69,f71])).
% 5.93/1.14  fof(f71,plain,(
% 5.93/1.14    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 5.93/1.14    inference(cnf_transformation,[],[f31])).
% 5.93/1.14  fof(f31,plain,(
% 5.93/1.14    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 5.93/1.14    inference(ennf_transformation,[],[f24])).
% 5.93/1.14  fof(f24,axiom,(
% 5.93/1.14    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 5.93/1.14    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).
% 5.93/1.14  fof(f69,plain,(
% 5.93/1.14    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 5.93/1.14    inference(cnf_transformation,[],[f29])).
% 5.93/1.14  fof(f29,plain,(
% 5.93/1.14    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 5.93/1.14    inference(ennf_transformation,[],[f16])).
% 5.93/1.14  fof(f16,axiom,(
% 5.93/1.14    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 5.93/1.14    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 5.93/1.14  fof(f1283,plain,(
% 5.93/1.14    sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl5_67),
% 5.93/1.14    inference(avatar_component_clause,[],[f1281])).
% 5.93/1.14  fof(f1284,plain,(
% 5.93/1.14    spl5_67 | ~spl5_8),
% 5.93/1.14    inference(avatar_split_clause,[],[f1278,f195,f1281])).
% 5.93/1.14  fof(f195,plain,(
% 5.93/1.14    spl5_8 <=> k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)),
% 5.93/1.14    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 5.93/1.14  fof(f1278,plain,(
% 5.93/1.14    sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl5_8),
% 5.93/1.14    inference(duplicate_literal_removal,[],[f1273])).
% 5.93/1.14  fof(f1273,plain,(
% 5.93/1.14    sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl5_8),
% 5.93/1.14    inference(resolution,[],[f1119,f296])).
% 5.93/1.14  fof(f296,plain,(
% 5.93/1.14    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1,X0),X0) | k4_xboole_0(X0,X1) = X0) )),
% 5.93/1.14    inference(factoring,[],[f80])).
% 5.93/1.14  fof(f80,plain,(
% 5.93/1.14    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,X1,X2),X2) | r2_hidden(sK2(X0,X1,X2),X0) | k4_xboole_0(X0,X1) = X2) )),
% 5.93/1.14    inference(cnf_transformation,[],[f54])).
% 5.93/1.14  fof(f54,plain,(
% 5.93/1.14    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 5.93/1.14    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f52,f53])).
% 5.93/1.14  fof(f53,plain,(
% 5.93/1.14    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 5.93/1.14    introduced(choice_axiom,[])).
% 5.93/1.15  fof(f52,plain,(
% 5.93/1.15    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 5.93/1.15    inference(rectify,[],[f51])).
% 5.93/1.15  fof(f51,plain,(
% 5.93/1.15    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 5.93/1.15    inference(flattening,[],[f50])).
% 5.93/1.15  fof(f50,plain,(
% 5.93/1.15    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 5.93/1.15    inference(nnf_transformation,[],[f2])).
% 5.93/1.15  fof(f2,axiom,(
% 5.93/1.15    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 5.93/1.15    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 5.93/1.16  fof(f1119,plain,(
% 5.93/1.16    ( ! [X1] : (~r2_hidden(sK2(X1,k2_tops_1(sK0,sK1),X1),sK1) | k4_xboole_0(X1,k2_tops_1(sK0,sK1)) = X1) ) | ~spl5_8),
% 5.93/1.16    inference(resolution,[],[f1107,f529])).
% 5.93/1.16  fof(f529,plain,(
% 5.93/1.16    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1,X0),X1) | k4_xboole_0(X0,X1) = X0) )),
% 5.93/1.16    inference(subsumption_resolution,[],[f528,f80])).
% 5.93/1.16  fof(f528,plain,(
% 5.93/1.16    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1,X0),X1) | ~r2_hidden(sK2(X0,X1,X0),X0) | k4_xboole_0(X0,X1) = X0) )),
% 5.93/1.16    inference(duplicate_literal_removal,[],[f520])).
% 5.93/1.16  fof(f520,plain,(
% 5.93/1.16    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1,X0),X1) | ~r2_hidden(sK2(X0,X1,X0),X0) | k4_xboole_0(X0,X1) = X0 | k4_xboole_0(X0,X1) = X0) )),
% 5.93/1.16    inference(resolution,[],[f82,f296])).
% 5.93/1.16  fof(f82,plain,(
% 5.93/1.16    ( ! [X2,X0,X1] : (~r2_hidden(sK2(X0,X1,X2),X2) | r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | k4_xboole_0(X0,X1) = X2) )),
% 5.93/1.16    inference(cnf_transformation,[],[f54])).
% 5.93/1.16  fof(f1107,plain,(
% 5.93/1.16    ( ! [X1] : (~r2_hidden(X1,k2_tops_1(sK0,sK1)) | ~r2_hidden(X1,sK1)) ) | ~spl5_8),
% 5.93/1.16    inference(superposition,[],[f100,f197])).
% 5.93/1.16  fof(f197,plain,(
% 5.93/1.16    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~spl5_8),
% 5.93/1.16    inference(avatar_component_clause,[],[f195])).
% 5.93/1.16  fof(f100,plain,(
% 5.93/1.16    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 5.93/1.16    inference(equality_resolution,[],[f78])).
% 5.93/1.16  fof(f78,plain,(
% 5.93/1.16    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 5.93/1.16    inference(cnf_transformation,[],[f54])).
% 5.93/1.16  fof(f1091,plain,(
% 5.93/1.16    ~spl5_2 | ~spl5_3 | spl5_7),
% 5.93/1.16    inference(avatar_contradiction_clause,[],[f1090])).
% 5.93/1.16  fof(f1090,plain,(
% 5.93/1.16    $false | (~spl5_2 | ~spl5_3 | spl5_7)),
% 5.93/1.16    inference(subsumption_resolution,[],[f1089,f113])).
% 5.93/1.16  fof(f1089,plain,(
% 5.93/1.16    ~l1_pre_topc(sK0) | (~spl5_3 | spl5_7)),
% 5.93/1.16    inference(subsumption_resolution,[],[f1079,f118])).
% 5.93/1.16  fof(f1079,plain,(
% 5.93/1.16    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl5_7),
% 5.93/1.16    inference(resolution,[],[f449,f193])).
% 5.93/1.16  fof(f193,plain,(
% 5.93/1.16    ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl5_7),
% 5.93/1.16    inference(avatar_component_clause,[],[f191])).
% 5.93/1.16  fof(f191,plain,(
% 5.93/1.16    spl5_7 <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 5.93/1.16    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 5.93/1.16  fof(f449,plain,(
% 5.93/1.16    ( ! [X2,X3] : (m1_subset_1(k2_pre_topc(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2)) )),
% 5.93/1.16    inference(subsumption_resolution,[],[f444,f73])).
% 5.93/1.16  fof(f73,plain,(
% 5.93/1.16    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 5.93/1.16    inference(cnf_transformation,[],[f34])).
% 5.93/1.16  fof(f34,plain,(
% 5.93/1.16    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 5.93/1.16    inference(flattening,[],[f33])).
% 5.93/1.16  fof(f33,plain,(
% 5.93/1.16    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 5.93/1.16    inference(ennf_transformation,[],[f19])).
% 5.93/1.16  fof(f19,axiom,(
% 5.93/1.16    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 5.93/1.16    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 5.93/1.16  fof(f444,plain,(
% 5.93/1.16    ( ! [X2,X3] : (m1_subset_1(k2_pre_topc(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) | ~m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2)) )),
% 5.93/1.16    inference(duplicate_literal_removal,[],[f443])).
% 5.93/1.16  fof(f443,plain,(
% 5.93/1.16    ( ! [X2,X3] : (m1_subset_1(k2_pre_topc(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) | ~m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2)) )),
% 5.93/1.16    inference(superposition,[],[f85,f72])).
% 5.93/1.16  fof(f72,plain,(
% 5.93/1.16    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 5.93/1.16    inference(cnf_transformation,[],[f32])).
% 5.93/1.16  fof(f32,plain,(
% 5.93/1.16    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 5.93/1.16    inference(ennf_transformation,[],[f23])).
% 5.93/1.16  fof(f23,axiom,(
% 5.93/1.16    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 5.93/1.16    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).
% 5.93/1.16  fof(f85,plain,(
% 5.93/1.16    ( ! [X2,X0,X1] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 5.93/1.16    inference(cnf_transformation,[],[f40])).
% 5.93/1.16  fof(f40,plain,(
% 5.93/1.16    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 5.93/1.16    inference(flattening,[],[f39])).
% 5.93/1.16  fof(f39,plain,(
% 5.93/1.16    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 5.93/1.16    inference(ennf_transformation,[],[f14])).
% 5.93/1.16  fof(f14,axiom,(
% 5.93/1.16    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 5.93/1.16    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).
% 5.93/1.16  fof(f988,plain,(
% 5.93/1.16    spl5_19 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_32),
% 5.93/1.16    inference(avatar_split_clause,[],[f987,f606,f121,f116,f111,f456])).
% 5.93/1.16  fof(f606,plain,(
% 5.93/1.16    spl5_32 <=> ! [X1,X3] : (k1_tops_1(X1,X3) = X3 | ~l1_pre_topc(X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~v3_pre_topc(X3,X1))),
% 5.93/1.16    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).
% 5.93/1.16  fof(f987,plain,(
% 5.93/1.16    sK1 = k1_tops_1(sK0,sK1) | (~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_32)),
% 5.93/1.16    inference(subsumption_resolution,[],[f867,f123])).
% 5.93/1.16  fof(f123,plain,(
% 5.93/1.16    v3_pre_topc(sK1,sK0) | ~spl5_4),
% 5.93/1.16    inference(avatar_component_clause,[],[f121])).
% 5.93/1.16  fof(f867,plain,(
% 5.93/1.16    sK1 = k1_tops_1(sK0,sK1) | ~v3_pre_topc(sK1,sK0) | (~spl5_2 | ~spl5_3 | ~spl5_32)),
% 5.93/1.16    inference(subsumption_resolution,[],[f688,f113])).
% 5.93/1.16  fof(f688,plain,(
% 5.93/1.16    ~l1_pre_topc(sK0) | sK1 = k1_tops_1(sK0,sK1) | ~v3_pre_topc(sK1,sK0) | (~spl5_3 | ~spl5_32)),
% 5.93/1.16    inference(resolution,[],[f607,f118])).
% 5.93/1.16  fof(f607,plain,(
% 5.93/1.16    ( ! [X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1)) ) | ~spl5_32),
% 5.93/1.16    inference(avatar_component_clause,[],[f606])).
% 5.93/1.16  fof(f770,plain,(
% 5.93/1.16    ~spl5_2 | ~spl5_3 | ~spl5_37),
% 5.93/1.16    inference(avatar_contradiction_clause,[],[f769])).
% 5.93/1.16  fof(f769,plain,(
% 5.93/1.16    $false | (~spl5_2 | ~spl5_3 | ~spl5_37)),
% 5.93/1.16    inference(subsumption_resolution,[],[f765,f113])).
% 5.93/1.16  fof(f765,plain,(
% 5.93/1.16    ~l1_pre_topc(sK0) | (~spl5_3 | ~spl5_37)),
% 5.93/1.16    inference(resolution,[],[f728,f118])).
% 5.93/1.16  fof(f728,plain,(
% 5.93/1.16    ( ! [X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1)) ) | ~spl5_37),
% 5.93/1.16    inference(avatar_component_clause,[],[f727])).
% 5.93/1.16  fof(f727,plain,(
% 5.93/1.16    spl5_37 <=> ! [X1,X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1))),
% 5.93/1.16    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).
% 5.93/1.16  fof(f732,plain,(
% 5.93/1.16    spl5_37 | spl5_38),
% 5.93/1.16    inference(avatar_split_clause,[],[f76,f730,f727])).
% 5.93/1.16  fof(f76,plain,(
% 5.93/1.16    ( ! [X2,X0,X3,X1] : (v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 5.93/1.16    inference(cnf_transformation,[],[f37])).
% 5.93/1.16  fof(f37,plain,(
% 5.93/1.16    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 5.93/1.16    inference(flattening,[],[f36])).
% 5.93/1.16  fof(f36,plain,(
% 5.93/1.16    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 5.93/1.16    inference(ennf_transformation,[],[f21])).
% 5.93/1.16  fof(f21,axiom,(
% 5.93/1.16    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((k1_tops_1(X0,X2) = X2 => v3_pre_topc(X2,X0)) & (v3_pre_topc(X3,X1) => k1_tops_1(X1,X3) = X3))))))),
% 5.93/1.16    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tops_1)).
% 5.93/1.16  fof(f625,plain,(
% 5.93/1.16    ~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_31),
% 5.93/1.16    inference(avatar_contradiction_clause,[],[f624])).
% 5.93/1.16  fof(f624,plain,(
% 5.93/1.16    $false | (~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_31)),
% 5.93/1.16    inference(subsumption_resolution,[],[f623,f113])).
% 5.93/1.16  fof(f623,plain,(
% 5.93/1.16    ~l1_pre_topc(sK0) | (~spl5_1 | ~spl5_3 | ~spl5_31)),
% 5.93/1.16    inference(subsumption_resolution,[],[f619,f108])).
% 5.93/1.16  fof(f619,plain,(
% 5.93/1.16    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | (~spl5_3 | ~spl5_31)),
% 5.93/1.16    inference(resolution,[],[f604,f118])).
% 5.93/1.16  fof(f604,plain,(
% 5.93/1.16    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0)) ) | ~spl5_31),
% 5.93/1.16    inference(avatar_component_clause,[],[f603])).
% 5.93/1.16  fof(f603,plain,(
% 5.93/1.16    spl5_31 <=> ! [X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0))),
% 5.93/1.16    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).
% 5.93/1.16  fof(f608,plain,(
% 5.93/1.16    spl5_31 | spl5_32),
% 5.93/1.16    inference(avatar_split_clause,[],[f75,f606,f603])).
% 5.93/1.16  fof(f75,plain,(
% 5.93/1.16    ( ! [X2,X0,X3,X1] : (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 5.93/1.16    inference(cnf_transformation,[],[f37])).
% 5.93/1.16  fof(f198,plain,(
% 5.93/1.16    ~spl5_7 | spl5_8 | ~spl5_5),
% 5.93/1.16    inference(avatar_split_clause,[],[f188,f125,f195,f191])).
% 5.93/1.16  fof(f188,plain,(
% 5.93/1.16    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_5),
% 5.93/1.16    inference(superposition,[],[f69,f127])).
% 5.93/1.16  fof(f127,plain,(
% 5.93/1.16    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~spl5_5),
% 5.93/1.16    inference(avatar_component_clause,[],[f125])).
% 5.93/1.16  fof(f130,plain,(
% 5.93/1.16    ~spl5_4 | ~spl5_5),
% 5.93/1.16    inference(avatar_split_clause,[],[f129,f125,f121])).
% 5.93/1.16  fof(f129,plain,(
% 5.93/1.16    ~v3_pre_topc(sK1,sK0) | ~spl5_5),
% 5.93/1.16    inference(subsumption_resolution,[],[f68,f127])).
% 5.93/1.16  fof(f68,plain,(
% 5.93/1.16    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)),
% 5.93/1.16    inference(cnf_transformation,[],[f49])).
% 5.93/1.16  fof(f49,plain,(
% 5.93/1.16    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 5.93/1.16    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f46,f48,f47])).
% 5.93/1.16  fof(f47,plain,(
% 5.93/1.16    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | ~v3_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 5.93/1.16    introduced(choice_axiom,[])).
% 5.93/1.16  fof(f48,plain,(
% 5.93/1.16    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | ~v3_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 5.93/1.16    introduced(choice_axiom,[])).
% 5.93/1.16  fof(f46,plain,(
% 5.93/1.16    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 5.93/1.16    inference(flattening,[],[f45])).
% 5.93/1.16  fof(f45,plain,(
% 5.93/1.16    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 5.93/1.16    inference(nnf_transformation,[],[f28])).
% 5.93/1.16  fof(f28,plain,(
% 5.93/1.16    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 5.93/1.16    inference(flattening,[],[f27])).
% 5.93/1.16  fof(f27,plain,(
% 5.93/1.16    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 5.93/1.16    inference(ennf_transformation,[],[f26])).
% 5.93/1.16  fof(f26,negated_conjecture,(
% 5.93/1.16    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 5.93/1.16    inference(negated_conjecture,[],[f25])).
% 5.93/1.16  fof(f25,conjecture,(
% 5.93/1.16    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 5.93/1.16    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_1)).
% 5.93/1.16  fof(f128,plain,(
% 5.93/1.16    spl5_4 | spl5_5),
% 5.93/1.16    inference(avatar_split_clause,[],[f67,f125,f121])).
% 5.93/1.16  fof(f67,plain,(
% 5.93/1.16    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)),
% 5.93/1.16    inference(cnf_transformation,[],[f49])).
% 5.93/1.16  fof(f119,plain,(
% 5.93/1.16    spl5_3),
% 5.93/1.16    inference(avatar_split_clause,[],[f66,f116])).
% 5.93/1.16  fof(f66,plain,(
% 5.93/1.16    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 5.93/1.16    inference(cnf_transformation,[],[f49])).
% 5.93/1.16  fof(f114,plain,(
% 5.93/1.16    spl5_2),
% 5.93/1.16    inference(avatar_split_clause,[],[f65,f111])).
% 5.93/1.16  fof(f65,plain,(
% 5.93/1.16    l1_pre_topc(sK0)),
% 5.93/1.16    inference(cnf_transformation,[],[f49])).
% 5.93/1.16  fof(f109,plain,(
% 5.93/1.16    spl5_1),
% 5.93/1.16    inference(avatar_split_clause,[],[f64,f106])).
% 5.93/1.16  fof(f64,plain,(
% 5.93/1.16    v2_pre_topc(sK0)),
% 5.93/1.16    inference(cnf_transformation,[],[f49])).
% 5.93/1.16  % SZS output end Proof for theBenchmark
% 5.93/1.16  % (27785)------------------------------
% 5.93/1.16  % (27785)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.93/1.16  % (27785)Termination reason: Refutation
% 5.93/1.16  
% 5.93/1.16  % (27785)Memory used [KB]: 11769
% 5.93/1.16  % (27785)Time elapsed: 0.205 s
% 5.93/1.16  % (27785)------------------------------
% 5.93/1.16  % (27785)------------------------------
% 5.93/1.16  % (27569)Success in time 0.787 s
%------------------------------------------------------------------------------
