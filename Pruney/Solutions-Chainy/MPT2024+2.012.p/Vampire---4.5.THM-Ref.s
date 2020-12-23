%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:10 EST 2020

% Result     : Theorem 1.60s
% Output     : Refutation 2.03s
% Verified   : 
% Statistics : Number of formulae       :  207 ( 507 expanded)
%              Number of leaves         :   48 ( 240 expanded)
%              Depth                    :   12
%              Number of atoms          :  910 (2008 expanded)
%              Number of equality atoms :   21 (  27 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2726,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f100,f105,f110,f115,f120,f125,f130,f192,f226,f261,f292,f300,f622,f661,f662,f733,f738,f794,f1043,f1059,f1071,f1080,f1459,f1601,f1990,f1998,f2704,f2725])).

fof(f2725,plain,(
    ~ spl5_224 ),
    inference(avatar_contradiction_clause,[],[f2724])).

fof(f2724,plain,
    ( $false
    | ~ spl5_224 ),
    inference(subsumption_resolution,[],[f2711,f60])).

fof(f60,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f2711,plain,
    ( ~ r1_tarski(k1_xboole_0,sK1)
    | ~ spl5_224 ),
    inference(unit_resulting_resolution,[],[f2703,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f2703,plain,
    ( r2_hidden(sK1,k1_xboole_0)
    | ~ spl5_224 ),
    inference(avatar_component_clause,[],[f2701])).

fof(f2701,plain,
    ( spl5_224
  <=> r2_hidden(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_224])])).

fof(f2704,plain,
    ( spl5_224
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | spl5_7
    | ~ spl5_162
    | ~ spl5_163 ),
    inference(avatar_split_clause,[],[f2568,f1995,f1982,f127,f122,f117,f112,f2701])).

fof(f112,plain,
    ( spl5_4
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f117,plain,
    ( spl5_5
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f122,plain,
    ( spl5_6
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f127,plain,
    ( spl5_7
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f1982,plain,
    ( spl5_162
  <=> m1_connsp_2(k1_xboole_0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_162])])).

fof(f1995,plain,
    ( spl5_163
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_163])])).

fof(f2568,plain,
    ( r2_hidden(sK1,k1_xboole_0)
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | spl5_7
    | ~ spl5_162
    | ~ spl5_163 ),
    inference(unit_resulting_resolution,[],[f129,f124,f119,f114,f1984,f1997,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ m1_connsp_2(X1,X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,X1)
              | ~ m1_connsp_2(X1,X0,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,X1)
              | ~ m1_connsp_2(X1,X0,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( m1_connsp_2(X1,X0,X2)
               => r2_hidden(X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_connsp_2)).

fof(f1997,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_163 ),
    inference(avatar_component_clause,[],[f1995])).

fof(f1984,plain,
    ( m1_connsp_2(k1_xboole_0,sK0,sK1)
    | ~ spl5_162 ),
    inference(avatar_component_clause,[],[f1982])).

fof(f114,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f112])).

fof(f119,plain,
    ( l1_pre_topc(sK0)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f117])).

fof(f124,plain,
    ( v2_pre_topc(sK0)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f122])).

fof(f129,plain,
    ( ~ v2_struct_0(sK0)
    | spl5_7 ),
    inference(avatar_component_clause,[],[f127])).

fof(f1998,plain,
    ( spl5_163
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | spl5_7
    | ~ spl5_162 ),
    inference(avatar_split_clause,[],[f1991,f1982,f127,f122,f117,f112,f1995])).

fof(f1991,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | spl5_7
    | ~ spl5_162 ),
    inference(unit_resulting_resolution,[],[f129,f124,f119,f114,f1984,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_connsp_2)).

fof(f1990,plain,
    ( spl5_162
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | spl5_7
    | ~ spl5_127 ),
    inference(avatar_split_clause,[],[f1989,f1598,f127,f122,f117,f112,f1982])).

fof(f1598,plain,
    ( spl5_127
  <=> m1_subset_1(k1_xboole_0,u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_127])])).

fof(f1989,plain,
    ( m1_connsp_2(k1_xboole_0,sK0,sK1)
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | spl5_7
    | ~ spl5_127 ),
    inference(subsumption_resolution,[],[f1988,f129])).

fof(f1988,plain,
    ( m1_connsp_2(k1_xboole_0,sK0,sK1)
    | v2_struct_0(sK0)
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_127 ),
    inference(subsumption_resolution,[],[f1987,f124])).

fof(f1987,plain,
    ( m1_connsp_2(k1_xboole_0,sK0,sK1)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_127 ),
    inference(subsumption_resolution,[],[f1986,f119])).

fof(f1986,plain,
    ( m1_connsp_2(k1_xboole_0,sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_4
    | ~ spl5_127 ),
    inference(subsumption_resolution,[],[f1972,f114])).

fof(f1972,plain,
    ( m1_connsp_2(k1_xboole_0,sK0,sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_127 ),
    inference(resolution,[],[f1600,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X2,X0,X1)
              | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X2,X0,X1)
              | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
             => m1_connsp_2(X2,X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_waybel_9)).

fof(f1600,plain,
    ( m1_subset_1(k1_xboole_0,u1_struct_0(k9_yellow_6(sK0,sK1)))
    | ~ spl5_127 ),
    inference(avatar_component_clause,[],[f1598])).

fof(f1601,plain,
    ( spl5_127
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f1564,f194,f1598])).

fof(f194,plain,
    ( spl5_12
  <=> v1_xboole_0(u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f1564,plain,
    ( m1_subset_1(k1_xboole_0,u1_struct_0(k9_yellow_6(sK0,sK1)))
    | ~ spl5_12 ),
    inference(unit_resulting_resolution,[],[f59,f196,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f196,plain,
    ( v1_xboole_0(u1_struct_0(k9_yellow_6(sK0,sK1)))
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f194])).

fof(f59,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f1459,plain,
    ( ~ spl5_30
    | spl5_51 ),
    inference(avatar_contradiction_clause,[],[f1458])).

fof(f1458,plain,
    ( $false
    | ~ spl5_30
    | spl5_51 ),
    inference(subsumption_resolution,[],[f1442,f391])).

fof(f391,plain,
    ( r2_hidden(sK1,sK2)
    | ~ spl5_30 ),
    inference(avatar_component_clause,[],[f389])).

fof(f389,plain,
    ( spl5_30
  <=> r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f1442,plain,
    ( ~ r2_hidden(sK1,sK2)
    | spl5_51 ),
    inference(resolution,[],[f789,f94])).

fof(f94,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_tarski(k2_tarski(X0,X1)))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f91])).

fof(f91,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k3_tarski(k2_tarski(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f79,f66])).

fof(f66,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f79,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
              & ~ r2_hidden(sK4(X0,X1,X2),X0) )
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( r2_hidden(sK4(X0,X1,X2),X1)
            | r2_hidden(sK4(X0,X1,X2),X0)
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f49,f50])).

fof(f50,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
            & ~ r2_hidden(sK4(X0,X1,X2),X0) )
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( r2_hidden(sK4(X0,X1,X2),X1)
          | r2_hidden(sK4(X0,X1,X2),X0)
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f789,plain,
    ( ~ r2_hidden(sK1,k3_tarski(k2_tarski(sK2,sK3)))
    | spl5_51 ),
    inference(avatar_component_clause,[],[f787])).

fof(f787,plain,
    ( spl5_51
  <=> r2_hidden(sK1,k3_tarski(k2_tarski(sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_51])])).

fof(f1080,plain,
    ( k3_tarski(k2_tarski(sK2,sK3)) != k4_subset_1(u1_struct_0(sK0),sK2,sK3)
    | ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k3_tarski(k2_tarski(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1071,plain,
    ( spl5_52
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_22
    | ~ spl5_23
    | ~ spl5_28
    | ~ spl5_31 ),
    inference(avatar_split_clause,[],[f998,f398,f361,f297,f289,f122,f117,f791])).

fof(f791,plain,
    ( spl5_52
  <=> v3_pre_topc(k3_tarski(k2_tarski(sK2,sK3)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_52])])).

fof(f289,plain,
    ( spl5_22
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f297,plain,
    ( spl5_23
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f361,plain,
    ( spl5_28
  <=> v3_pre_topc(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).

fof(f398,plain,
    ( spl5_31
  <=> v3_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).

fof(f998,plain,
    ( v3_pre_topc(k3_tarski(k2_tarski(sK2,sK3)),sK0)
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_22
    | ~ spl5_23
    | ~ spl5_28
    | ~ spl5_31 ),
    inference(unit_resulting_resolution,[],[f124,f119,f400,f363,f291,f299,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(k3_tarski(k2_tarski(X1,X2)),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(definition_unfolding,[],[f74,f66])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(k2_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v3_pre_topc(k2_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( v3_pre_topc(k2_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        & v3_pre_topc(X2,X0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & v3_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k2_xboole_0(X1,X2),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_tops_1)).

fof(f299,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_23 ),
    inference(avatar_component_clause,[],[f297])).

fof(f291,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_22 ),
    inference(avatar_component_clause,[],[f289])).

fof(f363,plain,
    ( v3_pre_topc(sK3,sK0)
    | ~ spl5_28 ),
    inference(avatar_component_clause,[],[f361])).

fof(f400,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ spl5_31 ),
    inference(avatar_component_clause,[],[f398])).

fof(f1059,plain,
    ( spl5_78
    | ~ spl5_22
    | ~ spl5_23 ),
    inference(avatar_split_clause,[],[f1006,f297,f289,f1056])).

fof(f1056,plain,
    ( spl5_78
  <=> k3_tarski(k2_tarski(sK2,sK3)) = k4_subset_1(u1_struct_0(sK0),sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_78])])).

fof(f1006,plain,
    ( k3_tarski(k2_tarski(sK2,sK3)) = k4_subset_1(u1_struct_0(sK0),sK2,sK3)
    | ~ spl5_22
    | ~ spl5_23 ),
    inference(unit_resulting_resolution,[],[f291,f299,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f77,f66])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f1043,plain,
    ( spl5_75
    | ~ spl5_22
    | ~ spl5_23 ),
    inference(avatar_split_clause,[],[f1010,f297,f289,f1040])).

fof(f1040,plain,
    ( spl5_75
  <=> m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_75])])).

fof(f1010,plain,
    ( m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_22
    | ~ spl5_23 ),
    inference(unit_resulting_resolution,[],[f291,f299,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).

fof(f794,plain,
    ( ~ spl5_50
    | ~ spl5_51
    | ~ spl5_52
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | spl5_7
    | spl5_19 ),
    inference(avatar_split_clause,[],[f781,f257,f127,f122,f117,f112,f791,f787,f783])).

fof(f783,plain,
    ( spl5_50
  <=> m1_subset_1(k3_tarski(k2_tarski(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_50])])).

fof(f257,plain,
    ( spl5_19
  <=> r2_hidden(k3_tarski(k2_tarski(sK2,sK3)),u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f781,plain,
    ( ~ v3_pre_topc(k3_tarski(k2_tarski(sK2,sK3)),sK0)
    | ~ r2_hidden(sK1,k3_tarski(k2_tarski(sK2,sK3)))
    | ~ m1_subset_1(k3_tarski(k2_tarski(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | spl5_7
    | spl5_19 ),
    inference(subsumption_resolution,[],[f780,f129])).

fof(f780,plain,
    ( ~ v3_pre_topc(k3_tarski(k2_tarski(sK2,sK3)),sK0)
    | ~ r2_hidden(sK1,k3_tarski(k2_tarski(sK2,sK3)))
    | ~ m1_subset_1(k3_tarski(k2_tarski(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | spl5_19 ),
    inference(subsumption_resolution,[],[f779,f124])).

fof(f779,plain,
    ( ~ v3_pre_topc(k3_tarski(k2_tarski(sK2,sK3)),sK0)
    | ~ r2_hidden(sK1,k3_tarski(k2_tarski(sK2,sK3)))
    | ~ m1_subset_1(k3_tarski(k2_tarski(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_4
    | ~ spl5_5
    | spl5_19 ),
    inference(subsumption_resolution,[],[f778,f119])).

fof(f778,plain,
    ( ~ v3_pre_topc(k3_tarski(k2_tarski(sK2,sK3)),sK0)
    | ~ r2_hidden(sK1,k3_tarski(k2_tarski(sK2,sK3)))
    | ~ m1_subset_1(k3_tarski(k2_tarski(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_4
    | spl5_19 ),
    inference(subsumption_resolution,[],[f763,f114])).

fof(f763,plain,
    ( ~ v3_pre_topc(k3_tarski(k2_tarski(sK2,sK3)),sK0)
    | ~ r2_hidden(sK1,k3_tarski(k2_tarski(sK2,sK3)))
    | ~ m1_subset_1(k3_tarski(k2_tarski(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl5_19 ),
    inference(resolution,[],[f259,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ v3_pre_topc(X2,X0)
      | ~ r2_hidden(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
                  | ~ v3_pre_topc(X2,X0)
                  | ~ r2_hidden(X1,X2) )
                & ( ( v3_pre_topc(X2,X0)
                    & r2_hidden(X1,X2) )
                  | ~ r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
                  | ~ v3_pre_topc(X2,X0)
                  | ~ r2_hidden(X1,X2) )
                & ( ( v3_pre_topc(X2,X0)
                    & r2_hidden(X1,X2) )
                  | ~ r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
              <=> ( v3_pre_topc(X2,X0)
                  & r2_hidden(X1,X2) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
              <=> ( v3_pre_topc(X2,X0)
                  & r2_hidden(X1,X2) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
              <=> ( v3_pre_topc(X2,X0)
                  & r2_hidden(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_yellow_6)).

fof(f259,plain,
    ( ~ r2_hidden(k3_tarski(k2_tarski(sK2,sK3)),u1_struct_0(k9_yellow_6(sK0,sK1)))
    | spl5_19 ),
    inference(avatar_component_clause,[],[f257])).

fof(f738,plain,
    ( ~ spl5_23
    | spl5_31
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | spl5_7
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f737,f228,f127,f122,f117,f112,f398,f297])).

fof(f228,plain,
    ( spl5_16
  <=> r2_hidden(sK2,u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f737,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | spl5_7
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f736,f129])).

fof(f736,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f735,f124])).

fof(f735,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f734,f119])).

fof(f734,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_4
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f720,f114])).

fof(f720,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_16 ),
    inference(resolution,[],[f230,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(X2,X0)
      | ~ r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f230,plain,
    ( r2_hidden(sK2,u1_struct_0(k9_yellow_6(sK0,sK1)))
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f228])).

fof(f733,plain,
    ( ~ spl5_23
    | spl5_30
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | spl5_7
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f732,f228,f127,f122,f117,f112,f389,f297])).

fof(f732,plain,
    ( r2_hidden(sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | spl5_7
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f731,f129])).

fof(f731,plain,
    ( r2_hidden(sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f730,f124])).

fof(f730,plain,
    ( r2_hidden(sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f729,f119])).

fof(f729,plain,
    ( r2_hidden(sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_4
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f719,f114])).

fof(f719,plain,
    ( r2_hidden(sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_16 ),
    inference(resolution,[],[f230,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | ~ r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f662,plain,
    ( spl5_13
    | ~ spl5_2
    | spl5_12 ),
    inference(avatar_split_clause,[],[f646,f194,f102,f198])).

fof(f198,plain,
    ( spl5_13
  <=> r2_hidden(sK3,u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f102,plain,
    ( spl5_2
  <=> m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f646,plain,
    ( r2_hidden(sK3,u1_struct_0(k9_yellow_6(sK0,sK1)))
    | ~ spl5_2
    | spl5_12 ),
    inference(unit_resulting_resolution,[],[f104,f195,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f195,plain,
    ( ~ v1_xboole_0(u1_struct_0(k9_yellow_6(sK0,sK1)))
    | spl5_12 ),
    inference(avatar_component_clause,[],[f194])).

fof(f104,plain,
    ( m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK0,sK1)))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f102])).

fof(f661,plain,
    ( spl5_16
    | ~ spl5_3
    | spl5_12 ),
    inference(avatar_split_clause,[],[f647,f194,f107,f228])).

fof(f107,plain,
    ( spl5_3
  <=> m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f647,plain,
    ( r2_hidden(sK2,u1_struct_0(k9_yellow_6(sK0,sK1)))
    | ~ spl5_3
    | spl5_12 ),
    inference(unit_resulting_resolution,[],[f109,f195,f67])).

fof(f109,plain,
    ( m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1)))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f107])).

fof(f622,plain,
    ( ~ spl5_22
    | spl5_28
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | spl5_7
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f621,f198,f127,f122,f117,f112,f361,f289])).

fof(f621,plain,
    ( v3_pre_topc(sK3,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | spl5_7
    | ~ spl5_13 ),
    inference(subsumption_resolution,[],[f620,f129])).

fof(f620,plain,
    ( v3_pre_topc(sK3,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_13 ),
    inference(subsumption_resolution,[],[f619,f124])).

fof(f619,plain,
    ( v3_pre_topc(sK3,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_13 ),
    inference(subsumption_resolution,[],[f618,f119])).

fof(f618,plain,
    ( v3_pre_topc(sK3,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_4
    | ~ spl5_13 ),
    inference(subsumption_resolution,[],[f334,f114])).

fof(f334,plain,
    ( v3_pre_topc(sK3,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_13 ),
    inference(resolution,[],[f200,f62])).

fof(f200,plain,
    ( r2_hidden(sK3,u1_struct_0(k9_yellow_6(sK0,sK1)))
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f198])).

fof(f300,plain,
    ( spl5_23
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | spl5_7
    | ~ spl5_15 ),
    inference(avatar_split_clause,[],[f293,f218,f127,f122,f117,f112,f297])).

fof(f218,plain,
    ( spl5_15
  <=> m1_connsp_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f293,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | spl5_7
    | ~ spl5_15 ),
    inference(unit_resulting_resolution,[],[f129,f124,f119,f114,f220,f72])).

fof(f220,plain,
    ( m1_connsp_2(sK2,sK0,sK1)
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f218])).

fof(f292,plain,
    ( spl5_22
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | spl5_7
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f285,f184,f127,f122,f117,f112,f289])).

fof(f184,plain,
    ( spl5_11
  <=> m1_connsp_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f285,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | spl5_7
    | ~ spl5_11 ),
    inference(unit_resulting_resolution,[],[f129,f124,f119,f114,f186,f72])).

fof(f186,plain,
    ( m1_connsp_2(sK3,sK0,sK1)
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f184])).

fof(f261,plain,
    ( ~ spl5_19
    | spl5_1 ),
    inference(avatar_split_clause,[],[f250,f97,f257])).

fof(f97,plain,
    ( spl5_1
  <=> m1_subset_1(k3_tarski(k2_tarski(sK2,sK3)),u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f250,plain,
    ( ~ r2_hidden(k3_tarski(k2_tarski(sK2,sK3)),u1_struct_0(k9_yellow_6(sK0,sK1)))
    | spl5_1 ),
    inference(resolution,[],[f99,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f99,plain,
    ( ~ m1_subset_1(k3_tarski(k2_tarski(sK2,sK3)),u1_struct_0(k9_yellow_6(sK0,sK1)))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f97])).

fof(f226,plain,
    ( spl5_15
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | spl5_7 ),
    inference(avatar_split_clause,[],[f225,f127,f122,f117,f112,f107,f218])).

fof(f225,plain,
    ( m1_connsp_2(sK2,sK0,sK1)
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | spl5_7 ),
    inference(subsumption_resolution,[],[f224,f129])).

fof(f224,plain,
    ( m1_connsp_2(sK2,sK0,sK1)
    | v2_struct_0(sK0)
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f223,f124])).

fof(f223,plain,
    ( m1_connsp_2(sK2,sK0,sK1)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f222,f119])).

fof(f222,plain,
    ( m1_connsp_2(sK2,sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f208,f114])).

fof(f208,plain,
    ( m1_connsp_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_3 ),
    inference(resolution,[],[f109,f64])).

fof(f192,plain,
    ( spl5_11
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | spl5_7 ),
    inference(avatar_split_clause,[],[f191,f127,f122,f117,f112,f102,f184])).

fof(f191,plain,
    ( m1_connsp_2(sK3,sK0,sK1)
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | spl5_7 ),
    inference(subsumption_resolution,[],[f190,f129])).

fof(f190,plain,
    ( m1_connsp_2(sK3,sK0,sK1)
    | v2_struct_0(sK0)
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f189,f124])).

fof(f189,plain,
    ( m1_connsp_2(sK3,sK0,sK1)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f188,f119])).

fof(f188,plain,
    ( m1_connsp_2(sK3,sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_2
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f174,f114])).

fof(f174,plain,
    ( m1_connsp_2(sK3,sK0,sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_2 ),
    inference(resolution,[],[f104,f64])).

fof(f130,plain,(
    ~ spl5_7 ),
    inference(avatar_split_clause,[],[f52,f127])).

fof(f52,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,
    ( ~ m1_subset_1(k2_xboole_0(sK2,sK3),u1_struct_0(k9_yellow_6(sK0,sK1)))
    & m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK0,sK1)))
    & m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1)))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f19,f42,f41,f40,f39])).

fof(f39,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))
                    & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) )
                & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(sK0,X1)))
                  & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK0,X1))) )
              & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK0,X1))) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(sK0,X1)))
                & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK0,X1))) )
            & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK0,X1))) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(sK0,sK1)))
              & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK0,sK1))) )
          & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK0,sK1))) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(sK0,sK1)))
            & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK0,sK1))) )
        & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK0,sK1))) )
   => ( ? [X3] :
          ( ~ m1_subset_1(k2_xboole_0(sK2,X3),u1_struct_0(k9_yellow_6(sK0,sK1)))
          & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK0,sK1))) )
      & m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ? [X3] :
        ( ~ m1_subset_1(k2_xboole_0(sK2,X3),u1_struct_0(k9_yellow_6(sK0,sK1)))
        & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK0,sK1))) )
   => ( ~ m1_subset_1(k2_xboole_0(sK2,sK3),u1_struct_0(k9_yellow_6(sK0,sK1)))
      & m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))
                  & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) )
              & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))
                  & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) )
              & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))
                   => m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))
                 => m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_waybel_9)).

fof(f125,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f53,f122])).

fof(f53,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f120,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f54,f117])).

fof(f54,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f115,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f55,f112])).

fof(f55,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f43])).

fof(f110,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f56,f107])).

fof(f56,plain,(
    m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    inference(cnf_transformation,[],[f43])).

fof(f105,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f57,f102])).

fof(f57,plain,(
    m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    inference(cnf_transformation,[],[f43])).

fof(f100,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f84,f97])).

fof(f84,plain,(
    ~ m1_subset_1(k3_tarski(k2_tarski(sK2,sK3)),u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    inference(definition_unfolding,[],[f58,f66])).

fof(f58,plain,(
    ~ m1_subset_1(k2_xboole_0(sK2,sK3),u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    inference(cnf_transformation,[],[f43])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 16:42:27 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.20/0.50  % (26418)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.50  % (26426)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.51  % (26442)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.51  % (26425)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.51  % (26443)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.51  % (26447)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.51  % (26422)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.52  % (26429)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.52  % (26429)Refutation not found, incomplete strategy% (26429)------------------------------
% 0.20/0.52  % (26429)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (26429)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (26429)Memory used [KB]: 10618
% 0.20/0.52  % (26429)Time elapsed: 0.108 s
% 0.20/0.52  % (26429)------------------------------
% 0.20/0.52  % (26429)------------------------------
% 0.20/0.52  % (26430)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.52  % (26430)Refutation not found, incomplete strategy% (26430)------------------------------
% 0.20/0.52  % (26430)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (26430)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (26430)Memory used [KB]: 10618
% 0.20/0.52  % (26430)Time elapsed: 0.108 s
% 0.20/0.52  % (26430)------------------------------
% 0.20/0.52  % (26430)------------------------------
% 0.20/0.52  % (26423)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.52  % (26433)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.52  % (26435)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.52  % (26420)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.53  % (26439)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.53  % (26436)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.53  % (26419)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.53  % (26434)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.53  % (26431)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  % (26440)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.53  % (26445)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.54  % (26437)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.54  % (26424)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.54  % (26444)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.54  % (26448)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.54  % (26421)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.54  % (26428)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.54  % (26432)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.55  % (26436)Refutation not found, incomplete strategy% (26436)------------------------------
% 0.20/0.55  % (26436)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (26436)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (26436)Memory used [KB]: 10618
% 0.20/0.55  % (26436)Time elapsed: 0.121 s
% 0.20/0.55  % (26436)------------------------------
% 0.20/0.55  % (26436)------------------------------
% 0.20/0.55  % (26446)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.45/0.55  % (26438)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.45/0.55  % (26441)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.60/0.57  % (26441)Refutation not found, incomplete strategy% (26441)------------------------------
% 1.60/0.57  % (26441)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.60/0.57  % (26441)Termination reason: Refutation not found, incomplete strategy
% 1.60/0.57  
% 1.60/0.57  % (26441)Memory used [KB]: 10874
% 1.60/0.57  % (26441)Time elapsed: 0.117 s
% 1.60/0.57  % (26441)------------------------------
% 1.60/0.57  % (26441)------------------------------
% 1.60/0.62  % (26444)Refutation found. Thanks to Tanya!
% 1.60/0.62  % SZS status Theorem for theBenchmark
% 1.60/0.62  % SZS output start Proof for theBenchmark
% 1.60/0.62  fof(f2726,plain,(
% 1.60/0.62    $false),
% 1.60/0.62    inference(avatar_sat_refutation,[],[f100,f105,f110,f115,f120,f125,f130,f192,f226,f261,f292,f300,f622,f661,f662,f733,f738,f794,f1043,f1059,f1071,f1080,f1459,f1601,f1990,f1998,f2704,f2725])).
% 2.03/0.63  fof(f2725,plain,(
% 2.03/0.63    ~spl5_224),
% 2.03/0.63    inference(avatar_contradiction_clause,[],[f2724])).
% 2.03/0.63  fof(f2724,plain,(
% 2.03/0.63    $false | ~spl5_224),
% 2.03/0.63    inference(subsumption_resolution,[],[f2711,f60])).
% 2.03/0.63  fof(f60,plain,(
% 2.03/0.63    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.03/0.63    inference(cnf_transformation,[],[f3])).
% 2.03/0.63  fof(f3,axiom,(
% 2.03/0.63    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.03/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 2.03/0.63  fof(f2711,plain,(
% 2.03/0.63    ~r1_tarski(k1_xboole_0,sK1) | ~spl5_224),
% 2.03/0.63    inference(unit_resulting_resolution,[],[f2703,f73])).
% 2.03/0.63  fof(f73,plain,(
% 2.03/0.63    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 2.03/0.63    inference(cnf_transformation,[],[f30])).
% 2.03/0.63  fof(f30,plain,(
% 2.03/0.63    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 2.03/0.63    inference(ennf_transformation,[],[f10])).
% 2.03/0.63  fof(f10,axiom,(
% 2.03/0.63    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 2.03/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 2.03/0.63  fof(f2703,plain,(
% 2.03/0.63    r2_hidden(sK1,k1_xboole_0) | ~spl5_224),
% 2.03/0.63    inference(avatar_component_clause,[],[f2701])).
% 2.03/0.63  fof(f2701,plain,(
% 2.03/0.63    spl5_224 <=> r2_hidden(sK1,k1_xboole_0)),
% 2.03/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_224])])).
% 2.03/0.63  fof(f2704,plain,(
% 2.03/0.63    spl5_224 | ~spl5_4 | ~spl5_5 | ~spl5_6 | spl5_7 | ~spl5_162 | ~spl5_163),
% 2.03/0.63    inference(avatar_split_clause,[],[f2568,f1995,f1982,f127,f122,f117,f112,f2701])).
% 2.03/0.63  fof(f112,plain,(
% 2.03/0.63    spl5_4 <=> m1_subset_1(sK1,u1_struct_0(sK0))),
% 2.03/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 2.03/0.63  fof(f117,plain,(
% 2.03/0.63    spl5_5 <=> l1_pre_topc(sK0)),
% 2.03/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 2.03/0.63  fof(f122,plain,(
% 2.03/0.63    spl5_6 <=> v2_pre_topc(sK0)),
% 2.03/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 2.03/0.63  fof(f127,plain,(
% 2.03/0.63    spl5_7 <=> v2_struct_0(sK0)),
% 2.03/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 2.03/0.63  fof(f1982,plain,(
% 2.03/0.63    spl5_162 <=> m1_connsp_2(k1_xboole_0,sK0,sK1)),
% 2.03/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_162])])).
% 2.03/0.63  fof(f1995,plain,(
% 2.03/0.63    spl5_163 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.03/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_163])])).
% 2.03/0.63  fof(f2568,plain,(
% 2.03/0.63    r2_hidden(sK1,k1_xboole_0) | (~spl5_4 | ~spl5_5 | ~spl5_6 | spl5_7 | ~spl5_162 | ~spl5_163)),
% 2.03/0.63    inference(unit_resulting_resolution,[],[f129,f124,f119,f114,f1984,f1997,f65])).
% 2.03/0.64  fof(f65,plain,(
% 2.03/0.64    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~m1_connsp_2(X1,X0,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.03/0.64    inference(cnf_transformation,[],[f25])).
% 2.03/0.64  fof(f25,plain,(
% 2.03/0.64    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(X2,X1) | ~m1_connsp_2(X1,X0,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.03/0.64    inference(flattening,[],[f24])).
% 2.03/0.64  fof(f24,plain,(
% 2.03/0.64    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,X1) | ~m1_connsp_2(X1,X0,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.03/0.64    inference(ennf_transformation,[],[f13])).
% 2.03/0.64  fof(f13,axiom,(
% 2.03/0.64    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (m1_connsp_2(X1,X0,X2) => r2_hidden(X2,X1)))))),
% 2.03/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_connsp_2)).
% 2.03/0.64  fof(f1997,plain,(
% 2.03/0.64    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_163),
% 2.03/0.64    inference(avatar_component_clause,[],[f1995])).
% 2.03/0.64  fof(f1984,plain,(
% 2.03/0.64    m1_connsp_2(k1_xboole_0,sK0,sK1) | ~spl5_162),
% 2.03/0.64    inference(avatar_component_clause,[],[f1982])).
% 2.03/0.64  fof(f114,plain,(
% 2.03/0.64    m1_subset_1(sK1,u1_struct_0(sK0)) | ~spl5_4),
% 2.03/0.64    inference(avatar_component_clause,[],[f112])).
% 2.03/0.64  fof(f119,plain,(
% 2.03/0.64    l1_pre_topc(sK0) | ~spl5_5),
% 2.03/0.64    inference(avatar_component_clause,[],[f117])).
% 2.03/0.64  fof(f124,plain,(
% 2.03/0.64    v2_pre_topc(sK0) | ~spl5_6),
% 2.03/0.64    inference(avatar_component_clause,[],[f122])).
% 2.03/0.64  fof(f129,plain,(
% 2.03/0.64    ~v2_struct_0(sK0) | spl5_7),
% 2.03/0.64    inference(avatar_component_clause,[],[f127])).
% 2.03/0.64  fof(f1998,plain,(
% 2.03/0.64    spl5_163 | ~spl5_4 | ~spl5_5 | ~spl5_6 | spl5_7 | ~spl5_162),
% 2.03/0.64    inference(avatar_split_clause,[],[f1991,f1982,f127,f122,f117,f112,f1995])).
% 2.03/0.64  fof(f1991,plain,(
% 2.03/0.64    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl5_4 | ~spl5_5 | ~spl5_6 | spl5_7 | ~spl5_162)),
% 2.03/0.64    inference(unit_resulting_resolution,[],[f129,f124,f119,f114,f1984,f72])).
% 2.03/0.64  fof(f72,plain,(
% 2.03/0.64    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.03/0.64    inference(cnf_transformation,[],[f29])).
% 2.03/0.64  fof(f29,plain,(
% 2.03/0.64    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.03/0.64    inference(flattening,[],[f28])).
% 2.03/0.64  fof(f28,plain,(
% 2.03/0.64    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.03/0.64    inference(ennf_transformation,[],[f12])).
% 2.03/0.64  fof(f12,axiom,(
% 2.03/0.64    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.03/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_connsp_2)).
% 2.03/0.64  fof(f1990,plain,(
% 2.03/0.64    spl5_162 | ~spl5_4 | ~spl5_5 | ~spl5_6 | spl5_7 | ~spl5_127),
% 2.03/0.64    inference(avatar_split_clause,[],[f1989,f1598,f127,f122,f117,f112,f1982])).
% 2.03/0.64  fof(f1598,plain,(
% 2.03/0.64    spl5_127 <=> m1_subset_1(k1_xboole_0,u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 2.03/0.64    introduced(avatar_definition,[new_symbols(naming,[spl5_127])])).
% 2.03/0.64  fof(f1989,plain,(
% 2.03/0.64    m1_connsp_2(k1_xboole_0,sK0,sK1) | (~spl5_4 | ~spl5_5 | ~spl5_6 | spl5_7 | ~spl5_127)),
% 2.03/0.64    inference(subsumption_resolution,[],[f1988,f129])).
% 2.03/0.64  fof(f1988,plain,(
% 2.03/0.64    m1_connsp_2(k1_xboole_0,sK0,sK1) | v2_struct_0(sK0) | (~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_127)),
% 2.03/0.64    inference(subsumption_resolution,[],[f1987,f124])).
% 2.03/0.64  fof(f1987,plain,(
% 2.03/0.64    m1_connsp_2(k1_xboole_0,sK0,sK1) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl5_4 | ~spl5_5 | ~spl5_127)),
% 2.03/0.64    inference(subsumption_resolution,[],[f1986,f119])).
% 2.03/0.64  fof(f1986,plain,(
% 2.03/0.64    m1_connsp_2(k1_xboole_0,sK0,sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl5_4 | ~spl5_127)),
% 2.03/0.64    inference(subsumption_resolution,[],[f1972,f114])).
% 2.03/0.64  fof(f1972,plain,(
% 2.03/0.64    m1_connsp_2(k1_xboole_0,sK0,sK1) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl5_127),
% 2.03/0.64    inference(resolution,[],[f1600,f64])).
% 2.03/0.64  fof(f64,plain,(
% 2.03/0.64    ( ! [X2,X0,X1] : (m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.03/0.64    inference(cnf_transformation,[],[f23])).
% 2.03/0.64  fof(f23,plain,(
% 2.03/0.64    ! [X0] : (! [X1] : (! [X2] : (m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.03/0.64    inference(flattening,[],[f22])).
% 2.03/0.64  fof(f22,plain,(
% 2.03/0.64    ! [X0] : (! [X1] : (! [X2] : (m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.03/0.64    inference(ennf_transformation,[],[f15])).
% 2.03/0.64  fof(f15,axiom,(
% 2.03/0.64    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => m1_connsp_2(X2,X0,X1))))),
% 2.03/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_waybel_9)).
% 2.03/0.64  fof(f1600,plain,(
% 2.03/0.64    m1_subset_1(k1_xboole_0,u1_struct_0(k9_yellow_6(sK0,sK1))) | ~spl5_127),
% 2.03/0.64    inference(avatar_component_clause,[],[f1598])).
% 2.03/0.64  fof(f1601,plain,(
% 2.03/0.64    spl5_127 | ~spl5_12),
% 2.03/0.64    inference(avatar_split_clause,[],[f1564,f194,f1598])).
% 2.03/0.64  fof(f194,plain,(
% 2.03/0.64    spl5_12 <=> v1_xboole_0(u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 2.03/0.64    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 2.03/0.64  fof(f1564,plain,(
% 2.03/0.64    m1_subset_1(k1_xboole_0,u1_struct_0(k9_yellow_6(sK0,sK1))) | ~spl5_12),
% 2.03/0.64    inference(unit_resulting_resolution,[],[f59,f196,f70])).
% 2.03/0.64  fof(f70,plain,(
% 2.03/0.64    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~v1_xboole_0(X1) | ~v1_xboole_0(X0)) )),
% 2.03/0.64    inference(cnf_transformation,[],[f46])).
% 2.03/0.64  fof(f46,plain,(
% 2.03/0.64    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 2.03/0.64    inference(nnf_transformation,[],[f26])).
% 2.03/0.64  fof(f26,plain,(
% 2.03/0.64    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 2.03/0.64    inference(ennf_transformation,[],[f5])).
% 2.03/0.64  fof(f5,axiom,(
% 2.03/0.64    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 2.03/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 2.03/0.64  fof(f196,plain,(
% 2.03/0.64    v1_xboole_0(u1_struct_0(k9_yellow_6(sK0,sK1))) | ~spl5_12),
% 2.03/0.64    inference(avatar_component_clause,[],[f194])).
% 2.03/0.64  fof(f59,plain,(
% 2.03/0.64    v1_xboole_0(k1_xboole_0)),
% 2.03/0.64    inference(cnf_transformation,[],[f2])).
% 2.03/0.64  fof(f2,axiom,(
% 2.03/0.64    v1_xboole_0(k1_xboole_0)),
% 2.03/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 2.03/0.64  fof(f1459,plain,(
% 2.03/0.64    ~spl5_30 | spl5_51),
% 2.03/0.64    inference(avatar_contradiction_clause,[],[f1458])).
% 2.03/0.64  fof(f1458,plain,(
% 2.03/0.64    $false | (~spl5_30 | spl5_51)),
% 2.03/0.64    inference(subsumption_resolution,[],[f1442,f391])).
% 2.03/0.64  fof(f391,plain,(
% 2.03/0.64    r2_hidden(sK1,sK2) | ~spl5_30),
% 2.03/0.64    inference(avatar_component_clause,[],[f389])).
% 2.03/0.64  fof(f389,plain,(
% 2.03/0.64    spl5_30 <=> r2_hidden(sK1,sK2)),
% 2.03/0.64    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).
% 2.03/0.64  fof(f1442,plain,(
% 2.03/0.64    ~r2_hidden(sK1,sK2) | spl5_51),
% 2.03/0.64    inference(resolution,[],[f789,f94])).
% 2.03/0.64  fof(f94,plain,(
% 2.03/0.64    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_tarski(k2_tarski(X0,X1))) | ~r2_hidden(X4,X0)) )),
% 2.03/0.64    inference(equality_resolution,[],[f91])).
% 2.03/0.64  fof(f91,plain,(
% 2.03/0.64    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k3_tarski(k2_tarski(X0,X1)) != X2) )),
% 2.03/0.64    inference(definition_unfolding,[],[f79,f66])).
% 2.03/0.64  fof(f66,plain,(
% 2.03/0.64    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.03/0.64    inference(cnf_transformation,[],[f4])).
% 2.03/0.64  fof(f4,axiom,(
% 2.03/0.64    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.03/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 2.03/0.64  fof(f79,plain,(
% 2.03/0.64    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k2_xboole_0(X0,X1) != X2) )),
% 2.03/0.64    inference(cnf_transformation,[],[f51])).
% 2.03/0.64  fof(f51,plain,(
% 2.03/0.64    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK4(X0,X1,X2),X1) & ~r2_hidden(sK4(X0,X1,X2),X0)) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.03/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f49,f50])).
% 2.03/0.64  fof(f50,plain,(
% 2.03/0.64    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK4(X0,X1,X2),X1) & ~r2_hidden(sK4(X0,X1,X2),X0)) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 2.03/0.64    introduced(choice_axiom,[])).
% 2.03/0.64  fof(f49,plain,(
% 2.03/0.64    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.03/0.64    inference(rectify,[],[f48])).
% 2.03/0.64  fof(f48,plain,(
% 2.03/0.64    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.03/0.64    inference(flattening,[],[f47])).
% 2.03/0.64  fof(f47,plain,(
% 2.03/0.64    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.03/0.64    inference(nnf_transformation,[],[f1])).
% 2.03/0.64  fof(f1,axiom,(
% 2.03/0.64    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 2.03/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).
% 2.03/0.64  fof(f789,plain,(
% 2.03/0.64    ~r2_hidden(sK1,k3_tarski(k2_tarski(sK2,sK3))) | spl5_51),
% 2.03/0.64    inference(avatar_component_clause,[],[f787])).
% 2.03/0.64  fof(f787,plain,(
% 2.03/0.64    spl5_51 <=> r2_hidden(sK1,k3_tarski(k2_tarski(sK2,sK3)))),
% 2.03/0.64    introduced(avatar_definition,[new_symbols(naming,[spl5_51])])).
% 2.03/0.64  fof(f1080,plain,(
% 2.03/0.64    k3_tarski(k2_tarski(sK2,sK3)) != k4_subset_1(u1_struct_0(sK0),sK2,sK3) | ~m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(k3_tarski(k2_tarski(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.03/0.64    introduced(theory_tautology_sat_conflict,[])).
% 2.03/0.64  fof(f1071,plain,(
% 2.03/0.64    spl5_52 | ~spl5_5 | ~spl5_6 | ~spl5_22 | ~spl5_23 | ~spl5_28 | ~spl5_31),
% 2.03/0.64    inference(avatar_split_clause,[],[f998,f398,f361,f297,f289,f122,f117,f791])).
% 2.03/0.64  fof(f791,plain,(
% 2.03/0.64    spl5_52 <=> v3_pre_topc(k3_tarski(k2_tarski(sK2,sK3)),sK0)),
% 2.03/0.64    introduced(avatar_definition,[new_symbols(naming,[spl5_52])])).
% 2.03/0.64  fof(f289,plain,(
% 2.03/0.64    spl5_22 <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.03/0.64    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 2.03/0.64  fof(f297,plain,(
% 2.03/0.64    spl5_23 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.03/0.64    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).
% 2.03/0.64  fof(f361,plain,(
% 2.03/0.64    spl5_28 <=> v3_pre_topc(sK3,sK0)),
% 2.03/0.64    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).
% 2.03/0.64  fof(f398,plain,(
% 2.03/0.64    spl5_31 <=> v3_pre_topc(sK2,sK0)),
% 2.03/0.64    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).
% 2.03/0.64  fof(f998,plain,(
% 2.03/0.64    v3_pre_topc(k3_tarski(k2_tarski(sK2,sK3)),sK0) | (~spl5_5 | ~spl5_6 | ~spl5_22 | ~spl5_23 | ~spl5_28 | ~spl5_31)),
% 2.03/0.64    inference(unit_resulting_resolution,[],[f124,f119,f400,f363,f291,f299,f85])).
% 2.03/0.64  fof(f85,plain,(
% 2.03/0.64    ( ! [X2,X0,X1] : (v3_pre_topc(k3_tarski(k2_tarski(X1,X2)),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.03/0.64    inference(definition_unfolding,[],[f74,f66])).
% 2.03/0.64  fof(f74,plain,(
% 2.03/0.64    ( ! [X2,X0,X1] : (v3_pre_topc(k2_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.03/0.64    inference(cnf_transformation,[],[f32])).
% 2.03/0.64  fof(f32,plain,(
% 2.03/0.64    ! [X0,X1,X2] : (v3_pre_topc(k2_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.03/0.64    inference(flattening,[],[f31])).
% 2.03/0.64  fof(f31,plain,(
% 2.03/0.64    ! [X0,X1,X2] : (v3_pre_topc(k2_xboole_0(X1,X2),X0) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.03/0.64    inference(ennf_transformation,[],[f11])).
% 2.03/0.64  fof(f11,axiom,(
% 2.03/0.64    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X2,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_xboole_0(X1,X2),X0))),
% 2.03/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_tops_1)).
% 2.03/0.64  fof(f299,plain,(
% 2.03/0.64    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_23),
% 2.03/0.64    inference(avatar_component_clause,[],[f297])).
% 2.03/0.64  fof(f291,plain,(
% 2.03/0.64    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_22),
% 2.03/0.64    inference(avatar_component_clause,[],[f289])).
% 2.03/0.64  fof(f363,plain,(
% 2.03/0.64    v3_pre_topc(sK3,sK0) | ~spl5_28),
% 2.03/0.64    inference(avatar_component_clause,[],[f361])).
% 2.03/0.64  fof(f400,plain,(
% 2.03/0.64    v3_pre_topc(sK2,sK0) | ~spl5_31),
% 2.03/0.64    inference(avatar_component_clause,[],[f398])).
% 2.03/0.64  fof(f1059,plain,(
% 2.03/0.64    spl5_78 | ~spl5_22 | ~spl5_23),
% 2.03/0.64    inference(avatar_split_clause,[],[f1006,f297,f289,f1056])).
% 2.03/0.64  fof(f1056,plain,(
% 2.03/0.64    spl5_78 <=> k3_tarski(k2_tarski(sK2,sK3)) = k4_subset_1(u1_struct_0(sK0),sK2,sK3)),
% 2.03/0.64    introduced(avatar_definition,[new_symbols(naming,[spl5_78])])).
% 2.03/0.64  fof(f1006,plain,(
% 2.03/0.64    k3_tarski(k2_tarski(sK2,sK3)) = k4_subset_1(u1_struct_0(sK0),sK2,sK3) | (~spl5_22 | ~spl5_23)),
% 2.03/0.64    inference(unit_resulting_resolution,[],[f291,f299,f86])).
% 2.03/0.64  fof(f86,plain,(
% 2.03/0.64    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.03/0.64    inference(definition_unfolding,[],[f77,f66])).
% 2.03/0.64  fof(f77,plain,(
% 2.03/0.64    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.03/0.64    inference(cnf_transformation,[],[f38])).
% 2.03/0.64  fof(f38,plain,(
% 2.03/0.64    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.03/0.64    inference(flattening,[],[f37])).
% 2.03/0.64  fof(f37,plain,(
% 2.03/0.64    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 2.03/0.64    inference(ennf_transformation,[],[f7])).
% 2.03/0.64  fof(f7,axiom,(
% 2.03/0.64    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 2.03/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 2.03/0.64  fof(f1043,plain,(
% 2.03/0.64    spl5_75 | ~spl5_22 | ~spl5_23),
% 2.03/0.64    inference(avatar_split_clause,[],[f1010,f297,f289,f1040])).
% 2.03/0.64  fof(f1040,plain,(
% 2.03/0.64    spl5_75 <=> m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.03/0.64    introduced(avatar_definition,[new_symbols(naming,[spl5_75])])).
% 2.03/0.64  fof(f1010,plain,(
% 2.03/0.64    m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl5_22 | ~spl5_23)),
% 2.03/0.64    inference(unit_resulting_resolution,[],[f291,f299,f76])).
% 2.03/0.64  fof(f76,plain,(
% 2.03/0.64    ( ! [X2,X0,X1] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.03/0.64    inference(cnf_transformation,[],[f36])).
% 2.03/0.64  fof(f36,plain,(
% 2.03/0.64    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.03/0.64    inference(flattening,[],[f35])).
% 2.03/0.64  fof(f35,plain,(
% 2.03/0.64    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 2.03/0.64    inference(ennf_transformation,[],[f6])).
% 2.03/0.64  fof(f6,axiom,(
% 2.03/0.64    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 2.03/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).
% 2.03/0.64  fof(f794,plain,(
% 2.03/0.64    ~spl5_50 | ~spl5_51 | ~spl5_52 | ~spl5_4 | ~spl5_5 | ~spl5_6 | spl5_7 | spl5_19),
% 2.03/0.64    inference(avatar_split_clause,[],[f781,f257,f127,f122,f117,f112,f791,f787,f783])).
% 2.03/0.64  fof(f783,plain,(
% 2.03/0.64    spl5_50 <=> m1_subset_1(k3_tarski(k2_tarski(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.03/0.64    introduced(avatar_definition,[new_symbols(naming,[spl5_50])])).
% 2.03/0.64  fof(f257,plain,(
% 2.03/0.64    spl5_19 <=> r2_hidden(k3_tarski(k2_tarski(sK2,sK3)),u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 2.03/0.64    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 2.03/0.64  fof(f781,plain,(
% 2.03/0.64    ~v3_pre_topc(k3_tarski(k2_tarski(sK2,sK3)),sK0) | ~r2_hidden(sK1,k3_tarski(k2_tarski(sK2,sK3))) | ~m1_subset_1(k3_tarski(k2_tarski(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl5_4 | ~spl5_5 | ~spl5_6 | spl5_7 | spl5_19)),
% 2.03/0.64    inference(subsumption_resolution,[],[f780,f129])).
% 2.03/0.64  fof(f780,plain,(
% 2.03/0.64    ~v3_pre_topc(k3_tarski(k2_tarski(sK2,sK3)),sK0) | ~r2_hidden(sK1,k3_tarski(k2_tarski(sK2,sK3))) | ~m1_subset_1(k3_tarski(k2_tarski(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | (~spl5_4 | ~spl5_5 | ~spl5_6 | spl5_19)),
% 2.03/0.64    inference(subsumption_resolution,[],[f779,f124])).
% 2.03/0.64  fof(f779,plain,(
% 2.03/0.64    ~v3_pre_topc(k3_tarski(k2_tarski(sK2,sK3)),sK0) | ~r2_hidden(sK1,k3_tarski(k2_tarski(sK2,sK3))) | ~m1_subset_1(k3_tarski(k2_tarski(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl5_4 | ~spl5_5 | spl5_19)),
% 2.03/0.64    inference(subsumption_resolution,[],[f778,f119])).
% 2.03/0.64  fof(f778,plain,(
% 2.03/0.64    ~v3_pre_topc(k3_tarski(k2_tarski(sK2,sK3)),sK0) | ~r2_hidden(sK1,k3_tarski(k2_tarski(sK2,sK3))) | ~m1_subset_1(k3_tarski(k2_tarski(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl5_4 | spl5_19)),
% 2.03/0.64    inference(subsumption_resolution,[],[f763,f114])).
% 2.03/0.64  fof(f763,plain,(
% 2.03/0.64    ~v3_pre_topc(k3_tarski(k2_tarski(sK2,sK3)),sK0) | ~r2_hidden(sK1,k3_tarski(k2_tarski(sK2,sK3))) | ~m1_subset_1(k3_tarski(k2_tarski(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl5_19),
% 2.03/0.64    inference(resolution,[],[f259,f63])).
% 2.03/0.64  fof(f63,plain,(
% 2.03/0.64    ( ! [X2,X0,X1] : (r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~v3_pre_topc(X2,X0) | ~r2_hidden(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.03/0.64    inference(cnf_transformation,[],[f45])).
% 2.03/0.64  fof(f45,plain,(
% 2.03/0.64    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~v3_pre_topc(X2,X0) | ~r2_hidden(X1,X2)) & ((v3_pre_topc(X2,X0) & r2_hidden(X1,X2)) | ~r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.03/0.64    inference(flattening,[],[f44])).
% 2.03/0.64  fof(f44,plain,(
% 2.03/0.64    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | (~v3_pre_topc(X2,X0) | ~r2_hidden(X1,X2))) & ((v3_pre_topc(X2,X0) & r2_hidden(X1,X2)) | ~r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.03/0.64    inference(nnf_transformation,[],[f21])).
% 2.03/0.64  fof(f21,plain,(
% 2.03/0.64    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.03/0.64    inference(flattening,[],[f20])).
% 2.03/0.64  fof(f20,plain,(
% 2.03/0.64    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.03/0.64    inference(ennf_transformation,[],[f14])).
% 2.03/0.64  fof(f14,axiom,(
% 2.03/0.64    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2))))))),
% 2.03/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_yellow_6)).
% 2.03/0.64  fof(f259,plain,(
% 2.03/0.64    ~r2_hidden(k3_tarski(k2_tarski(sK2,sK3)),u1_struct_0(k9_yellow_6(sK0,sK1))) | spl5_19),
% 2.03/0.64    inference(avatar_component_clause,[],[f257])).
% 2.03/0.64  fof(f738,plain,(
% 2.03/0.64    ~spl5_23 | spl5_31 | ~spl5_4 | ~spl5_5 | ~spl5_6 | spl5_7 | ~spl5_16),
% 2.03/0.64    inference(avatar_split_clause,[],[f737,f228,f127,f122,f117,f112,f398,f297])).
% 2.03/0.64  fof(f228,plain,(
% 2.03/0.64    spl5_16 <=> r2_hidden(sK2,u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 2.03/0.64    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 2.03/0.64  fof(f737,plain,(
% 2.03/0.64    v3_pre_topc(sK2,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl5_4 | ~spl5_5 | ~spl5_6 | spl5_7 | ~spl5_16)),
% 2.03/0.64    inference(subsumption_resolution,[],[f736,f129])).
% 2.03/0.64  fof(f736,plain,(
% 2.03/0.64    v3_pre_topc(sK2,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | (~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_16)),
% 2.03/0.64    inference(subsumption_resolution,[],[f735,f124])).
% 2.03/0.64  fof(f735,plain,(
% 2.03/0.64    v3_pre_topc(sK2,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl5_4 | ~spl5_5 | ~spl5_16)),
% 2.03/0.64    inference(subsumption_resolution,[],[f734,f119])).
% 2.03/0.64  fof(f734,plain,(
% 2.03/0.64    v3_pre_topc(sK2,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl5_4 | ~spl5_16)),
% 2.03/0.64    inference(subsumption_resolution,[],[f720,f114])).
% 2.03/0.64  fof(f720,plain,(
% 2.03/0.64    v3_pre_topc(sK2,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl5_16),
% 2.03/0.64    inference(resolution,[],[f230,f62])).
% 2.03/0.64  fof(f62,plain,(
% 2.03/0.64    ( ! [X2,X0,X1] : (v3_pre_topc(X2,X0) | ~r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.03/0.64    inference(cnf_transformation,[],[f45])).
% 2.03/0.64  fof(f230,plain,(
% 2.03/0.64    r2_hidden(sK2,u1_struct_0(k9_yellow_6(sK0,sK1))) | ~spl5_16),
% 2.03/0.64    inference(avatar_component_clause,[],[f228])).
% 2.03/0.64  fof(f733,plain,(
% 2.03/0.64    ~spl5_23 | spl5_30 | ~spl5_4 | ~spl5_5 | ~spl5_6 | spl5_7 | ~spl5_16),
% 2.03/0.64    inference(avatar_split_clause,[],[f732,f228,f127,f122,f117,f112,f389,f297])).
% 2.03/0.64  fof(f732,plain,(
% 2.03/0.64    r2_hidden(sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl5_4 | ~spl5_5 | ~spl5_6 | spl5_7 | ~spl5_16)),
% 2.03/0.64    inference(subsumption_resolution,[],[f731,f129])).
% 2.03/0.64  fof(f731,plain,(
% 2.03/0.64    r2_hidden(sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | (~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_16)),
% 2.03/0.64    inference(subsumption_resolution,[],[f730,f124])).
% 2.03/0.64  fof(f730,plain,(
% 2.03/0.64    r2_hidden(sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl5_4 | ~spl5_5 | ~spl5_16)),
% 2.03/0.64    inference(subsumption_resolution,[],[f729,f119])).
% 2.03/0.65  fof(f729,plain,(
% 2.03/0.65    r2_hidden(sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl5_4 | ~spl5_16)),
% 2.03/0.65    inference(subsumption_resolution,[],[f719,f114])).
% 2.03/0.65  fof(f719,plain,(
% 2.03/0.65    r2_hidden(sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl5_16),
% 2.03/0.65    inference(resolution,[],[f230,f61])).
% 2.03/0.65  fof(f61,plain,(
% 2.03/0.65    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | ~r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.03/0.65    inference(cnf_transformation,[],[f45])).
% 2.03/0.65  fof(f662,plain,(
% 2.03/0.65    spl5_13 | ~spl5_2 | spl5_12),
% 2.03/0.65    inference(avatar_split_clause,[],[f646,f194,f102,f198])).
% 2.03/0.65  fof(f198,plain,(
% 2.03/0.65    spl5_13 <=> r2_hidden(sK3,u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 2.03/0.65    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 2.03/0.65  fof(f102,plain,(
% 2.03/0.65    spl5_2 <=> m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 2.03/0.65    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 2.03/0.65  fof(f646,plain,(
% 2.03/0.65    r2_hidden(sK3,u1_struct_0(k9_yellow_6(sK0,sK1))) | (~spl5_2 | spl5_12)),
% 2.03/0.65    inference(unit_resulting_resolution,[],[f104,f195,f67])).
% 2.03/0.65  fof(f67,plain,(
% 2.03/0.65    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.03/0.65    inference(cnf_transformation,[],[f46])).
% 2.03/0.65  fof(f195,plain,(
% 2.03/0.65    ~v1_xboole_0(u1_struct_0(k9_yellow_6(sK0,sK1))) | spl5_12),
% 2.03/0.65    inference(avatar_component_clause,[],[f194])).
% 2.03/0.65  fof(f104,plain,(
% 2.03/0.65    m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK0,sK1))) | ~spl5_2),
% 2.03/0.65    inference(avatar_component_clause,[],[f102])).
% 2.03/0.65  fof(f661,plain,(
% 2.03/0.65    spl5_16 | ~spl5_3 | spl5_12),
% 2.03/0.65    inference(avatar_split_clause,[],[f647,f194,f107,f228])).
% 2.03/0.65  fof(f107,plain,(
% 2.03/0.65    spl5_3 <=> m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 2.03/0.65    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 2.03/0.65  fof(f647,plain,(
% 2.03/0.65    r2_hidden(sK2,u1_struct_0(k9_yellow_6(sK0,sK1))) | (~spl5_3 | spl5_12)),
% 2.03/0.65    inference(unit_resulting_resolution,[],[f109,f195,f67])).
% 2.03/0.65  fof(f109,plain,(
% 2.03/0.65    m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1))) | ~spl5_3),
% 2.03/0.65    inference(avatar_component_clause,[],[f107])).
% 2.03/0.65  fof(f622,plain,(
% 2.03/0.65    ~spl5_22 | spl5_28 | ~spl5_4 | ~spl5_5 | ~spl5_6 | spl5_7 | ~spl5_13),
% 2.03/0.65    inference(avatar_split_clause,[],[f621,f198,f127,f122,f117,f112,f361,f289])).
% 2.03/0.65  fof(f621,plain,(
% 2.03/0.65    v3_pre_topc(sK3,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl5_4 | ~spl5_5 | ~spl5_6 | spl5_7 | ~spl5_13)),
% 2.03/0.65    inference(subsumption_resolution,[],[f620,f129])).
% 2.03/0.65  fof(f620,plain,(
% 2.03/0.65    v3_pre_topc(sK3,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | (~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_13)),
% 2.03/0.65    inference(subsumption_resolution,[],[f619,f124])).
% 2.03/0.65  fof(f619,plain,(
% 2.03/0.65    v3_pre_topc(sK3,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl5_4 | ~spl5_5 | ~spl5_13)),
% 2.03/0.65    inference(subsumption_resolution,[],[f618,f119])).
% 2.03/0.65  fof(f618,plain,(
% 2.03/0.65    v3_pre_topc(sK3,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl5_4 | ~spl5_13)),
% 2.03/0.65    inference(subsumption_resolution,[],[f334,f114])).
% 2.03/0.65  fof(f334,plain,(
% 2.03/0.65    v3_pre_topc(sK3,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl5_13),
% 2.03/0.65    inference(resolution,[],[f200,f62])).
% 2.03/0.65  fof(f200,plain,(
% 2.03/0.65    r2_hidden(sK3,u1_struct_0(k9_yellow_6(sK0,sK1))) | ~spl5_13),
% 2.03/0.65    inference(avatar_component_clause,[],[f198])).
% 2.03/0.65  fof(f300,plain,(
% 2.03/0.65    spl5_23 | ~spl5_4 | ~spl5_5 | ~spl5_6 | spl5_7 | ~spl5_15),
% 2.03/0.65    inference(avatar_split_clause,[],[f293,f218,f127,f122,f117,f112,f297])).
% 2.03/0.65  fof(f218,plain,(
% 2.03/0.65    spl5_15 <=> m1_connsp_2(sK2,sK0,sK1)),
% 2.03/0.65    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 2.03/0.65  fof(f293,plain,(
% 2.03/0.65    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl5_4 | ~spl5_5 | ~spl5_6 | spl5_7 | ~spl5_15)),
% 2.03/0.65    inference(unit_resulting_resolution,[],[f129,f124,f119,f114,f220,f72])).
% 2.03/0.65  fof(f220,plain,(
% 2.03/0.65    m1_connsp_2(sK2,sK0,sK1) | ~spl5_15),
% 2.03/0.65    inference(avatar_component_clause,[],[f218])).
% 2.03/0.65  fof(f292,plain,(
% 2.03/0.65    spl5_22 | ~spl5_4 | ~spl5_5 | ~spl5_6 | spl5_7 | ~spl5_11),
% 2.03/0.65    inference(avatar_split_clause,[],[f285,f184,f127,f122,f117,f112,f289])).
% 2.03/0.65  fof(f184,plain,(
% 2.03/0.65    spl5_11 <=> m1_connsp_2(sK3,sK0,sK1)),
% 2.03/0.65    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 2.03/0.65  fof(f285,plain,(
% 2.03/0.65    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl5_4 | ~spl5_5 | ~spl5_6 | spl5_7 | ~spl5_11)),
% 2.03/0.65    inference(unit_resulting_resolution,[],[f129,f124,f119,f114,f186,f72])).
% 2.03/0.65  fof(f186,plain,(
% 2.03/0.65    m1_connsp_2(sK3,sK0,sK1) | ~spl5_11),
% 2.03/0.65    inference(avatar_component_clause,[],[f184])).
% 2.03/0.65  fof(f261,plain,(
% 2.03/0.65    ~spl5_19 | spl5_1),
% 2.03/0.65    inference(avatar_split_clause,[],[f250,f97,f257])).
% 2.03/0.65  fof(f97,plain,(
% 2.03/0.65    spl5_1 <=> m1_subset_1(k3_tarski(k2_tarski(sK2,sK3)),u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 2.03/0.65    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 2.03/0.65  fof(f250,plain,(
% 2.03/0.65    ~r2_hidden(k3_tarski(k2_tarski(sK2,sK3)),u1_struct_0(k9_yellow_6(sK0,sK1))) | spl5_1),
% 2.03/0.65    inference(resolution,[],[f99,f71])).
% 2.03/0.65  fof(f71,plain,(
% 2.03/0.65    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 2.03/0.65    inference(cnf_transformation,[],[f27])).
% 2.03/0.65  fof(f27,plain,(
% 2.03/0.65    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 2.03/0.65    inference(ennf_transformation,[],[f8])).
% 2.03/0.65  fof(f8,axiom,(
% 2.03/0.65    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 2.03/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 2.03/0.65  fof(f99,plain,(
% 2.03/0.65    ~m1_subset_1(k3_tarski(k2_tarski(sK2,sK3)),u1_struct_0(k9_yellow_6(sK0,sK1))) | spl5_1),
% 2.03/0.65    inference(avatar_component_clause,[],[f97])).
% 2.03/0.65  fof(f226,plain,(
% 2.03/0.65    spl5_15 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6 | spl5_7),
% 2.03/0.65    inference(avatar_split_clause,[],[f225,f127,f122,f117,f112,f107,f218])).
% 2.03/0.65  fof(f225,plain,(
% 2.03/0.65    m1_connsp_2(sK2,sK0,sK1) | (~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6 | spl5_7)),
% 2.03/0.65    inference(subsumption_resolution,[],[f224,f129])).
% 2.03/0.65  fof(f224,plain,(
% 2.03/0.65    m1_connsp_2(sK2,sK0,sK1) | v2_struct_0(sK0) | (~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6)),
% 2.03/0.65    inference(subsumption_resolution,[],[f223,f124])).
% 2.03/0.65  fof(f223,plain,(
% 2.03/0.65    m1_connsp_2(sK2,sK0,sK1) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl5_3 | ~spl5_4 | ~spl5_5)),
% 2.03/0.65    inference(subsumption_resolution,[],[f222,f119])).
% 2.03/0.65  fof(f222,plain,(
% 2.03/0.65    m1_connsp_2(sK2,sK0,sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl5_3 | ~spl5_4)),
% 2.03/0.65    inference(subsumption_resolution,[],[f208,f114])).
% 2.03/0.65  fof(f208,plain,(
% 2.03/0.65    m1_connsp_2(sK2,sK0,sK1) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl5_3),
% 2.03/0.65    inference(resolution,[],[f109,f64])).
% 2.03/0.65  fof(f192,plain,(
% 2.03/0.65    spl5_11 | ~spl5_2 | ~spl5_4 | ~spl5_5 | ~spl5_6 | spl5_7),
% 2.03/0.65    inference(avatar_split_clause,[],[f191,f127,f122,f117,f112,f102,f184])).
% 2.03/0.65  fof(f191,plain,(
% 2.03/0.65    m1_connsp_2(sK3,sK0,sK1) | (~spl5_2 | ~spl5_4 | ~spl5_5 | ~spl5_6 | spl5_7)),
% 2.03/0.65    inference(subsumption_resolution,[],[f190,f129])).
% 2.03/0.65  fof(f190,plain,(
% 2.03/0.65    m1_connsp_2(sK3,sK0,sK1) | v2_struct_0(sK0) | (~spl5_2 | ~spl5_4 | ~spl5_5 | ~spl5_6)),
% 2.03/0.65    inference(subsumption_resolution,[],[f189,f124])).
% 2.03/0.65  fof(f189,plain,(
% 2.03/0.65    m1_connsp_2(sK3,sK0,sK1) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl5_2 | ~spl5_4 | ~spl5_5)),
% 2.03/0.65    inference(subsumption_resolution,[],[f188,f119])).
% 2.03/0.65  fof(f188,plain,(
% 2.03/0.65    m1_connsp_2(sK3,sK0,sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl5_2 | ~spl5_4)),
% 2.03/0.65    inference(subsumption_resolution,[],[f174,f114])).
% 2.03/0.65  fof(f174,plain,(
% 2.03/0.65    m1_connsp_2(sK3,sK0,sK1) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl5_2),
% 2.03/0.65    inference(resolution,[],[f104,f64])).
% 2.03/0.65  fof(f130,plain,(
% 2.03/0.65    ~spl5_7),
% 2.03/0.65    inference(avatar_split_clause,[],[f52,f127])).
% 2.03/0.65  fof(f52,plain,(
% 2.03/0.65    ~v2_struct_0(sK0)),
% 2.03/0.65    inference(cnf_transformation,[],[f43])).
% 2.03/0.65  fof(f43,plain,(
% 2.03/0.65    (((~m1_subset_1(k2_xboole_0(sK2,sK3),u1_struct_0(k9_yellow_6(sK0,sK1))) & m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK0,sK1)))) & m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1)))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 2.03/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f19,f42,f41,f40,f39])).
% 2.03/0.65  fof(f39,plain,(
% 2.03/0.65    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(sK0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK0,X1)))) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 2.03/0.65    introduced(choice_axiom,[])).
% 2.03/0.65  fof(f40,plain,(
% 2.03/0.65    ? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(sK0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK0,X1)))) & m1_subset_1(X1,u1_struct_0(sK0))) => (? [X2] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(sK0,sK1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK0,sK1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK0,sK1)))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 2.03/0.65    introduced(choice_axiom,[])).
% 2.03/0.65  fof(f41,plain,(
% 2.03/0.65    ? [X2] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(sK0,sK1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK0,sK1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK0,sK1)))) => (? [X3] : (~m1_subset_1(k2_xboole_0(sK2,X3),u1_struct_0(k9_yellow_6(sK0,sK1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK0,sK1)))) & m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1))))),
% 2.03/0.65    introduced(choice_axiom,[])).
% 2.03/0.65  fof(f42,plain,(
% 2.03/0.65    ? [X3] : (~m1_subset_1(k2_xboole_0(sK2,X3),u1_struct_0(k9_yellow_6(sK0,sK1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK0,sK1)))) => (~m1_subset_1(k2_xboole_0(sK2,sK3),u1_struct_0(k9_yellow_6(sK0,sK1))) & m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK0,sK1))))),
% 2.03/0.65    introduced(choice_axiom,[])).
% 2.03/0.65  fof(f19,plain,(
% 2.03/0.65    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.03/0.65    inference(flattening,[],[f18])).
% 2.03/0.65  fof(f18,plain,(
% 2.03/0.65    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.03/0.65    inference(ennf_transformation,[],[f17])).
% 2.03/0.65  fof(f17,negated_conjecture,(
% 2.03/0.65    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) => m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))))))),
% 2.03/0.65    inference(negated_conjecture,[],[f16])).
% 2.03/0.65  fof(f16,conjecture,(
% 2.03/0.65    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) => m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))))))),
% 2.03/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_waybel_9)).
% 2.03/0.65  fof(f125,plain,(
% 2.03/0.65    spl5_6),
% 2.03/0.65    inference(avatar_split_clause,[],[f53,f122])).
% 2.03/0.65  fof(f53,plain,(
% 2.03/0.65    v2_pre_topc(sK0)),
% 2.03/0.65    inference(cnf_transformation,[],[f43])).
% 2.03/0.65  fof(f120,plain,(
% 2.03/0.65    spl5_5),
% 2.03/0.65    inference(avatar_split_clause,[],[f54,f117])).
% 2.03/0.65  fof(f54,plain,(
% 2.03/0.65    l1_pre_topc(sK0)),
% 2.03/0.65    inference(cnf_transformation,[],[f43])).
% 2.03/0.65  fof(f115,plain,(
% 2.03/0.65    spl5_4),
% 2.03/0.65    inference(avatar_split_clause,[],[f55,f112])).
% 2.03/0.65  fof(f55,plain,(
% 2.03/0.65    m1_subset_1(sK1,u1_struct_0(sK0))),
% 2.03/0.65    inference(cnf_transformation,[],[f43])).
% 2.03/0.65  fof(f110,plain,(
% 2.03/0.65    spl5_3),
% 2.03/0.65    inference(avatar_split_clause,[],[f56,f107])).
% 2.03/0.65  fof(f56,plain,(
% 2.03/0.65    m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 2.03/0.65    inference(cnf_transformation,[],[f43])).
% 2.03/0.65  fof(f105,plain,(
% 2.03/0.65    spl5_2),
% 2.03/0.65    inference(avatar_split_clause,[],[f57,f102])).
% 2.03/0.65  fof(f57,plain,(
% 2.03/0.65    m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 2.03/0.65    inference(cnf_transformation,[],[f43])).
% 2.03/0.65  fof(f100,plain,(
% 2.03/0.65    ~spl5_1),
% 2.03/0.65    inference(avatar_split_clause,[],[f84,f97])).
% 2.03/0.65  fof(f84,plain,(
% 2.03/0.65    ~m1_subset_1(k3_tarski(k2_tarski(sK2,sK3)),u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 2.03/0.65    inference(definition_unfolding,[],[f58,f66])).
% 2.03/0.65  fof(f58,plain,(
% 2.03/0.65    ~m1_subset_1(k2_xboole_0(sK2,sK3),u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 2.03/0.65    inference(cnf_transformation,[],[f43])).
% 2.03/0.65  % SZS output end Proof for theBenchmark
% 2.03/0.65  % (26444)------------------------------
% 2.03/0.65  % (26444)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.03/0.65  % (26444)Termination reason: Refutation
% 2.03/0.65  
% 2.03/0.65  % (26444)Memory used [KB]: 7675
% 2.03/0.65  % (26444)Time elapsed: 0.228 s
% 2.03/0.65  % (26444)------------------------------
% 2.03/0.65  % (26444)------------------------------
% 2.03/0.65  % (26417)Success in time 0.285 s
%------------------------------------------------------------------------------
