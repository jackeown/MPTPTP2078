%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:45 EST 2020

% Result     : Theorem 2.04s
% Output     : Refutation 2.04s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 339 expanded)
%              Number of leaves         :   19 ( 103 expanded)
%              Depth                    :   19
%              Number of atoms          :  430 (1746 expanded)
%              Number of equality atoms :   69 ( 374 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1355,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f107,f108,f115,f126,f163,f882,f903,f904,f916,f1354])).

fof(f1354,plain,
    ( spl8_6
    | ~ spl8_8 ),
    inference(avatar_contradiction_clause,[],[f1353])).

fof(f1353,plain,
    ( $false
    | spl8_6
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f1352,f61])).

fof(f61,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,
    ( ( k2_tops_1(sK4,sK5) != k7_subset_1(u1_struct_0(sK4),k2_pre_topc(sK4,sK5),sK5)
      | ~ v3_pre_topc(sK5,sK4) )
    & ( k2_tops_1(sK4,sK5) = k7_subset_1(u1_struct_0(sK4),k2_pre_topc(sK4,sK5),sK5)
      | v3_pre_topc(sK5,sK4) )
    & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    & l1_pre_topc(sK4)
    & v2_pre_topc(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f39,f41,f40])).

fof(f40,plain,
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
          ( ( k2_tops_1(sK4,X1) != k7_subset_1(u1_struct_0(sK4),k2_pre_topc(sK4,X1),X1)
            | ~ v3_pre_topc(X1,sK4) )
          & ( k2_tops_1(sK4,X1) = k7_subset_1(u1_struct_0(sK4),k2_pre_topc(sK4,X1),X1)
            | v3_pre_topc(X1,sK4) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) )
      & l1_pre_topc(sK4)
      & v2_pre_topc(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X1] :
        ( ( k2_tops_1(sK4,X1) != k7_subset_1(u1_struct_0(sK4),k2_pre_topc(sK4,X1),X1)
          | ~ v3_pre_topc(X1,sK4) )
        & ( k2_tops_1(sK4,X1) = k7_subset_1(u1_struct_0(sK4),k2_pre_topc(sK4,X1),X1)
          | v3_pre_topc(X1,sK4) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) )
   => ( ( k2_tops_1(sK4,sK5) != k7_subset_1(u1_struct_0(sK4),k2_pre_topc(sK4,sK5),sK5)
        | ~ v3_pre_topc(sK5,sK4) )
      & ( k2_tops_1(sK4,sK5) = k7_subset_1(u1_struct_0(sK4),k2_pre_topc(sK4,sK5),sK5)
        | v3_pre_topc(sK5,sK4) )
      & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_tops_1)).

fof(f1352,plain,
    ( ~ l1_pre_topc(sK4)
    | spl8_6
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f1351,f62])).

fof(f62,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f42])).

fof(f1351,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ l1_pre_topc(sK4)
    | spl8_6
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f1336,f142])).

fof(f142,plain,
    ( sK5 != k1_tops_1(sK4,sK5)
    | spl8_6 ),
    inference(avatar_component_clause,[],[f141])).

fof(f141,plain,
    ( spl8_6
  <=> sK5 = k1_tops_1(sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f1336,plain,
    ( sK5 = k1_tops_1(sK4,sK5)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ l1_pre_topc(sK4)
    | ~ spl8_8 ),
    inference(superposition,[],[f321,f1333])).

fof(f1333,plain,
    ( sK5 = k4_xboole_0(sK5,k2_tops_1(sK4,sK5))
    | ~ spl8_8 ),
    inference(resolution,[],[f1329,f96])).

fof(f96,plain,(
    ! [X0,X1] : sP3(X0,X1,k4_xboole_0(X0,X1)) ),
    inference(equality_resolution,[],[f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( sP3(X0,X1,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ~ sP3(X0,X1,X2) )
      & ( sP3(X0,X1,X2)
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> sP3(X0,X1,X2) ) ),
    inference(definition_folding,[],[f1,f36,f35])).

fof(f35,plain,(
    ! [X1,X3,X0] :
      ( sP2(X1,X3,X0)
    <=> ( ~ r2_hidden(X3,X1)
        & r2_hidden(X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( sP3(X0,X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> sP2(X1,X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f1329,plain,
    ( ! [X0] :
        ( ~ sP3(sK5,k2_tops_1(sK4,sK5),X0)
        | sK5 = X0 )
    | ~ spl8_8 ),
    inference(resolution,[],[f1328,f117])).

fof(f117,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP3(X0,X1,X3)
      | X2 = X3
      | ~ sP3(X0,X1,X2) ) ),
    inference(superposition,[],[f93,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f1328,plain,
    ( sP3(sK5,k2_tops_1(sK4,sK5),sK5)
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f1322,f208])).

fof(f208,plain,(
    ! [X4,X5,X3] :
      ( r2_hidden(sK7(X3,X4,X5),X5)
      | sP3(X3,X4,X5)
      | r2_hidden(sK7(X3,X4,X5),X3) ) ),
    inference(resolution,[],[f87,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ sP2(X0,X1,X2)
      | r2_hidden(X1,X2) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | r2_hidden(X1,X0)
        | ~ r2_hidden(X1,X2) )
      & ( ( ~ r2_hidden(X1,X0)
          & r2_hidden(X1,X2) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(rectify,[],[f57])).

fof(f57,plain,(
    ! [X1,X3,X0] :
      ( ( sP2(X1,X3,X0)
        | r2_hidden(X3,X1)
        | ~ r2_hidden(X3,X0) )
      & ( ( ~ r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
        | ~ sP2(X1,X3,X0) ) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X1,X3,X0] :
      ( ( sP2(X1,X3,X0)
        | r2_hidden(X3,X1)
        | ~ r2_hidden(X3,X0) )
      & ( ( ~ r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
        | ~ sP2(X1,X3,X0) ) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( sP2(X1,sK7(X0,X1,X2),X0)
      | sP3(X0,X1,X2)
      | r2_hidden(sK7(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( ( sP3(X0,X1,X2)
        | ( ( ~ sP2(X1,sK7(X0,X1,X2),X0)
            | ~ r2_hidden(sK7(X0,X1,X2),X2) )
          & ( sP2(X1,sK7(X0,X1,X2),X0)
            | r2_hidden(sK7(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP2(X1,X4,X0) )
            & ( sP2(X1,X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP3(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f53,f54])).

fof(f54,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ sP2(X1,X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( sP2(X1,X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ~ sP2(X1,sK7(X0,X1,X2),X0)
          | ~ r2_hidden(sK7(X0,X1,X2),X2) )
        & ( sP2(X1,sK7(X0,X1,X2),X0)
          | r2_hidden(sK7(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ( sP3(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP2(X1,X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP2(X1,X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP2(X1,X4,X0) )
            & ( sP2(X1,X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP3(X0,X1,X2) ) ) ),
    inference(rectify,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ( sP3(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP2(X1,X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP2(X1,X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ sP2(X1,X3,X0) )
            & ( sP2(X1,X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP3(X0,X1,X2) ) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f1322,plain,
    ( sP3(sK5,k2_tops_1(sK4,sK5),sK5)
    | ~ r2_hidden(sK7(sK5,k2_tops_1(sK4,sK5),sK5),sK5)
    | ~ spl8_8 ),
    inference(duplicate_literal_removal,[],[f1317])).

fof(f1317,plain,
    ( sP3(sK5,k2_tops_1(sK4,sK5),sK5)
    | ~ r2_hidden(sK7(sK5,k2_tops_1(sK4,sK5),sK5),sK5)
    | ~ r2_hidden(sK7(sK5,k2_tops_1(sK4,sK5),sK5),sK5)
    | sP3(sK5,k2_tops_1(sK4,sK5),sK5)
    | ~ spl8_8 ),
    inference(resolution,[],[f1253,f788])).

fof(f788,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(X0,X1,X0),X0)
      | sP3(X0,X1,X0) ) ),
    inference(factoring,[],[f208])).

fof(f1253,plain,
    ( ! [X48,X49] :
        ( ~ r2_hidden(sK7(X48,k2_tops_1(sK4,sK5),X49),sK5)
        | sP3(X48,k2_tops_1(sK4,sK5),X49)
        | ~ r2_hidden(sK7(X48,k2_tops_1(sK4,sK5),X49),X48)
        | ~ r2_hidden(sK7(X48,k2_tops_1(sK4,sK5),X49),X49) )
    | ~ spl8_8 ),
    inference(resolution,[],[f233,f190])).

fof(f190,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k2_tops_1(sK4,sK5))
        | ~ r2_hidden(X1,sK5) )
    | ~ spl8_8 ),
    inference(resolution,[],[f168,f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ sP2(X0,X1,X2)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f168,plain,
    ( ! [X1] :
        ( sP2(sK5,X1,k2_pre_topc(sK4,sK5))
        | ~ r2_hidden(X1,k2_tops_1(sK4,sK5)) )
    | ~ spl8_8 ),
    inference(superposition,[],[f127,f155])).

fof(f155,plain,
    ( k2_tops_1(sK4,sK5) = k4_xboole_0(k2_pre_topc(sK4,sK5),sK5)
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f153])).

fof(f153,plain,
    ( spl8_8
  <=> k2_tops_1(sK4,sK5) = k4_xboole_0(k2_pre_topc(sK4,sK5),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f127,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k4_xboole_0(X1,X2))
      | sP2(X2,X0,X1) ) ),
    inference(resolution,[],[f85,f96])).

fof(f85,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP3(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | sP2(X1,X4,X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f233,plain,(
    ! [X6,X4,X5] :
      ( r2_hidden(sK7(X4,X5,X6),X5)
      | ~ r2_hidden(sK7(X4,X5,X6),X6)
      | sP3(X4,X5,X6)
      | ~ r2_hidden(sK7(X4,X5,X6),X4) ) ),
    inference(resolution,[],[f88,f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( sP2(X0,X1,X2)
      | r2_hidden(X1,X0)
      | ~ r2_hidden(X1,X2) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ sP2(X1,sK7(X0,X1,X2),X0)
      | sP3(X0,X1,X2)
      | ~ r2_hidden(sK7(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f321,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f320])).

fof(f320,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(superposition,[],[f84,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f916,plain,
    ( spl8_8
    | ~ spl8_2
    | ~ spl8_7 ),
    inference(avatar_split_clause,[],[f915,f149,f104,f153])).

fof(f104,plain,
    ( spl8_2
  <=> k2_tops_1(sK4,sK5) = k7_subset_1(u1_struct_0(sK4),k2_pre_topc(sK4,sK5),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f149,plain,
    ( spl8_7
  <=> m1_subset_1(k2_pre_topc(sK4,sK5),k1_zfmisc_1(u1_struct_0(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f915,plain,
    ( k2_tops_1(sK4,sK5) = k4_xboole_0(k2_pre_topc(sK4,sK5),sK5)
    | ~ spl8_2
    | ~ spl8_7 ),
    inference(subsumption_resolution,[],[f912,f150])).

fof(f150,plain,
    ( m1_subset_1(k2_pre_topc(sK4,sK5),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f149])).

fof(f912,plain,
    ( k2_tops_1(sK4,sK5) = k4_xboole_0(k2_pre_topc(sK4,sK5),sK5)
    | ~ m1_subset_1(k2_pre_topc(sK4,sK5),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ spl8_2 ),
    inference(superposition,[],[f84,f105])).

fof(f105,plain,
    ( k2_tops_1(sK4,sK5) = k7_subset_1(u1_struct_0(sK4),k2_pre_topc(sK4,sK5),sK5)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f104])).

fof(f904,plain,
    ( ~ spl8_1
    | ~ spl8_4
    | spl8_6 ),
    inference(avatar_split_clause,[],[f875,f141,f113,f100])).

fof(f100,plain,
    ( spl8_1
  <=> v3_pre_topc(sK5,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f113,plain,
    ( spl8_4
  <=> ! [X1,X3] :
        ( k1_tops_1(X1,X3) = X3
        | ~ l1_pre_topc(X1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ v3_pre_topc(X3,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f875,plain,
    ( ~ v3_pre_topc(sK5,sK4)
    | ~ spl8_4
    | spl8_6 ),
    inference(subsumption_resolution,[],[f874,f142])).

fof(f874,plain,
    ( sK5 = k1_tops_1(sK4,sK5)
    | ~ v3_pre_topc(sK5,sK4)
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f196,f61])).

fof(f196,plain,
    ( ~ l1_pre_topc(sK4)
    | sK5 = k1_tops_1(sK4,sK5)
    | ~ v3_pre_topc(sK5,sK4)
    | ~ spl8_4 ),
    inference(resolution,[],[f114,f62])).

fof(f114,plain,
    ( ! [X3,X1] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ l1_pre_topc(X1)
        | k1_tops_1(X1,X3) = X3
        | ~ v3_pre_topc(X3,X1) )
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f113])).

fof(f903,plain,
    ( spl8_2
    | ~ spl8_6 ),
    inference(avatar_contradiction_clause,[],[f902])).

fof(f902,plain,
    ( $false
    | spl8_2
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f901,f61])).

fof(f901,plain,
    ( ~ l1_pre_topc(sK4)
    | spl8_2
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f900,f62])).

fof(f900,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ l1_pre_topc(sK4)
    | spl8_2
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f897,f106])).

fof(f106,plain,
    ( k2_tops_1(sK4,sK5) != k7_subset_1(u1_struct_0(sK4),k2_pre_topc(sK4,sK5),sK5)
    | spl8_2 ),
    inference(avatar_component_clause,[],[f104])).

fof(f897,plain,
    ( k2_tops_1(sK4,sK5) = k7_subset_1(u1_struct_0(sK4),k2_pre_topc(sK4,sK5),sK5)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ l1_pre_topc(sK4)
    | ~ spl8_6 ),
    inference(superposition,[],[f67,f143])).

fof(f143,plain,
    ( sK5 = k1_tops_1(sK4,sK5)
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f141])).

fof(f67,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

fof(f882,plain,
    ( ~ spl8_6
    | spl8_1 ),
    inference(avatar_split_clause,[],[f881,f100,f141])).

fof(f881,plain,
    ( v3_pre_topc(sK5,sK4)
    | sK5 != k1_tops_1(sK4,sK5) ),
    inference(subsumption_resolution,[],[f880,f60])).

fof(f60,plain,(
    v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f42])).

fof(f880,plain,
    ( v3_pre_topc(sK5,sK4)
    | sK5 != k1_tops_1(sK4,sK5)
    | ~ v2_pre_topc(sK4) ),
    inference(subsumption_resolution,[],[f275,f61])).

fof(f275,plain,
    ( v3_pre_topc(sK5,sK4)
    | sK5 != k1_tops_1(sK4,sK5)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(resolution,[],[f98,f62])).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | v3_pre_topc(X0,X1)
      | k1_tops_1(X1,X0) != X0
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1) ) ),
    inference(duplicate_literal_removal,[],[f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | v3_pre_topc(X0,X1)
      | k1_tops_1(X1,X0) != X0
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1) ) ),
    inference(condensation,[],[f70])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( v3_pre_topc(X2,X0)
      | k1_tops_1(X0,X2) != X2
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tops_1)).

fof(f163,plain,(
    spl8_7 ),
    inference(avatar_contradiction_clause,[],[f162])).

fof(f162,plain,
    ( $false
    | spl8_7 ),
    inference(subsumption_resolution,[],[f161,f61])).

fof(f161,plain,
    ( ~ l1_pre_topc(sK4)
    | spl8_7 ),
    inference(subsumption_resolution,[],[f160,f62])).

fof(f160,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ l1_pre_topc(sK4)
    | spl8_7 ),
    inference(resolution,[],[f151,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f151,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK4,sK5),k1_zfmisc_1(u1_struct_0(sK4)))
    | spl8_7 ),
    inference(avatar_component_clause,[],[f149])).

fof(f126,plain,(
    ~ spl8_3 ),
    inference(avatar_contradiction_clause,[],[f125])).

fof(f125,plain,
    ( $false
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f124,f61])).

fof(f124,plain,
    ( ~ l1_pre_topc(sK4)
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f123,f60])).

fof(f123,plain,
    ( ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK4)
    | ~ spl8_3 ),
    inference(resolution,[],[f111,f62])).

fof(f111,plain,
    ( ! [X2,X0] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl8_3
  <=> ! [X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f115,plain,
    ( spl8_3
    | spl8_4 ),
    inference(avatar_split_clause,[],[f69,f113,f110])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_tops_1(X1,X3) = X3
      | ~ v3_pre_topc(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f108,plain,
    ( spl8_1
    | spl8_2 ),
    inference(avatar_split_clause,[],[f63,f104,f100])).

fof(f63,plain,
    ( k2_tops_1(sK4,sK5) = k7_subset_1(u1_struct_0(sK4),k2_pre_topc(sK4,sK5),sK5)
    | v3_pre_topc(sK5,sK4) ),
    inference(cnf_transformation,[],[f42])).

fof(f107,plain,
    ( ~ spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f64,f104,f100])).

fof(f64,plain,
    ( k2_tops_1(sK4,sK5) != k7_subset_1(u1_struct_0(sK4),k2_pre_topc(sK4,sK5),sK5)
    | ~ v3_pre_topc(sK5,sK4) ),
    inference(cnf_transformation,[],[f42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:27:08 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.49  % (8063)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.49  % (8062)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.50  % (8054)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.50  % (8056)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.50  % (8051)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.50  % (8055)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.51  % (8058)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.51  % (8066)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.51  % (8059)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.51  % (8072)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.51  % (8052)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (8061)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.51  % (8053)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.52  % (8069)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.52  % (8067)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.28/0.53  % (8074)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.28/0.53  % (8065)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.28/0.53  % (8057)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.28/0.53  % (8070)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.28/0.53  % (8071)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.28/0.53  % (8064)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.28/0.53  % (8068)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.28/0.54  % (8077)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.44/0.54  % (8076)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.44/0.55  % (8073)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.44/0.55  % (8060)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 2.04/0.63  % (8055)Refutation found. Thanks to Tanya!
% 2.04/0.63  % SZS status Theorem for theBenchmark
% 2.04/0.63  % SZS output start Proof for theBenchmark
% 2.04/0.63  fof(f1355,plain,(
% 2.04/0.63    $false),
% 2.04/0.63    inference(avatar_sat_refutation,[],[f107,f108,f115,f126,f163,f882,f903,f904,f916,f1354])).
% 2.04/0.63  fof(f1354,plain,(
% 2.04/0.63    spl8_6 | ~spl8_8),
% 2.04/0.63    inference(avatar_contradiction_clause,[],[f1353])).
% 2.04/0.63  fof(f1353,plain,(
% 2.04/0.63    $false | (spl8_6 | ~spl8_8)),
% 2.04/0.63    inference(subsumption_resolution,[],[f1352,f61])).
% 2.04/0.63  fof(f61,plain,(
% 2.04/0.63    l1_pre_topc(sK4)),
% 2.04/0.63    inference(cnf_transformation,[],[f42])).
% 2.04/0.63  fof(f42,plain,(
% 2.04/0.63    ((k2_tops_1(sK4,sK5) != k7_subset_1(u1_struct_0(sK4),k2_pre_topc(sK4,sK5),sK5) | ~v3_pre_topc(sK5,sK4)) & (k2_tops_1(sK4,sK5) = k7_subset_1(u1_struct_0(sK4),k2_pre_topc(sK4,sK5),sK5) | v3_pre_topc(sK5,sK4)) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))) & l1_pre_topc(sK4) & v2_pre_topc(sK4)),
% 2.04/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f39,f41,f40])).
% 2.04/0.63  fof(f40,plain,(
% 2.04/0.63    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK4,X1) != k7_subset_1(u1_struct_0(sK4),k2_pre_topc(sK4,X1),X1) | ~v3_pre_topc(X1,sK4)) & (k2_tops_1(sK4,X1) = k7_subset_1(u1_struct_0(sK4),k2_pre_topc(sK4,X1),X1) | v3_pre_topc(X1,sK4)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))) & l1_pre_topc(sK4) & v2_pre_topc(sK4))),
% 2.04/0.63    introduced(choice_axiom,[])).
% 2.04/0.63  fof(f41,plain,(
% 2.04/0.63    ? [X1] : ((k2_tops_1(sK4,X1) != k7_subset_1(u1_struct_0(sK4),k2_pre_topc(sK4,X1),X1) | ~v3_pre_topc(X1,sK4)) & (k2_tops_1(sK4,X1) = k7_subset_1(u1_struct_0(sK4),k2_pre_topc(sK4,X1),X1) | v3_pre_topc(X1,sK4)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))) => ((k2_tops_1(sK4,sK5) != k7_subset_1(u1_struct_0(sK4),k2_pre_topc(sK4,sK5),sK5) | ~v3_pre_topc(sK5,sK4)) & (k2_tops_1(sK4,sK5) = k7_subset_1(u1_struct_0(sK4),k2_pre_topc(sK4,sK5),sK5) | v3_pre_topc(sK5,sK4)) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))))),
% 2.04/0.63    introduced(choice_axiom,[])).
% 2.04/0.63  fof(f39,plain,(
% 2.04/0.63    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.04/0.63    inference(flattening,[],[f38])).
% 2.04/0.63  fof(f38,plain,(
% 2.04/0.63    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.04/0.63    inference(nnf_transformation,[],[f16])).
% 2.04/0.63  fof(f16,plain,(
% 2.04/0.63    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.04/0.63    inference(flattening,[],[f15])).
% 2.04/0.63  fof(f15,plain,(
% 2.04/0.63    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 2.04/0.63    inference(ennf_transformation,[],[f14])).
% 2.04/0.63  fof(f14,negated_conjecture,(
% 2.04/0.63    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 2.04/0.63    inference(negated_conjecture,[],[f13])).
% 2.04/0.63  fof(f13,conjecture,(
% 2.04/0.63    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 2.04/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_tops_1)).
% 2.04/0.63  fof(f1352,plain,(
% 2.04/0.63    ~l1_pre_topc(sK4) | (spl8_6 | ~spl8_8)),
% 2.04/0.63    inference(subsumption_resolution,[],[f1351,f62])).
% 2.04/0.63  fof(f62,plain,(
% 2.04/0.63    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))),
% 2.04/0.63    inference(cnf_transformation,[],[f42])).
% 2.04/0.63  fof(f1351,plain,(
% 2.04/0.63    ~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) | ~l1_pre_topc(sK4) | (spl8_6 | ~spl8_8)),
% 2.04/0.63    inference(subsumption_resolution,[],[f1336,f142])).
% 2.04/0.63  fof(f142,plain,(
% 2.04/0.63    sK5 != k1_tops_1(sK4,sK5) | spl8_6),
% 2.04/0.63    inference(avatar_component_clause,[],[f141])).
% 2.04/0.63  fof(f141,plain,(
% 2.04/0.63    spl8_6 <=> sK5 = k1_tops_1(sK4,sK5)),
% 2.04/0.63    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 2.04/0.63  fof(f1336,plain,(
% 2.04/0.63    sK5 = k1_tops_1(sK4,sK5) | ~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) | ~l1_pre_topc(sK4) | ~spl8_8),
% 2.04/0.63    inference(superposition,[],[f321,f1333])).
% 2.04/0.63  fof(f1333,plain,(
% 2.04/0.63    sK5 = k4_xboole_0(sK5,k2_tops_1(sK4,sK5)) | ~spl8_8),
% 2.04/0.63    inference(resolution,[],[f1329,f96])).
% 2.04/0.63  fof(f96,plain,(
% 2.04/0.63    ( ! [X0,X1] : (sP3(X0,X1,k4_xboole_0(X0,X1))) )),
% 2.04/0.63    inference(equality_resolution,[],[f92])).
% 2.04/0.63  fof(f92,plain,(
% 2.04/0.63    ( ! [X2,X0,X1] : (sP3(X0,X1,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.04/0.63    inference(cnf_transformation,[],[f59])).
% 2.04/0.63  fof(f59,plain,(
% 2.04/0.63    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ~sP3(X0,X1,X2)) & (sP3(X0,X1,X2) | k4_xboole_0(X0,X1) != X2))),
% 2.04/0.63    inference(nnf_transformation,[],[f37])).
% 2.04/0.63  fof(f37,plain,(
% 2.04/0.63    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> sP3(X0,X1,X2))),
% 2.04/0.63    inference(definition_folding,[],[f1,f36,f35])).
% 2.04/0.63  fof(f35,plain,(
% 2.04/0.63    ! [X1,X3,X0] : (sP2(X1,X3,X0) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0)))),
% 2.04/0.63    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 2.04/0.63  fof(f36,plain,(
% 2.04/0.63    ! [X0,X1,X2] : (sP3(X0,X1,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> sP2(X1,X3,X0)))),
% 2.04/0.63    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 2.04/0.63  fof(f1,axiom,(
% 2.04/0.63    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.04/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 2.04/0.63  fof(f1329,plain,(
% 2.04/0.63    ( ! [X0] : (~sP3(sK5,k2_tops_1(sK4,sK5),X0) | sK5 = X0) ) | ~spl8_8),
% 2.04/0.63    inference(resolution,[],[f1328,f117])).
% 2.04/0.63  fof(f117,plain,(
% 2.04/0.63    ( ! [X2,X0,X3,X1] : (~sP3(X0,X1,X3) | X2 = X3 | ~sP3(X0,X1,X2)) )),
% 2.04/0.63    inference(superposition,[],[f93,f93])).
% 2.04/0.63  fof(f93,plain,(
% 2.04/0.63    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~sP3(X0,X1,X2)) )),
% 2.04/0.63    inference(cnf_transformation,[],[f59])).
% 2.04/0.63  fof(f1328,plain,(
% 2.04/0.63    sP3(sK5,k2_tops_1(sK4,sK5),sK5) | ~spl8_8),
% 2.04/0.63    inference(subsumption_resolution,[],[f1322,f208])).
% 2.04/0.63  fof(f208,plain,(
% 2.04/0.63    ( ! [X4,X5,X3] : (r2_hidden(sK7(X3,X4,X5),X5) | sP3(X3,X4,X5) | r2_hidden(sK7(X3,X4,X5),X3)) )),
% 2.04/0.63    inference(resolution,[],[f87,f89])).
% 2.04/0.63  fof(f89,plain,(
% 2.04/0.63    ( ! [X2,X0,X1] : (~sP2(X0,X1,X2) | r2_hidden(X1,X2)) )),
% 2.04/0.63    inference(cnf_transformation,[],[f58])).
% 2.04/0.63  fof(f58,plain,(
% 2.04/0.63    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | r2_hidden(X1,X0) | ~r2_hidden(X1,X2)) & ((~r2_hidden(X1,X0) & r2_hidden(X1,X2)) | ~sP2(X0,X1,X2)))),
% 2.04/0.63    inference(rectify,[],[f57])).
% 2.04/0.63  fof(f57,plain,(
% 2.04/0.63    ! [X1,X3,X0] : ((sP2(X1,X3,X0) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~sP2(X1,X3,X0)))),
% 2.04/0.63    inference(flattening,[],[f56])).
% 2.04/0.63  fof(f56,plain,(
% 2.04/0.63    ! [X1,X3,X0] : ((sP2(X1,X3,X0) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~sP2(X1,X3,X0)))),
% 2.04/0.63    inference(nnf_transformation,[],[f35])).
% 2.04/0.63  fof(f87,plain,(
% 2.04/0.63    ( ! [X2,X0,X1] : (sP2(X1,sK7(X0,X1,X2),X0) | sP3(X0,X1,X2) | r2_hidden(sK7(X0,X1,X2),X2)) )),
% 2.04/0.63    inference(cnf_transformation,[],[f55])).
% 2.04/0.63  fof(f55,plain,(
% 2.04/0.63    ! [X0,X1,X2] : ((sP3(X0,X1,X2) | ((~sP2(X1,sK7(X0,X1,X2),X0) | ~r2_hidden(sK7(X0,X1,X2),X2)) & (sP2(X1,sK7(X0,X1,X2),X0) | r2_hidden(sK7(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP2(X1,X4,X0)) & (sP2(X1,X4,X0) | ~r2_hidden(X4,X2))) | ~sP3(X0,X1,X2)))),
% 2.04/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f53,f54])).
% 2.04/0.63  fof(f54,plain,(
% 2.04/0.63    ! [X2,X1,X0] : (? [X3] : ((~sP2(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP2(X1,X3,X0) | r2_hidden(X3,X2))) => ((~sP2(X1,sK7(X0,X1,X2),X0) | ~r2_hidden(sK7(X0,X1,X2),X2)) & (sP2(X1,sK7(X0,X1,X2),X0) | r2_hidden(sK7(X0,X1,X2),X2))))),
% 2.04/0.63    introduced(choice_axiom,[])).
% 2.04/0.63  fof(f53,plain,(
% 2.04/0.63    ! [X0,X1,X2] : ((sP3(X0,X1,X2) | ? [X3] : ((~sP2(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP2(X1,X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP2(X1,X4,X0)) & (sP2(X1,X4,X0) | ~r2_hidden(X4,X2))) | ~sP3(X0,X1,X2)))),
% 2.04/0.63    inference(rectify,[],[f52])).
% 2.04/0.63  fof(f52,plain,(
% 2.04/0.63    ! [X0,X1,X2] : ((sP3(X0,X1,X2) | ? [X3] : ((~sP2(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP2(X1,X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~sP2(X1,X3,X0)) & (sP2(X1,X3,X0) | ~r2_hidden(X3,X2))) | ~sP3(X0,X1,X2)))),
% 2.04/0.63    inference(nnf_transformation,[],[f36])).
% 2.04/0.63  fof(f1322,plain,(
% 2.04/0.63    sP3(sK5,k2_tops_1(sK4,sK5),sK5) | ~r2_hidden(sK7(sK5,k2_tops_1(sK4,sK5),sK5),sK5) | ~spl8_8),
% 2.04/0.63    inference(duplicate_literal_removal,[],[f1317])).
% 2.04/0.63  fof(f1317,plain,(
% 2.04/0.63    sP3(sK5,k2_tops_1(sK4,sK5),sK5) | ~r2_hidden(sK7(sK5,k2_tops_1(sK4,sK5),sK5),sK5) | ~r2_hidden(sK7(sK5,k2_tops_1(sK4,sK5),sK5),sK5) | sP3(sK5,k2_tops_1(sK4,sK5),sK5) | ~spl8_8),
% 2.04/0.63    inference(resolution,[],[f1253,f788])).
% 2.04/0.63  fof(f788,plain,(
% 2.04/0.63    ( ! [X0,X1] : (r2_hidden(sK7(X0,X1,X0),X0) | sP3(X0,X1,X0)) )),
% 2.04/0.63    inference(factoring,[],[f208])).
% 2.04/0.63  fof(f1253,plain,(
% 2.04/0.63    ( ! [X48,X49] : (~r2_hidden(sK7(X48,k2_tops_1(sK4,sK5),X49),sK5) | sP3(X48,k2_tops_1(sK4,sK5),X49) | ~r2_hidden(sK7(X48,k2_tops_1(sK4,sK5),X49),X48) | ~r2_hidden(sK7(X48,k2_tops_1(sK4,sK5),X49),X49)) ) | ~spl8_8),
% 2.04/0.63    inference(resolution,[],[f233,f190])).
% 2.04/0.63  fof(f190,plain,(
% 2.04/0.63    ( ! [X1] : (~r2_hidden(X1,k2_tops_1(sK4,sK5)) | ~r2_hidden(X1,sK5)) ) | ~spl8_8),
% 2.04/0.63    inference(resolution,[],[f168,f90])).
% 2.04/0.63  fof(f90,plain,(
% 2.04/0.63    ( ! [X2,X0,X1] : (~sP2(X0,X1,X2) | ~r2_hidden(X1,X0)) )),
% 2.04/0.63    inference(cnf_transformation,[],[f58])).
% 2.04/0.63  fof(f168,plain,(
% 2.04/0.63    ( ! [X1] : (sP2(sK5,X1,k2_pre_topc(sK4,sK5)) | ~r2_hidden(X1,k2_tops_1(sK4,sK5))) ) | ~spl8_8),
% 2.04/0.63    inference(superposition,[],[f127,f155])).
% 2.04/0.63  fof(f155,plain,(
% 2.04/0.63    k2_tops_1(sK4,sK5) = k4_xboole_0(k2_pre_topc(sK4,sK5),sK5) | ~spl8_8),
% 2.04/0.63    inference(avatar_component_clause,[],[f153])).
% 2.04/0.63  fof(f153,plain,(
% 2.04/0.63    spl8_8 <=> k2_tops_1(sK4,sK5) = k4_xboole_0(k2_pre_topc(sK4,sK5),sK5)),
% 2.04/0.63    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 2.04/0.63  fof(f127,plain,(
% 2.04/0.63    ( ! [X2,X0,X1] : (~r2_hidden(X0,k4_xboole_0(X1,X2)) | sP2(X2,X0,X1)) )),
% 2.04/0.63    inference(resolution,[],[f85,f96])).
% 2.04/0.63  fof(f85,plain,(
% 2.04/0.63    ( ! [X4,X2,X0,X1] : (~sP3(X0,X1,X2) | ~r2_hidden(X4,X2) | sP2(X1,X4,X0)) )),
% 2.04/0.63    inference(cnf_transformation,[],[f55])).
% 2.04/0.63  fof(f233,plain,(
% 2.04/0.63    ( ! [X6,X4,X5] : (r2_hidden(sK7(X4,X5,X6),X5) | ~r2_hidden(sK7(X4,X5,X6),X6) | sP3(X4,X5,X6) | ~r2_hidden(sK7(X4,X5,X6),X4)) )),
% 2.04/0.63    inference(resolution,[],[f88,f91])).
% 2.04/0.63  fof(f91,plain,(
% 2.04/0.63    ( ! [X2,X0,X1] : (sP2(X0,X1,X2) | r2_hidden(X1,X0) | ~r2_hidden(X1,X2)) )),
% 2.04/0.63    inference(cnf_transformation,[],[f58])).
% 2.04/0.63  fof(f88,plain,(
% 2.04/0.63    ( ! [X2,X0,X1] : (~sP2(X1,sK7(X0,X1,X2),X0) | sP3(X0,X1,X2) | ~r2_hidden(sK7(X0,X1,X2),X2)) )),
% 2.04/0.63    inference(cnf_transformation,[],[f55])).
% 2.04/0.63  fof(f321,plain,(
% 2.04/0.63    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.04/0.63    inference(duplicate_literal_removal,[],[f320])).
% 2.04/0.63  fof(f320,plain,(
% 2.04/0.63    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.04/0.63    inference(superposition,[],[f84,f66])).
% 2.04/0.63  fof(f66,plain,(
% 2.04/0.63    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.04/0.63    inference(cnf_transformation,[],[f18])).
% 2.04/0.63  fof(f18,plain,(
% 2.04/0.63    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.04/0.63    inference(ennf_transformation,[],[f12])).
% 2.04/0.63  fof(f12,axiom,(
% 2.04/0.63    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 2.04/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).
% 2.04/0.63  fof(f84,plain,(
% 2.04/0.63    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.04/0.63    inference(cnf_transformation,[],[f31])).
% 2.04/0.63  fof(f31,plain,(
% 2.04/0.63    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.04/0.63    inference(ennf_transformation,[],[f4])).
% 2.04/0.63  fof(f4,axiom,(
% 2.04/0.63    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 2.04/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 2.04/0.63  fof(f916,plain,(
% 2.04/0.63    spl8_8 | ~spl8_2 | ~spl8_7),
% 2.04/0.63    inference(avatar_split_clause,[],[f915,f149,f104,f153])).
% 2.04/0.63  fof(f104,plain,(
% 2.04/0.63    spl8_2 <=> k2_tops_1(sK4,sK5) = k7_subset_1(u1_struct_0(sK4),k2_pre_topc(sK4,sK5),sK5)),
% 2.04/0.63    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 2.04/0.63  fof(f149,plain,(
% 2.04/0.63    spl8_7 <=> m1_subset_1(k2_pre_topc(sK4,sK5),k1_zfmisc_1(u1_struct_0(sK4)))),
% 2.04/0.63    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 2.04/0.63  fof(f915,plain,(
% 2.04/0.63    k2_tops_1(sK4,sK5) = k4_xboole_0(k2_pre_topc(sK4,sK5),sK5) | (~spl8_2 | ~spl8_7)),
% 2.04/0.63    inference(subsumption_resolution,[],[f912,f150])).
% 2.04/0.63  fof(f150,plain,(
% 2.04/0.63    m1_subset_1(k2_pre_topc(sK4,sK5),k1_zfmisc_1(u1_struct_0(sK4))) | ~spl8_7),
% 2.04/0.63    inference(avatar_component_clause,[],[f149])).
% 2.04/0.63  fof(f912,plain,(
% 2.04/0.63    k2_tops_1(sK4,sK5) = k4_xboole_0(k2_pre_topc(sK4,sK5),sK5) | ~m1_subset_1(k2_pre_topc(sK4,sK5),k1_zfmisc_1(u1_struct_0(sK4))) | ~spl8_2),
% 2.04/0.63    inference(superposition,[],[f84,f105])).
% 2.04/0.63  fof(f105,plain,(
% 2.04/0.63    k2_tops_1(sK4,sK5) = k7_subset_1(u1_struct_0(sK4),k2_pre_topc(sK4,sK5),sK5) | ~spl8_2),
% 2.04/0.63    inference(avatar_component_clause,[],[f104])).
% 2.04/0.63  fof(f904,plain,(
% 2.04/0.63    ~spl8_1 | ~spl8_4 | spl8_6),
% 2.04/0.63    inference(avatar_split_clause,[],[f875,f141,f113,f100])).
% 2.04/0.63  fof(f100,plain,(
% 2.04/0.63    spl8_1 <=> v3_pre_topc(sK5,sK4)),
% 2.04/0.63    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 2.04/0.63  fof(f113,plain,(
% 2.04/0.63    spl8_4 <=> ! [X1,X3] : (k1_tops_1(X1,X3) = X3 | ~l1_pre_topc(X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~v3_pre_topc(X3,X1))),
% 2.04/0.63    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 2.04/0.63  fof(f875,plain,(
% 2.04/0.63    ~v3_pre_topc(sK5,sK4) | (~spl8_4 | spl8_6)),
% 2.04/0.63    inference(subsumption_resolution,[],[f874,f142])).
% 2.04/0.63  fof(f874,plain,(
% 2.04/0.63    sK5 = k1_tops_1(sK4,sK5) | ~v3_pre_topc(sK5,sK4) | ~spl8_4),
% 2.04/0.63    inference(subsumption_resolution,[],[f196,f61])).
% 2.04/0.63  fof(f196,plain,(
% 2.04/0.63    ~l1_pre_topc(sK4) | sK5 = k1_tops_1(sK4,sK5) | ~v3_pre_topc(sK5,sK4) | ~spl8_4),
% 2.04/0.63    inference(resolution,[],[f114,f62])).
% 2.04/0.63  fof(f114,plain,(
% 2.04/0.63    ( ! [X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1)) ) | ~spl8_4),
% 2.04/0.63    inference(avatar_component_clause,[],[f113])).
% 2.04/0.63  fof(f903,plain,(
% 2.04/0.63    spl8_2 | ~spl8_6),
% 2.04/0.63    inference(avatar_contradiction_clause,[],[f902])).
% 2.04/0.63  fof(f902,plain,(
% 2.04/0.63    $false | (spl8_2 | ~spl8_6)),
% 2.04/0.63    inference(subsumption_resolution,[],[f901,f61])).
% 2.04/0.63  fof(f901,plain,(
% 2.04/0.63    ~l1_pre_topc(sK4) | (spl8_2 | ~spl8_6)),
% 2.04/0.63    inference(subsumption_resolution,[],[f900,f62])).
% 2.04/0.63  fof(f900,plain,(
% 2.04/0.63    ~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) | ~l1_pre_topc(sK4) | (spl8_2 | ~spl8_6)),
% 2.04/0.63    inference(subsumption_resolution,[],[f897,f106])).
% 2.04/0.63  fof(f106,plain,(
% 2.04/0.63    k2_tops_1(sK4,sK5) != k7_subset_1(u1_struct_0(sK4),k2_pre_topc(sK4,sK5),sK5) | spl8_2),
% 2.04/0.63    inference(avatar_component_clause,[],[f104])).
% 2.04/0.63  fof(f897,plain,(
% 2.04/0.63    k2_tops_1(sK4,sK5) = k7_subset_1(u1_struct_0(sK4),k2_pre_topc(sK4,sK5),sK5) | ~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) | ~l1_pre_topc(sK4) | ~spl8_6),
% 2.04/0.63    inference(superposition,[],[f67,f143])).
% 2.04/0.63  fof(f143,plain,(
% 2.04/0.63    sK5 = k1_tops_1(sK4,sK5) | ~spl8_6),
% 2.04/0.63    inference(avatar_component_clause,[],[f141])).
% 2.04/0.63  fof(f67,plain,(
% 2.04/0.63    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.04/0.63    inference(cnf_transformation,[],[f19])).
% 2.04/0.63  fof(f19,plain,(
% 2.04/0.63    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.04/0.63    inference(ennf_transformation,[],[f8])).
% 2.04/0.63  fof(f8,axiom,(
% 2.04/0.63    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 2.04/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).
% 2.04/0.63  fof(f882,plain,(
% 2.04/0.63    ~spl8_6 | spl8_1),
% 2.04/0.63    inference(avatar_split_clause,[],[f881,f100,f141])).
% 2.04/0.63  fof(f881,plain,(
% 2.04/0.63    v3_pre_topc(sK5,sK4) | sK5 != k1_tops_1(sK4,sK5)),
% 2.04/0.63    inference(subsumption_resolution,[],[f880,f60])).
% 2.04/0.63  fof(f60,plain,(
% 2.04/0.63    v2_pre_topc(sK4)),
% 2.04/0.63    inference(cnf_transformation,[],[f42])).
% 2.04/0.63  fof(f880,plain,(
% 2.04/0.63    v3_pre_topc(sK5,sK4) | sK5 != k1_tops_1(sK4,sK5) | ~v2_pre_topc(sK4)),
% 2.04/0.63    inference(subsumption_resolution,[],[f275,f61])).
% 2.04/0.63  fof(f275,plain,(
% 2.04/0.63    v3_pre_topc(sK5,sK4) | sK5 != k1_tops_1(sK4,sK5) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4)),
% 2.04/0.63    inference(resolution,[],[f98,f62])).
% 2.04/0.63  fof(f98,plain,(
% 2.04/0.63    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | v3_pre_topc(X0,X1) | k1_tops_1(X1,X0) != X0 | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) )),
% 2.04/0.63    inference(duplicate_literal_removal,[],[f97])).
% 2.04/0.63  fof(f97,plain,(
% 2.04/0.63    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | v3_pre_topc(X0,X1) | k1_tops_1(X1,X0) != X0 | ~l1_pre_topc(X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) )),
% 2.04/0.63    inference(condensation,[],[f70])).
% 2.04/0.63  fof(f70,plain,(
% 2.04/0.63    ( ! [X2,X0,X3,X1] : (v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.04/0.63    inference(cnf_transformation,[],[f23])).
% 2.04/0.63  fof(f23,plain,(
% 2.04/0.63    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.04/0.63    inference(flattening,[],[f22])).
% 2.04/0.63  fof(f22,plain,(
% 2.04/0.63    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.04/0.63    inference(ennf_transformation,[],[f10])).
% 2.04/0.63  fof(f10,axiom,(
% 2.04/0.63    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((k1_tops_1(X0,X2) = X2 => v3_pre_topc(X2,X0)) & (v3_pre_topc(X3,X1) => k1_tops_1(X1,X3) = X3))))))),
% 2.04/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tops_1)).
% 2.04/0.63  fof(f163,plain,(
% 2.04/0.63    spl8_7),
% 2.04/0.63    inference(avatar_contradiction_clause,[],[f162])).
% 2.04/0.63  fof(f162,plain,(
% 2.04/0.63    $false | spl8_7),
% 2.04/0.63    inference(subsumption_resolution,[],[f161,f61])).
% 2.04/0.63  fof(f161,plain,(
% 2.04/0.63    ~l1_pre_topc(sK4) | spl8_7),
% 2.04/0.63    inference(subsumption_resolution,[],[f160,f62])).
% 2.04/0.63  fof(f160,plain,(
% 2.04/0.63    ~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) | ~l1_pre_topc(sK4) | spl8_7),
% 2.04/0.63    inference(resolution,[],[f151,f78])).
% 2.04/0.63  fof(f78,plain,(
% 2.04/0.63    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.04/0.63    inference(cnf_transformation,[],[f27])).
% 2.04/0.63  fof(f27,plain,(
% 2.04/0.63    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 2.04/0.63    inference(flattening,[],[f26])).
% 2.04/0.63  fof(f26,plain,(
% 2.04/0.63    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 2.04/0.63    inference(ennf_transformation,[],[f6])).
% 2.04/0.63  fof(f6,axiom,(
% 2.04/0.63    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.04/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 2.04/0.63  fof(f151,plain,(
% 2.04/0.63    ~m1_subset_1(k2_pre_topc(sK4,sK5),k1_zfmisc_1(u1_struct_0(sK4))) | spl8_7),
% 2.04/0.63    inference(avatar_component_clause,[],[f149])).
% 2.04/0.63  fof(f126,plain,(
% 2.04/0.63    ~spl8_3),
% 2.04/0.63    inference(avatar_contradiction_clause,[],[f125])).
% 2.04/0.63  fof(f125,plain,(
% 2.04/0.63    $false | ~spl8_3),
% 2.04/0.63    inference(subsumption_resolution,[],[f124,f61])).
% 2.04/0.63  fof(f124,plain,(
% 2.04/0.63    ~l1_pre_topc(sK4) | ~spl8_3),
% 2.04/0.63    inference(subsumption_resolution,[],[f123,f60])).
% 2.04/0.63  fof(f123,plain,(
% 2.04/0.63    ~v2_pre_topc(sK4) | ~l1_pre_topc(sK4) | ~spl8_3),
% 2.04/0.63    inference(resolution,[],[f111,f62])).
% 2.04/0.63  fof(f111,plain,(
% 2.04/0.63    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0)) ) | ~spl8_3),
% 2.04/0.63    inference(avatar_component_clause,[],[f110])).
% 2.04/0.63  fof(f110,plain,(
% 2.04/0.63    spl8_3 <=> ! [X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0))),
% 2.04/0.63    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 2.04/0.63  fof(f115,plain,(
% 2.04/0.63    spl8_3 | spl8_4),
% 2.04/0.63    inference(avatar_split_clause,[],[f69,f113,f110])).
% 2.04/0.63  fof(f69,plain,(
% 2.04/0.63    ( ! [X2,X0,X3,X1] : (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.04/0.63    inference(cnf_transformation,[],[f23])).
% 2.04/0.63  fof(f108,plain,(
% 2.04/0.63    spl8_1 | spl8_2),
% 2.04/0.63    inference(avatar_split_clause,[],[f63,f104,f100])).
% 2.04/0.63  fof(f63,plain,(
% 2.04/0.63    k2_tops_1(sK4,sK5) = k7_subset_1(u1_struct_0(sK4),k2_pre_topc(sK4,sK5),sK5) | v3_pre_topc(sK5,sK4)),
% 2.04/0.63    inference(cnf_transformation,[],[f42])).
% 2.04/0.63  fof(f107,plain,(
% 2.04/0.63    ~spl8_1 | ~spl8_2),
% 2.04/0.63    inference(avatar_split_clause,[],[f64,f104,f100])).
% 2.04/0.63  fof(f64,plain,(
% 2.04/0.63    k2_tops_1(sK4,sK5) != k7_subset_1(u1_struct_0(sK4),k2_pre_topc(sK4,sK5),sK5) | ~v3_pre_topc(sK5,sK4)),
% 2.04/0.63    inference(cnf_transformation,[],[f42])).
% 2.04/0.63  % SZS output end Proof for theBenchmark
% 2.04/0.63  % (8055)------------------------------
% 2.04/0.63  % (8055)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.04/0.63  % (8055)Termination reason: Refutation
% 2.04/0.63  
% 2.04/0.63  % (8055)Memory used [KB]: 6780
% 2.04/0.63  % (8055)Time elapsed: 0.217 s
% 2.04/0.63  % (8055)------------------------------
% 2.04/0.63  % (8055)------------------------------
% 2.04/0.63  % (8050)Success in time 0.27 s
%------------------------------------------------------------------------------
