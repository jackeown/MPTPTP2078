%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:41 EST 2020

% Result     : Theorem 10.01s
% Output     : Refutation 10.01s
% Verified   : 
% Statistics : Number of formulae       :  141 ( 286 expanded)
%              Number of leaves         :   27 (  99 expanded)
%              Depth                    :   14
%              Number of atoms          :  521 (1262 expanded)
%              Number of equality atoms :   83 ( 228 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16450,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f113,f114,f119,f124,f129,f136,f231,f243,f1334,f1767,f1933,f1938,f1939,f13480,f16369,f16448])).

fof(f16448,plain,
    ( ~ spl4_3
    | ~ spl4_4
    | spl4_60
    | ~ spl4_260 ),
    inference(avatar_contradiction_clause,[],[f16447])).

fof(f16447,plain,
    ( $false
    | ~ spl4_3
    | ~ spl4_4
    | spl4_60
    | ~ spl4_260 ),
    inference(subsumption_resolution,[],[f16446,f123])).

fof(f123,plain,
    ( l1_pre_topc(sK0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl4_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f16446,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl4_3
    | spl4_60
    | ~ spl4_260 ),
    inference(subsumption_resolution,[],[f16445,f118])).

fof(f118,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl4_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f16445,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl4_60
    | ~ spl4_260 ),
    inference(subsumption_resolution,[],[f16384,f1343])).

fof(f1343,plain,
    ( sK1 != k1_tops_1(sK0,sK1)
    | spl4_60 ),
    inference(avatar_component_clause,[],[f1342])).

fof(f1342,plain,
    ( spl4_60
  <=> sK1 = k1_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_60])])).

fof(f16384,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_260 ),
    inference(superposition,[],[f296,f16368])).

fof(f16368,plain,
    ( sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl4_260 ),
    inference(avatar_component_clause,[],[f16366])).

fof(f16366,plain,
    ( spl4_260
  <=> sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_260])])).

fof(f296,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f295])).

fof(f295,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(superposition,[],[f63,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f16369,plain,
    ( spl4_260
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f16364,f214,f16366])).

fof(f214,plain,
    ( spl4_10
  <=> k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f16364,plain,
    ( sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl4_10 ),
    inference(duplicate_literal_removal,[],[f16339])).

fof(f16339,plain,
    ( sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl4_10 ),
    inference(resolution,[],[f1987,f252])).

fof(f252,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1,X0),X0)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(factoring,[],[f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X2),X2)
      | r2_hidden(sK2(X0,X1,X2),X0)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f50,f51])).

fof(f51,plain,(
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
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f49])).

fof(f49,plain,(
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
    inference(flattening,[],[f48])).

fof(f48,plain,(
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
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f1987,plain,
    ( ! [X2] :
        ( ~ r2_hidden(sK2(X2,k2_tops_1(sK0,sK1),X2),sK1)
        | k4_xboole_0(X2,k2_tops_1(sK0,sK1)) = X2 )
    | ~ spl4_10 ),
    inference(resolution,[],[f1951,f499])).

fof(f499,plain,(
    ! [X2,X1] :
      ( r2_hidden(sK2(X1,X2,X1),X2)
      | k4_xboole_0(X1,X2) = X1 ) ),
    inference(subsumption_resolution,[],[f497,f83])).

fof(f497,plain,(
    ! [X2,X1] :
      ( k4_xboole_0(X1,X2) = X1
      | r2_hidden(sK2(X1,X2,X1),X2)
      | ~ r2_hidden(sK2(X1,X2,X1),X1) ) ),
    inference(duplicate_literal_removal,[],[f487])).

fof(f487,plain,(
    ! [X2,X1] :
      ( k4_xboole_0(X1,X2) = X1
      | r2_hidden(sK2(X1,X2,X1),X2)
      | ~ r2_hidden(sK2(X1,X2,X1),X1)
      | k4_xboole_0(X1,X2) = X1 ) ),
    inference(resolution,[],[f252,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1,X2),X2)
      | r2_hidden(sK2(X0,X1,X2),X1)
      | ~ r2_hidden(sK2(X0,X1,X2),X0)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f1951,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k2_tops_1(sK0,sK1))
        | ~ r2_hidden(X1,sK1) )
    | ~ spl4_10 ),
    inference(superposition,[],[f100,f216])).

fof(f216,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f214])).

fof(f100,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f13480,plain,
    ( spl4_10
    | ~ spl4_2
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f13479,f210,f110,f214])).

fof(f110,plain,
    ( spl4_2
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f210,plain,
    ( spl4_9
  <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f13479,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl4_2
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f13476,f211])).

fof(f211,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f210])).

fof(f13476,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_2 ),
    inference(superposition,[],[f63,f111])).

fof(f111,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f110])).

fof(f1939,plain,
    ( ~ spl4_1
    | spl4_60
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_59 ),
    inference(avatar_split_clause,[],[f1787,f1338,f133,f121,f116,f1342,f106])).

fof(f106,plain,
    ( spl4_1
  <=> v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f133,plain,
    ( spl4_6
  <=> r1_tarski(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f1338,plain,
    ( spl4_59
  <=> r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_59])])).

fof(f1787,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ v3_pre_topc(sK1,sK0)
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_59 ),
    inference(subsumption_resolution,[],[f1786,f135])).

fof(f135,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f133])).

fof(f1786,plain,
    ( ~ r1_tarski(sK1,u1_struct_0(sK0))
    | sK1 = k1_tops_1(sK0,sK1)
    | ~ v3_pre_topc(sK1,sK0)
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_59 ),
    inference(subsumption_resolution,[],[f1783,f97])).

fof(f97,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f1783,plain,
    ( ~ r1_tarski(sK1,sK1)
    | ~ r1_tarski(sK1,u1_struct_0(sK0))
    | sK1 = k1_tops_1(sK0,sK1)
    | ~ v3_pre_topc(sK1,sK0)
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_59 ),
    inference(resolution,[],[f1339,f400])).

fof(f400,plain,
    ( ! [X2] :
        ( ~ r1_tarski(k1_tops_1(sK0,sK1),X2)
        | ~ r1_tarski(X2,sK1)
        | ~ r1_tarski(X2,u1_struct_0(sK0))
        | k1_tops_1(sK0,sK1) = X2
        | ~ v3_pre_topc(X2,sK0) )
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(resolution,[],[f341,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f341,plain,
    ( ! [X0] :
        ( r1_tarski(X0,k1_tops_1(sK0,sK1))
        | ~ v3_pre_topc(X0,sK0)
        | ~ r1_tarski(X0,sK1)
        | ~ r1_tarski(X0,u1_struct_0(sK0)) )
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(resolution,[],[f311,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f311,plain,
    ( ! [X10] :
        ( ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X10,sK0)
        | r1_tarski(X10,k1_tops_1(sK0,sK1))
        | ~ r1_tarski(X10,sK1) )
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f308,f123])).

fof(f308,plain,
    ( ! [X10] :
        ( ~ r1_tarski(X10,sK1)
        | ~ v3_pre_topc(X10,sK0)
        | r1_tarski(X10,k1_tops_1(sK0,sK1))
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl4_3 ),
    inference(resolution,[],[f76,f118])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X1,X2)
      | ~ v3_pre_topc(X1,X0)
      | r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_tarski(X1,X2)
                  & v3_pre_topc(X1,X0) )
               => r1_tarski(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tops_1)).

fof(f1339,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl4_59 ),
    inference(avatar_component_clause,[],[f1338])).

fof(f1938,plain,
    ( sK1 != k1_tops_1(sK0,sK1)
    | v3_pre_topc(sK1,sK0)
    | ~ v3_pre_topc(k1_tops_1(sK0,sK1),sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1933,plain,
    ( ~ spl4_3
    | ~ spl4_4
    | spl4_10
    | ~ spl4_60 ),
    inference(avatar_contradiction_clause,[],[f1932])).

fof(f1932,plain,
    ( $false
    | ~ spl4_3
    | ~ spl4_4
    | spl4_10
    | ~ spl4_60 ),
    inference(subsumption_resolution,[],[f1931,f123])).

fof(f1931,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl4_3
    | spl4_10
    | ~ spl4_60 ),
    inference(subsumption_resolution,[],[f1930,f118])).

fof(f1930,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl4_10
    | ~ spl4_60 ),
    inference(subsumption_resolution,[],[f1926,f215])).

fof(f215,plain,
    ( k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | spl4_10 ),
    inference(avatar_component_clause,[],[f214])).

fof(f1926,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_60 ),
    inference(superposition,[],[f302,f1344])).

fof(f1344,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ spl4_60 ),
    inference(avatar_component_clause,[],[f1342])).

fof(f302,plain,(
    ! [X2,X3] :
      ( k2_tops_1(X2,X3) = k4_xboole_0(k2_pre_topc(X2,X3),k1_tops_1(X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2) ) ),
    inference(subsumption_resolution,[],[f300,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f300,plain,(
    ! [X2,X3] :
      ( k2_tops_1(X2,X3) = k4_xboole_0(k2_pre_topc(X2,X3),k1_tops_1(X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(k2_pre_topc(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) ) ),
    inference(superposition,[],[f73,f63])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

fof(f1767,plain,
    ( spl4_59
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f1766,f121,f116,f1338])).

fof(f1766,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f1755,f123])).

fof(f1755,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl4_3 ),
    inference(resolution,[],[f535,f118])).

fof(f535,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | r1_tarski(k1_tops_1(X1,X0),X0)
      | ~ l1_pre_topc(X1) ) ),
    inference(superposition,[],[f86,f296])).

fof(f86,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f1334,plain,
    ( ~ spl4_10
    | spl4_2
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f1333,f210,f110,f214])).

fof(f1333,plain,
    ( k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | spl4_2
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f1332,f211])).

fof(f1332,plain,
    ( k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_2 ),
    inference(superposition,[],[f112,f63])).

fof(f112,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f110])).

fof(f243,plain,
    ( spl4_12
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f238,f126,f121,f116,f240])).

fof(f240,plain,
    ( spl4_12
  <=> v3_pre_topc(k1_tops_1(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f126,plain,
    ( spl4_5
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f238,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f237,f128])).

fof(f128,plain,
    ( v2_pre_topc(sK0)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f126])).

fof(f237,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f235,f123])).

fof(f235,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl4_3 ),
    inference(resolution,[],[f75,f118])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

fof(f231,plain,
    ( ~ spl4_3
    | ~ spl4_4
    | spl4_9 ),
    inference(avatar_contradiction_clause,[],[f230])).

fof(f230,plain,
    ( $false
    | ~ spl4_3
    | ~ spl4_4
    | spl4_9 ),
    inference(subsumption_resolution,[],[f229,f123])).

fof(f229,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl4_3
    | spl4_9 ),
    inference(subsumption_resolution,[],[f226,f118])).

fof(f226,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl4_9 ),
    inference(resolution,[],[f74,f212])).

fof(f212,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_9 ),
    inference(avatar_component_clause,[],[f210])).

fof(f136,plain,
    ( spl4_6
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f131,f116,f133])).

fof(f131,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl4_3 ),
    inference(resolution,[],[f77,f118])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f129,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f58,f126])).

fof(f58,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
      | ~ v3_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
      | v3_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f41,f43,f42])).

fof(f42,plain,
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

fof(f43,plain,
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

fof(f41,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_tops_1)).

fof(f124,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f59,f121])).

fof(f59,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f119,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f60,f116])).

fof(f60,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f44])).

fof(f114,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f61,f110,f106])).

fof(f61,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f113,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f62,f110,f106])).

fof(f62,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f44])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n008.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 17:47:15 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.20/0.48  % (15476)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.49  % (15472)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.53  % (15496)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.54  % (15473)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.55  % (15478)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.55  % (15485)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.55  % (15488)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.56  % (15488)Refutation not found, incomplete strategy% (15488)------------------------------
% 0.20/0.56  % (15488)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (15488)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (15488)Memory used [KB]: 10746
% 0.20/0.56  % (15488)Time elapsed: 0.151 s
% 0.20/0.56  % (15488)------------------------------
% 0.20/0.56  % (15488)------------------------------
% 0.20/0.56  % (15497)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.56  % (15474)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.56  % (15484)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.56  % (15481)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.57  % (15480)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.57  % (15493)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.57  % (15492)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.57  % (15477)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.58  % (15494)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.58  % (15475)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.58  % (15486)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.58  % (15495)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.60  % (15487)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.61  % (15500)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.61  % (15479)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.61  % (15499)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.61  % (15501)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.62  % (15499)Refutation not found, incomplete strategy% (15499)------------------------------
% 0.20/0.62  % (15499)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.62  % (15499)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.62  
% 0.20/0.62  % (15499)Memory used [KB]: 6268
% 0.20/0.62  % (15499)Time elapsed: 0.196 s
% 0.20/0.62  % (15499)------------------------------
% 0.20/0.62  % (15499)------------------------------
% 0.20/0.62  % (15491)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.62  % (15482)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.62  % (15489)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.63  % (15483)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.63  % (15498)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 2.01/0.63  % (15490)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 2.01/0.63  % (15500)Refutation not found, incomplete strategy% (15500)------------------------------
% 2.01/0.63  % (15500)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.01/0.63  % (15500)Termination reason: Refutation not found, incomplete strategy
% 2.01/0.63  
% 2.01/0.63  % (15500)Memory used [KB]: 10746
% 2.01/0.63  % (15500)Time elapsed: 0.199 s
% 2.01/0.63  % (15500)------------------------------
% 2.01/0.63  % (15500)------------------------------
% 2.01/0.64  % (15482)Refutation not found, incomplete strategy% (15482)------------------------------
% 2.01/0.64  % (15482)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.01/0.64  % (15482)Termination reason: Refutation not found, incomplete strategy
% 2.01/0.64  
% 2.01/0.64  % (15482)Memory used [KB]: 10874
% 2.01/0.64  % (15482)Time elapsed: 0.229 s
% 2.01/0.64  % (15482)------------------------------
% 2.01/0.64  % (15482)------------------------------
% 3.02/0.77  % (15538)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 3.02/0.78  % (15539)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 3.02/0.79  % (15541)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 3.02/0.80  % (15496)Time limit reached!
% 3.02/0.80  % (15496)------------------------------
% 3.02/0.80  % (15496)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.02/0.80  % (15496)Termination reason: Time limit
% 3.02/0.80  
% 3.02/0.80  % (15496)Memory used [KB]: 13432
% 3.02/0.80  % (15496)Time elapsed: 0.404 s
% 3.02/0.80  % (15496)------------------------------
% 3.02/0.80  % (15496)------------------------------
% 3.02/0.80  % (15542)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 3.02/0.82  % (15474)Time limit reached!
% 3.02/0.82  % (15474)------------------------------
% 3.02/0.82  % (15474)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.02/0.82  % (15474)Termination reason: Time limit
% 3.02/0.82  
% 3.02/0.82  % (15474)Memory used [KB]: 6396
% 3.02/0.82  % (15474)Time elapsed: 0.411 s
% 3.02/0.82  % (15474)------------------------------
% 3.02/0.82  % (15474)------------------------------
% 4.02/0.92  % (15501)Time limit reached!
% 4.02/0.92  % (15501)------------------------------
% 4.02/0.92  % (15501)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.02/0.92  % (15486)Time limit reached!
% 4.02/0.92  % (15486)------------------------------
% 4.02/0.92  % (15486)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.02/0.92  % (15501)Termination reason: Time limit
% 4.02/0.92  
% 4.02/0.92  % (15501)Memory used [KB]: 4733
% 4.02/0.92  % (15501)Time elapsed: 0.508 s
% 4.02/0.92  % (15501)------------------------------
% 4.02/0.92  % (15501)------------------------------
% 4.02/0.93  % (15486)Termination reason: Time limit
% 4.02/0.93  
% 4.02/0.93  % (15486)Memory used [KB]: 5245
% 4.02/0.93  % (15486)Time elapsed: 0.504 s
% 4.02/0.93  % (15486)------------------------------
% 4.02/0.93  % (15486)------------------------------
% 4.02/0.94  % (15478)Time limit reached!
% 4.02/0.94  % (15478)------------------------------
% 4.02/0.94  % (15478)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.02/0.94  % (15478)Termination reason: Time limit
% 4.02/0.94  % (15478)Termination phase: Saturation
% 4.02/0.94  
% 4.02/0.94  % (15478)Memory used [KB]: 16119
% 4.02/0.94  % (15478)Time elapsed: 0.500 s
% 4.02/0.94  % (15478)------------------------------
% 4.02/0.94  % (15478)------------------------------
% 4.02/0.94  % (15585)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 4.51/0.96  % (15594)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 4.77/1.02  % (15666)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 4.77/1.04  % (15668)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 5.03/1.06  % (15664)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 5.03/1.09  % (15479)Time limit reached!
% 5.03/1.09  % (15479)------------------------------
% 5.03/1.09  % (15479)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.03/1.09  % (15479)Termination reason: Time limit
% 5.03/1.09  % (15479)Termination phase: Saturation
% 5.03/1.09  
% 5.03/1.09  % (15479)Memory used [KB]: 4733
% 5.03/1.09  % (15479)Time elapsed: 0.600 s
% 5.03/1.09  % (15479)------------------------------
% 5.03/1.09  % (15479)------------------------------
% 6.65/1.22  % (15473)Time limit reached!
% 6.65/1.22  % (15473)------------------------------
% 6.65/1.22  % (15473)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.65/1.22  % (15724)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_4 on theBenchmark
% 6.65/1.22  % (15473)Termination reason: Time limit
% 6.65/1.22  % (15473)Termination phase: Saturation
% 6.65/1.22  
% 6.65/1.22  % (15473)Memory used [KB]: 7036
% 6.65/1.22  % (15473)Time elapsed: 0.800 s
% 6.65/1.22  % (15473)------------------------------
% 6.65/1.22  % (15473)------------------------------
% 7.13/1.31  % (15475)Time limit reached!
% 7.13/1.31  % (15475)------------------------------
% 7.13/1.31  % (15475)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.13/1.31  % (15475)Termination reason: Time limit
% 7.13/1.31  % (15475)Termination phase: Saturation
% 7.13/1.31  
% 7.13/1.31  % (15475)Memory used [KB]: 7164
% 7.13/1.31  % (15475)Time elapsed: 0.900 s
% 7.13/1.31  % (15475)------------------------------
% 7.13/1.31  % (15475)------------------------------
% 7.13/1.32  % (15778)lrs+1010_3:2_afr=on:afp=100000:afq=1.1:anc=none:gsp=input_only:irw=on:lwlo=on:nm=2:newcnf=on:nwc=1.7:stl=30:sac=on:sp=occurrence_95 on theBenchmark
% 8.17/1.41  % (15484)Time limit reached!
% 8.17/1.41  % (15484)------------------------------
% 8.17/1.41  % (15484)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.17/1.42  % (15484)Termination reason: Time limit
% 8.17/1.42  
% 8.17/1.42  % (15484)Memory used [KB]: 16502
% 8.17/1.42  % (15484)Time elapsed: 1.014 s
% 8.17/1.42  % (15484)------------------------------
% 8.17/1.42  % (15484)------------------------------
% 8.45/1.45  % (15779)lrs+1010_2_add=large:afp=4000:afq=2.0:amm=off:bd=off:bs=unit_only:bsr=on:br=off:fsr=off:gs=on:gsem=off:irw=on:lma=on:nm=32:nwc=1.1:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_80 on theBenchmark
% 8.45/1.47  % (15541)Time limit reached!
% 8.45/1.47  % (15541)------------------------------
% 8.45/1.47  % (15541)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.45/1.49  % (15541)Termination reason: Time limit
% 8.45/1.49  % (15541)Termination phase: Saturation
% 8.45/1.49  
% 8.45/1.49  % (15541)Memory used [KB]: 9466
% 8.45/1.49  % (15541)Time elapsed: 0.800 s
% 8.45/1.49  % (15541)------------------------------
% 8.45/1.49  % (15541)------------------------------
% 8.45/1.52  % (15780)lrs+1004_8:1_av=off:bd=off:fsr=off:lwlo=on:nm=4:nwc=1.5:stl=30:sd=1:ss=axioms:st=5.0:uhcvi=on_98 on theBenchmark
% 9.19/1.55  % (15664)Time limit reached!
% 9.19/1.55  % (15664)------------------------------
% 9.19/1.55  % (15664)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.19/1.55  % (15664)Termination reason: Time limit
% 9.19/1.55  % (15664)Termination phase: Saturation
% 9.19/1.55  
% 9.19/1.55  % (15664)Memory used [KB]: 15991
% 9.19/1.55  % (15664)Time elapsed: 0.604 s
% 9.19/1.55  % (15664)------------------------------
% 9.19/1.55  % (15664)------------------------------
% 9.56/1.60  % (15472)Time limit reached!
% 9.56/1.60  % (15472)------------------------------
% 9.56/1.60  % (15472)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.56/1.60  % (15781)lrs+1_2:3_aac=none:afr=on:afp=100000:afq=1.0:amm=sco:bd=off:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off:uhcvi=on_1 on theBenchmark
% 9.56/1.62  % (15472)Termination reason: Time limit
% 9.56/1.62  
% 9.56/1.62  % (15472)Memory used [KB]: 3326
% 9.56/1.62  % (15472)Time elapsed: 1.212 s
% 9.56/1.62  % (15472)------------------------------
% 9.56/1.62  % (15472)------------------------------
% 10.01/1.67  % (15782)lrs+1010_5_afr=on:afp=4000:afq=2.0:amm=sco:anc=none:bd=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=64:newcnf=on:nwc=4:sas=z3:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off_298 on theBenchmark
% 10.01/1.71  % (15477)Time limit reached!
% 10.01/1.71  % (15477)------------------------------
% 10.01/1.71  % (15477)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.01/1.73  % (15477)Termination reason: Time limit
% 10.01/1.73  % (15477)Termination phase: Saturation
% 10.01/1.73  
% 10.01/1.73  % (15477)Memory used [KB]: 5884
% 10.01/1.73  % (15477)Time elapsed: 1.300 s
% 10.01/1.73  % (15477)------------------------------
% 10.01/1.73  % (15477)------------------------------
% 10.01/1.74  % (15493)Refutation found. Thanks to Tanya!
% 10.01/1.74  % SZS status Theorem for theBenchmark
% 10.01/1.74  % SZS output start Proof for theBenchmark
% 10.01/1.74  fof(f16450,plain,(
% 10.01/1.74    $false),
% 10.01/1.74    inference(avatar_sat_refutation,[],[f113,f114,f119,f124,f129,f136,f231,f243,f1334,f1767,f1933,f1938,f1939,f13480,f16369,f16448])).
% 10.01/1.74  fof(f16448,plain,(
% 10.01/1.74    ~spl4_3 | ~spl4_4 | spl4_60 | ~spl4_260),
% 10.01/1.74    inference(avatar_contradiction_clause,[],[f16447])).
% 10.01/1.74  fof(f16447,plain,(
% 10.01/1.74    $false | (~spl4_3 | ~spl4_4 | spl4_60 | ~spl4_260)),
% 10.01/1.74    inference(subsumption_resolution,[],[f16446,f123])).
% 10.01/1.74  fof(f123,plain,(
% 10.01/1.74    l1_pre_topc(sK0) | ~spl4_4),
% 10.01/1.74    inference(avatar_component_clause,[],[f121])).
% 10.01/1.74  fof(f121,plain,(
% 10.01/1.74    spl4_4 <=> l1_pre_topc(sK0)),
% 10.01/1.74    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 10.01/1.74  fof(f16446,plain,(
% 10.01/1.74    ~l1_pre_topc(sK0) | (~spl4_3 | spl4_60 | ~spl4_260)),
% 10.01/1.74    inference(subsumption_resolution,[],[f16445,f118])).
% 10.01/1.74  fof(f118,plain,(
% 10.01/1.74    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_3),
% 10.01/1.74    inference(avatar_component_clause,[],[f116])).
% 10.01/1.74  fof(f116,plain,(
% 10.01/1.74    spl4_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 10.01/1.74    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 10.01/1.74  fof(f16445,plain,(
% 10.01/1.74    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (spl4_60 | ~spl4_260)),
% 10.01/1.74    inference(subsumption_resolution,[],[f16384,f1343])).
% 10.01/1.74  fof(f1343,plain,(
% 10.01/1.74    sK1 != k1_tops_1(sK0,sK1) | spl4_60),
% 10.01/1.74    inference(avatar_component_clause,[],[f1342])).
% 10.01/1.74  fof(f1342,plain,(
% 10.01/1.74    spl4_60 <=> sK1 = k1_tops_1(sK0,sK1)),
% 10.01/1.74    introduced(avatar_definition,[new_symbols(naming,[spl4_60])])).
% 10.01/1.74  fof(f16384,plain,(
% 10.01/1.74    sK1 = k1_tops_1(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl4_260),
% 10.01/1.74    inference(superposition,[],[f296,f16368])).
% 10.01/1.74  fof(f16368,plain,(
% 10.01/1.74    sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl4_260),
% 10.01/1.74    inference(avatar_component_clause,[],[f16366])).
% 10.01/1.74  fof(f16366,plain,(
% 10.01/1.74    spl4_260 <=> sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 10.01/1.74    introduced(avatar_definition,[new_symbols(naming,[spl4_260])])).
% 10.01/1.74  fof(f296,plain,(
% 10.01/1.74    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 10.01/1.74    inference(duplicate_literal_removal,[],[f295])).
% 10.01/1.74  fof(f295,plain,(
% 10.01/1.74    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 10.01/1.74    inference(superposition,[],[f63,f71])).
% 10.01/1.74  fof(f71,plain,(
% 10.01/1.74    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 10.01/1.74    inference(cnf_transformation,[],[f30])).
% 10.01/1.74  fof(f30,plain,(
% 10.01/1.74    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 10.01/1.74    inference(ennf_transformation,[],[f21])).
% 10.01/1.74  fof(f21,axiom,(
% 10.01/1.74    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 10.01/1.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).
% 10.01/1.74  fof(f63,plain,(
% 10.01/1.74    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 10.01/1.74    inference(cnf_transformation,[],[f26])).
% 10.01/1.74  fof(f26,plain,(
% 10.01/1.74    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 10.01/1.74    inference(ennf_transformation,[],[f13])).
% 10.01/1.74  fof(f13,axiom,(
% 10.01/1.74    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 10.01/1.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 10.01/1.74  fof(f16369,plain,(
% 10.01/1.74    spl4_260 | ~spl4_10),
% 10.01/1.74    inference(avatar_split_clause,[],[f16364,f214,f16366])).
% 10.01/1.74  fof(f214,plain,(
% 10.01/1.74    spl4_10 <=> k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)),
% 10.01/1.74    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 10.01/1.74  fof(f16364,plain,(
% 10.01/1.74    sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl4_10),
% 10.01/1.74    inference(duplicate_literal_removal,[],[f16339])).
% 10.01/1.74  fof(f16339,plain,(
% 10.01/1.74    sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl4_10),
% 10.01/1.74    inference(resolution,[],[f1987,f252])).
% 10.01/1.74  fof(f252,plain,(
% 10.01/1.74    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1,X0),X0) | k4_xboole_0(X0,X1) = X0) )),
% 10.01/1.74    inference(factoring,[],[f83])).
% 10.01/1.74  fof(f83,plain,(
% 10.01/1.74    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,X1,X2),X2) | r2_hidden(sK2(X0,X1,X2),X0) | k4_xboole_0(X0,X1) = X2) )),
% 10.01/1.74    inference(cnf_transformation,[],[f52])).
% 10.01/1.74  fof(f52,plain,(
% 10.01/1.74    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 10.01/1.74    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f50,f51])).
% 10.01/1.74  fof(f51,plain,(
% 10.01/1.74    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 10.01/1.74    introduced(choice_axiom,[])).
% 10.01/1.74  fof(f50,plain,(
% 10.01/1.74    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 10.01/1.74    inference(rectify,[],[f49])).
% 10.01/1.74  fof(f49,plain,(
% 10.01/1.74    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 10.01/1.74    inference(flattening,[],[f48])).
% 10.01/1.74  fof(f48,plain,(
% 10.01/1.74    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 10.01/1.74    inference(nnf_transformation,[],[f3])).
% 10.01/1.74  fof(f3,axiom,(
% 10.01/1.74    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 10.01/1.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 10.01/1.74  fof(f1987,plain,(
% 10.01/1.74    ( ! [X2] : (~r2_hidden(sK2(X2,k2_tops_1(sK0,sK1),X2),sK1) | k4_xboole_0(X2,k2_tops_1(sK0,sK1)) = X2) ) | ~spl4_10),
% 10.01/1.74    inference(resolution,[],[f1951,f499])).
% 10.01/1.74  fof(f499,plain,(
% 10.01/1.74    ( ! [X2,X1] : (r2_hidden(sK2(X1,X2,X1),X2) | k4_xboole_0(X1,X2) = X1) )),
% 10.01/1.74    inference(subsumption_resolution,[],[f497,f83])).
% 10.01/1.74  fof(f497,plain,(
% 10.01/1.74    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = X1 | r2_hidden(sK2(X1,X2,X1),X2) | ~r2_hidden(sK2(X1,X2,X1),X1)) )),
% 10.01/1.74    inference(duplicate_literal_removal,[],[f487])).
% 10.01/1.74  fof(f487,plain,(
% 10.01/1.74    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = X1 | r2_hidden(sK2(X1,X2,X1),X2) | ~r2_hidden(sK2(X1,X2,X1),X1) | k4_xboole_0(X1,X2) = X1) )),
% 10.01/1.74    inference(resolution,[],[f252,f85])).
% 10.01/1.74  fof(f85,plain,(
% 10.01/1.74    ( ! [X2,X0,X1] : (~r2_hidden(sK2(X0,X1,X2),X2) | r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | k4_xboole_0(X0,X1) = X2) )),
% 10.01/1.74    inference(cnf_transformation,[],[f52])).
% 10.01/1.74  fof(f1951,plain,(
% 10.01/1.74    ( ! [X1] : (~r2_hidden(X1,k2_tops_1(sK0,sK1)) | ~r2_hidden(X1,sK1)) ) | ~spl4_10),
% 10.01/1.74    inference(superposition,[],[f100,f216])).
% 10.01/1.74  fof(f216,plain,(
% 10.01/1.74    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~spl4_10),
% 10.01/1.74    inference(avatar_component_clause,[],[f214])).
% 10.01/1.74  fof(f100,plain,(
% 10.01/1.74    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 10.01/1.74    inference(equality_resolution,[],[f81])).
% 10.01/1.74  fof(f81,plain,(
% 10.01/1.74    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 10.01/1.74    inference(cnf_transformation,[],[f52])).
% 10.01/1.74  fof(f13480,plain,(
% 10.01/1.74    spl4_10 | ~spl4_2 | ~spl4_9),
% 10.01/1.74    inference(avatar_split_clause,[],[f13479,f210,f110,f214])).
% 10.01/1.74  fof(f110,plain,(
% 10.01/1.74    spl4_2 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)),
% 10.01/1.74    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 10.01/1.74  fof(f210,plain,(
% 10.01/1.74    spl4_9 <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 10.01/1.74    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 10.01/1.74  fof(f13479,plain,(
% 10.01/1.74    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | (~spl4_2 | ~spl4_9)),
% 10.01/1.74    inference(subsumption_resolution,[],[f13476,f211])).
% 10.01/1.74  fof(f211,plain,(
% 10.01/1.74    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_9),
% 10.01/1.74    inference(avatar_component_clause,[],[f210])).
% 10.01/1.74  fof(f13476,plain,(
% 10.01/1.74    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_2),
% 10.01/1.74    inference(superposition,[],[f63,f111])).
% 10.01/1.74  fof(f111,plain,(
% 10.01/1.74    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~spl4_2),
% 10.01/1.74    inference(avatar_component_clause,[],[f110])).
% 10.01/1.74  fof(f1939,plain,(
% 10.01/1.74    ~spl4_1 | spl4_60 | ~spl4_3 | ~spl4_4 | ~spl4_6 | ~spl4_59),
% 10.01/1.74    inference(avatar_split_clause,[],[f1787,f1338,f133,f121,f116,f1342,f106])).
% 10.01/1.74  fof(f106,plain,(
% 10.01/1.74    spl4_1 <=> v3_pre_topc(sK1,sK0)),
% 10.01/1.74    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 10.01/1.74  fof(f133,plain,(
% 10.01/1.74    spl4_6 <=> r1_tarski(sK1,u1_struct_0(sK0))),
% 10.01/1.74    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 10.01/1.74  fof(f1338,plain,(
% 10.01/1.74    spl4_59 <=> r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 10.01/1.74    introduced(avatar_definition,[new_symbols(naming,[spl4_59])])).
% 10.01/1.74  fof(f1787,plain,(
% 10.01/1.74    sK1 = k1_tops_1(sK0,sK1) | ~v3_pre_topc(sK1,sK0) | (~spl4_3 | ~spl4_4 | ~spl4_6 | ~spl4_59)),
% 10.01/1.74    inference(subsumption_resolution,[],[f1786,f135])).
% 10.01/1.74  fof(f135,plain,(
% 10.01/1.74    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl4_6),
% 10.01/1.74    inference(avatar_component_clause,[],[f133])).
% 10.01/1.74  fof(f1786,plain,(
% 10.01/1.74    ~r1_tarski(sK1,u1_struct_0(sK0)) | sK1 = k1_tops_1(sK0,sK1) | ~v3_pre_topc(sK1,sK0) | (~spl4_3 | ~spl4_4 | ~spl4_59)),
% 10.01/1.74    inference(subsumption_resolution,[],[f1783,f97])).
% 10.01/1.74  fof(f97,plain,(
% 10.01/1.74    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 10.01/1.74    inference(equality_resolution,[],[f65])).
% 10.01/1.74  fof(f65,plain,(
% 10.01/1.74    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 10.01/1.74    inference(cnf_transformation,[],[f46])).
% 10.01/1.74  fof(f46,plain,(
% 10.01/1.74    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 10.01/1.74    inference(flattening,[],[f45])).
% 10.01/1.74  fof(f45,plain,(
% 10.01/1.74    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 10.01/1.74    inference(nnf_transformation,[],[f4])).
% 10.01/1.74  fof(f4,axiom,(
% 10.01/1.74    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 10.01/1.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 10.01/1.74  fof(f1783,plain,(
% 10.01/1.74    ~r1_tarski(sK1,sK1) | ~r1_tarski(sK1,u1_struct_0(sK0)) | sK1 = k1_tops_1(sK0,sK1) | ~v3_pre_topc(sK1,sK0) | (~spl4_3 | ~spl4_4 | ~spl4_59)),
% 10.01/1.74    inference(resolution,[],[f1339,f400])).
% 10.01/1.74  fof(f400,plain,(
% 10.01/1.74    ( ! [X2] : (~r1_tarski(k1_tops_1(sK0,sK1),X2) | ~r1_tarski(X2,sK1) | ~r1_tarski(X2,u1_struct_0(sK0)) | k1_tops_1(sK0,sK1) = X2 | ~v3_pre_topc(X2,sK0)) ) | (~spl4_3 | ~spl4_4)),
% 10.01/1.74    inference(resolution,[],[f341,f66])).
% 10.01/1.74  fof(f66,plain,(
% 10.01/1.74    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 10.01/1.74    inference(cnf_transformation,[],[f46])).
% 10.01/1.74  fof(f341,plain,(
% 10.01/1.74    ( ! [X0] : (r1_tarski(X0,k1_tops_1(sK0,sK1)) | ~v3_pre_topc(X0,sK0) | ~r1_tarski(X0,sK1) | ~r1_tarski(X0,u1_struct_0(sK0))) ) | (~spl4_3 | ~spl4_4)),
% 10.01/1.74    inference(resolution,[],[f311,f78])).
% 10.01/1.74  fof(f78,plain,(
% 10.01/1.74    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 10.01/1.74    inference(cnf_transformation,[],[f47])).
% 10.01/1.74  fof(f47,plain,(
% 10.01/1.74    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 10.01/1.74    inference(nnf_transformation,[],[f15])).
% 10.01/1.74  fof(f15,axiom,(
% 10.01/1.74    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 10.01/1.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 10.01/1.74  fof(f311,plain,(
% 10.01/1.74    ( ! [X10] : (~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X10,sK0) | r1_tarski(X10,k1_tops_1(sK0,sK1)) | ~r1_tarski(X10,sK1)) ) | (~spl4_3 | ~spl4_4)),
% 10.01/1.74    inference(subsumption_resolution,[],[f308,f123])).
% 10.01/1.74  fof(f308,plain,(
% 10.01/1.74    ( ! [X10] : (~r1_tarski(X10,sK1) | ~v3_pre_topc(X10,sK0) | r1_tarski(X10,k1_tops_1(sK0,sK1)) | ~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) ) | ~spl4_3),
% 10.01/1.74    inference(resolution,[],[f76,f118])).
% 10.01/1.74  fof(f76,plain,(
% 10.01/1.74    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | r1_tarski(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 10.01/1.74    inference(cnf_transformation,[],[f38])).
% 10.01/1.74  fof(f38,plain,(
% 10.01/1.74    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 10.01/1.74    inference(flattening,[],[f37])).
% 10.01/1.74  fof(f37,plain,(
% 10.01/1.74    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(X1,k1_tops_1(X0,X2)) | (~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 10.01/1.74    inference(ennf_transformation,[],[f19])).
% 10.01/1.74  fof(f19,axiom,(
% 10.01/1.74    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v3_pre_topc(X1,X0)) => r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 10.01/1.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tops_1)).
% 10.01/1.74  fof(f1339,plain,(
% 10.01/1.74    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~spl4_59),
% 10.01/1.74    inference(avatar_component_clause,[],[f1338])).
% 10.01/1.74  fof(f1938,plain,(
% 10.01/1.74    sK1 != k1_tops_1(sK0,sK1) | v3_pre_topc(sK1,sK0) | ~v3_pre_topc(k1_tops_1(sK0,sK1),sK0)),
% 10.01/1.74    introduced(theory_tautology_sat_conflict,[])).
% 10.01/1.74  fof(f1933,plain,(
% 10.01/1.74    ~spl4_3 | ~spl4_4 | spl4_10 | ~spl4_60),
% 10.01/1.74    inference(avatar_contradiction_clause,[],[f1932])).
% 10.01/1.74  fof(f1932,plain,(
% 10.01/1.74    $false | (~spl4_3 | ~spl4_4 | spl4_10 | ~spl4_60)),
% 10.01/1.74    inference(subsumption_resolution,[],[f1931,f123])).
% 10.01/1.74  fof(f1931,plain,(
% 10.01/1.74    ~l1_pre_topc(sK0) | (~spl4_3 | spl4_10 | ~spl4_60)),
% 10.01/1.74    inference(subsumption_resolution,[],[f1930,f118])).
% 10.01/1.74  fof(f1930,plain,(
% 10.01/1.74    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (spl4_10 | ~spl4_60)),
% 10.01/1.74    inference(subsumption_resolution,[],[f1926,f215])).
% 10.01/1.74  fof(f215,plain,(
% 10.01/1.74    k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | spl4_10),
% 10.01/1.74    inference(avatar_component_clause,[],[f214])).
% 10.01/1.74  fof(f1926,plain,(
% 10.01/1.74    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl4_60),
% 10.01/1.74    inference(superposition,[],[f302,f1344])).
% 10.01/1.74  fof(f1344,plain,(
% 10.01/1.74    sK1 = k1_tops_1(sK0,sK1) | ~spl4_60),
% 10.01/1.74    inference(avatar_component_clause,[],[f1342])).
% 10.01/1.74  fof(f302,plain,(
% 10.01/1.74    ( ! [X2,X3] : (k2_tops_1(X2,X3) = k4_xboole_0(k2_pre_topc(X2,X3),k1_tops_1(X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2)) )),
% 10.01/1.74    inference(subsumption_resolution,[],[f300,f74])).
% 10.01/1.74  fof(f74,plain,(
% 10.01/1.74    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 10.01/1.74    inference(cnf_transformation,[],[f34])).
% 10.01/1.74  fof(f34,plain,(
% 10.01/1.74    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 10.01/1.74    inference(flattening,[],[f33])).
% 10.01/1.74  fof(f33,plain,(
% 10.01/1.74    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 10.01/1.74    inference(ennf_transformation,[],[f16])).
% 10.01/1.74  fof(f16,axiom,(
% 10.01/1.74    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 10.01/1.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 10.01/1.74  fof(f300,plain,(
% 10.01/1.74    ( ! [X2,X3] : (k2_tops_1(X2,X3) = k4_xboole_0(k2_pre_topc(X2,X3),k1_tops_1(X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2) | ~m1_subset_1(k2_pre_topc(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))) )),
% 10.01/1.74    inference(superposition,[],[f73,f63])).
% 10.01/1.74  fof(f73,plain,(
% 10.01/1.74    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 10.01/1.74    inference(cnf_transformation,[],[f32])).
% 10.01/1.74  fof(f32,plain,(
% 10.01/1.74    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 10.01/1.74    inference(ennf_transformation,[],[f18])).
% 10.01/1.74  fof(f18,axiom,(
% 10.01/1.74    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 10.01/1.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).
% 10.01/1.74  fof(f1767,plain,(
% 10.01/1.74    spl4_59 | ~spl4_3 | ~spl4_4),
% 10.01/1.74    inference(avatar_split_clause,[],[f1766,f121,f116,f1338])).
% 10.01/1.74  fof(f1766,plain,(
% 10.01/1.74    r1_tarski(k1_tops_1(sK0,sK1),sK1) | (~spl4_3 | ~spl4_4)),
% 10.01/1.74    inference(subsumption_resolution,[],[f1755,f123])).
% 10.01/1.74  fof(f1755,plain,(
% 10.01/1.74    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~l1_pre_topc(sK0) | ~spl4_3),
% 10.01/1.74    inference(resolution,[],[f535,f118])).
% 10.01/1.74  fof(f535,plain,(
% 10.01/1.74    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | r1_tarski(k1_tops_1(X1,X0),X0) | ~l1_pre_topc(X1)) )),
% 10.01/1.74    inference(superposition,[],[f86,f296])).
% 10.01/1.74  fof(f86,plain,(
% 10.01/1.74    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 10.01/1.74    inference(cnf_transformation,[],[f7])).
% 10.01/1.74  fof(f7,axiom,(
% 10.01/1.74    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 10.01/1.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 10.01/1.74  fof(f1334,plain,(
% 10.01/1.74    ~spl4_10 | spl4_2 | ~spl4_9),
% 10.01/1.74    inference(avatar_split_clause,[],[f1333,f210,f110,f214])).
% 10.01/1.74  fof(f1333,plain,(
% 10.01/1.74    k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | (spl4_2 | ~spl4_9)),
% 10.01/1.74    inference(subsumption_resolution,[],[f1332,f211])).
% 10.01/1.74  fof(f1332,plain,(
% 10.01/1.74    k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl4_2),
% 10.01/1.74    inference(superposition,[],[f112,f63])).
% 10.01/1.74  fof(f112,plain,(
% 10.01/1.74    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | spl4_2),
% 10.01/1.74    inference(avatar_component_clause,[],[f110])).
% 10.01/1.74  fof(f243,plain,(
% 10.01/1.74    spl4_12 | ~spl4_3 | ~spl4_4 | ~spl4_5),
% 10.01/1.74    inference(avatar_split_clause,[],[f238,f126,f121,f116,f240])).
% 10.01/1.74  fof(f240,plain,(
% 10.01/1.74    spl4_12 <=> v3_pre_topc(k1_tops_1(sK0,sK1),sK0)),
% 10.01/1.74    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 10.01/1.74  fof(f126,plain,(
% 10.01/1.74    spl4_5 <=> v2_pre_topc(sK0)),
% 10.01/1.74    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 10.01/1.74  fof(f238,plain,(
% 10.01/1.74    v3_pre_topc(k1_tops_1(sK0,sK1),sK0) | (~spl4_3 | ~spl4_4 | ~spl4_5)),
% 10.01/1.74    inference(subsumption_resolution,[],[f237,f128])).
% 10.01/1.74  fof(f128,plain,(
% 10.01/1.74    v2_pre_topc(sK0) | ~spl4_5),
% 10.01/1.74    inference(avatar_component_clause,[],[f126])).
% 10.01/1.74  fof(f237,plain,(
% 10.01/1.74    v3_pre_topc(k1_tops_1(sK0,sK1),sK0) | ~v2_pre_topc(sK0) | (~spl4_3 | ~spl4_4)),
% 10.01/1.74    inference(subsumption_resolution,[],[f235,f123])).
% 10.01/1.74  fof(f235,plain,(
% 10.01/1.74    v3_pre_topc(k1_tops_1(sK0,sK1),sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~spl4_3),
% 10.01/1.74    inference(resolution,[],[f75,f118])).
% 10.01/1.74  fof(f75,plain,(
% 10.01/1.74    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(k1_tops_1(X0,X1),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 10.01/1.74    inference(cnf_transformation,[],[f36])).
% 10.01/1.74  fof(f36,plain,(
% 10.01/1.74    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 10.01/1.74    inference(flattening,[],[f35])).
% 10.01/1.74  fof(f35,plain,(
% 10.01/1.74    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 10.01/1.74    inference(ennf_transformation,[],[f17])).
% 10.01/1.74  fof(f17,axiom,(
% 10.01/1.74    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 10.01/1.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).
% 10.01/1.74  fof(f231,plain,(
% 10.01/1.74    ~spl4_3 | ~spl4_4 | spl4_9),
% 10.01/1.74    inference(avatar_contradiction_clause,[],[f230])).
% 10.01/1.74  fof(f230,plain,(
% 10.01/1.74    $false | (~spl4_3 | ~spl4_4 | spl4_9)),
% 10.01/1.74    inference(subsumption_resolution,[],[f229,f123])).
% 10.01/1.74  fof(f229,plain,(
% 10.01/1.74    ~l1_pre_topc(sK0) | (~spl4_3 | spl4_9)),
% 10.01/1.74    inference(subsumption_resolution,[],[f226,f118])).
% 10.01/1.74  fof(f226,plain,(
% 10.01/1.74    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl4_9),
% 10.01/1.74    inference(resolution,[],[f74,f212])).
% 10.01/1.74  fof(f212,plain,(
% 10.01/1.74    ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl4_9),
% 10.01/1.74    inference(avatar_component_clause,[],[f210])).
% 10.01/1.74  fof(f136,plain,(
% 10.01/1.74    spl4_6 | ~spl4_3),
% 10.01/1.74    inference(avatar_split_clause,[],[f131,f116,f133])).
% 10.01/1.74  fof(f131,plain,(
% 10.01/1.74    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl4_3),
% 10.01/1.74    inference(resolution,[],[f77,f118])).
% 10.01/1.74  fof(f77,plain,(
% 10.01/1.74    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 10.01/1.74    inference(cnf_transformation,[],[f47])).
% 10.01/1.74  fof(f129,plain,(
% 10.01/1.74    spl4_5),
% 10.01/1.74    inference(avatar_split_clause,[],[f58,f126])).
% 10.01/1.74  fof(f58,plain,(
% 10.01/1.74    v2_pre_topc(sK0)),
% 10.01/1.74    inference(cnf_transformation,[],[f44])).
% 10.01/1.74  fof(f44,plain,(
% 10.01/1.74    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 10.01/1.74    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f41,f43,f42])).
% 10.01/1.74  fof(f42,plain,(
% 10.01/1.74    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | ~v3_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 10.01/1.74    introduced(choice_axiom,[])).
% 10.01/1.74  fof(f43,plain,(
% 10.01/1.74    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | ~v3_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 10.01/1.74    introduced(choice_axiom,[])).
% 10.01/1.74  fof(f41,plain,(
% 10.01/1.74    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 10.01/1.74    inference(flattening,[],[f40])).
% 10.01/1.74  fof(f40,plain,(
% 10.01/1.74    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 10.01/1.74    inference(nnf_transformation,[],[f25])).
% 10.01/1.74  fof(f25,plain,(
% 10.01/1.74    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 10.01/1.74    inference(flattening,[],[f24])).
% 10.01/1.74  fof(f24,plain,(
% 10.01/1.74    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 10.01/1.74    inference(ennf_transformation,[],[f23])).
% 10.01/1.74  fof(f23,negated_conjecture,(
% 10.01/1.74    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 10.01/1.74    inference(negated_conjecture,[],[f22])).
% 10.01/1.74  fof(f22,conjecture,(
% 10.01/1.74    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 10.01/1.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_tops_1)).
% 10.01/1.74  fof(f124,plain,(
% 10.01/1.74    spl4_4),
% 10.01/1.74    inference(avatar_split_clause,[],[f59,f121])).
% 10.01/1.74  fof(f59,plain,(
% 10.01/1.74    l1_pre_topc(sK0)),
% 10.01/1.74    inference(cnf_transformation,[],[f44])).
% 10.01/1.74  fof(f119,plain,(
% 10.01/1.74    spl4_3),
% 10.01/1.74    inference(avatar_split_clause,[],[f60,f116])).
% 10.01/1.74  fof(f60,plain,(
% 10.01/1.74    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 10.01/1.74    inference(cnf_transformation,[],[f44])).
% 10.01/1.74  fof(f114,plain,(
% 10.01/1.74    spl4_1 | spl4_2),
% 10.01/1.74    inference(avatar_split_clause,[],[f61,f110,f106])).
% 10.01/1.74  fof(f61,plain,(
% 10.01/1.74    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)),
% 10.01/1.74    inference(cnf_transformation,[],[f44])).
% 10.01/1.74  fof(f113,plain,(
% 10.01/1.74    ~spl4_1 | ~spl4_2),
% 10.01/1.74    inference(avatar_split_clause,[],[f62,f110,f106])).
% 10.01/1.74  fof(f62,plain,(
% 10.01/1.74    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)),
% 10.01/1.74    inference(cnf_transformation,[],[f44])).
% 10.01/1.74  % SZS output end Proof for theBenchmark
% 10.01/1.74  % (15493)------------------------------
% 10.01/1.74  % (15493)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.01/1.74  % (15493)Termination reason: Refutation
% 10.01/1.74  
% 10.01/1.74  % (15493)Memory used [KB]: 16502
% 10.01/1.74  % (15493)Time elapsed: 1.326 s
% 10.01/1.74  % (15493)------------------------------
% 10.01/1.74  % (15493)------------------------------
% 10.63/1.76  % (15471)Success in time 1.407 s
%------------------------------------------------------------------------------
