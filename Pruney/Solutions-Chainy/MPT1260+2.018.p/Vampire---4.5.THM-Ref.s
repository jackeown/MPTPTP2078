%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:35 EST 2020

% Result     : Theorem 1.89s
% Output     : Refutation 1.89s
% Verified   : 
% Statistics : Number of formulae       :  141 ( 295 expanded)
%              Number of leaves         :   28 ( 102 expanded)
%              Depth                    :   14
%              Number of atoms          :  512 (1282 expanded)
%              Number of equality atoms :   84 ( 233 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1507,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f106,f107,f112,f117,f122,f174,f319,f710,f893,f984,f1015,f1020,f1149,f1471,f1505,f1506])).

fof(f1506,plain,
    ( sK1 != k1_tops_1(sK0,sK1)
    | v3_pre_topc(sK1,sK0)
    | ~ v3_pre_topc(k1_tops_1(sK0,sK1),sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1505,plain,
    ( spl4_25
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_41 ),
    inference(avatar_split_clause,[],[f1504,f1468,f114,f109,f887])).

fof(f887,plain,
    ( spl4_25
  <=> sK1 = k1_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f109,plain,
    ( spl4_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f114,plain,
    ( spl4_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f1468,plain,
    ( spl4_41
  <=> sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).

fof(f1504,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_41 ),
    inference(subsumption_resolution,[],[f1503,f116])).

fof(f116,plain,
    ( l1_pre_topc(sK0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f114])).

fof(f1503,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl4_3
    | ~ spl4_41 ),
    inference(subsumption_resolution,[],[f1485,f111])).

fof(f111,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f109])).

fof(f1485,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_41 ),
    inference(superposition,[],[f210,f1470])).

fof(f1470,plain,
    ( sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl4_41 ),
    inference(avatar_component_clause,[],[f1468])).

fof(f210,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f209])).

fof(f209,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(superposition,[],[f59,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f1471,plain,
    ( spl4_41
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f1466,f160,f1468])).

fof(f160,plain,
    ( spl4_7
  <=> k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f1466,plain,
    ( sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl4_7 ),
    inference(duplicate_literal_removal,[],[f1457])).

fof(f1457,plain,
    ( sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl4_7 ),
    inference(resolution,[],[f1049,f181])).

fof(f181,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1,X0),X0)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(factoring,[],[f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X2),X2)
      | r2_hidden(sK2(X0,X1,X2),X0)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f46,f47])).

fof(f47,plain,(
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

fof(f46,plain,(
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
    inference(rectify,[],[f45])).

fof(f45,plain,(
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
    inference(flattening,[],[f44])).

fof(f44,plain,(
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

fof(f1049,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK2(X1,k2_tops_1(sK0,sK1),X1),sK1)
        | k4_xboole_0(X1,k2_tops_1(sK0,sK1)) = X1 )
    | ~ spl4_7 ),
    inference(resolution,[],[f1029,f285])).

fof(f285,plain,(
    ! [X2,X1] :
      ( r2_hidden(sK2(X1,X2,X1),X2)
      | k4_xboole_0(X1,X2) = X1 ) ),
    inference(subsumption_resolution,[],[f283,f74])).

fof(f283,plain,(
    ! [X2,X1] :
      ( k4_xboole_0(X1,X2) = X1
      | r2_hidden(sK2(X1,X2,X1),X2)
      | ~ r2_hidden(sK2(X1,X2,X1),X1) ) ),
    inference(duplicate_literal_removal,[],[f277])).

fof(f277,plain,(
    ! [X2,X1] :
      ( k4_xboole_0(X1,X2) = X1
      | r2_hidden(sK2(X1,X2,X1),X2)
      | ~ r2_hidden(sK2(X1,X2,X1),X1)
      | k4_xboole_0(X1,X2) = X1 ) ),
    inference(resolution,[],[f181,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1,X2),X2)
      | r2_hidden(sK2(X0,X1,X2),X1)
      | ~ r2_hidden(sK2(X0,X1,X2),X0)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f1029,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k2_tops_1(sK0,sK1))
        | ~ r2_hidden(X1,sK1) )
    | ~ spl4_7 ),
    inference(superposition,[],[f93,f162])).

fof(f162,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f160])).

fof(f93,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f1149,plain,
    ( spl4_7
    | ~ spl4_2
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f1148,f156,f103,f160])).

fof(f103,plain,
    ( spl4_2
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f156,plain,
    ( spl4_6
  <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f1148,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl4_2
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f1145,f157])).

fof(f157,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f156])).

fof(f1145,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_2 ),
    inference(superposition,[],[f59,f104])).

fof(f104,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f103])).

fof(f1020,plain,
    ( ~ spl4_19
    | spl4_25
    | ~ spl4_24 ),
    inference(avatar_split_clause,[],[f991,f883,f887,f707])).

fof(f707,plain,
    ( spl4_19
  <=> r1_tarski(sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f883,plain,
    ( spl4_24
  <=> r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f991,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | ~ spl4_24 ),
    inference(resolution,[],[f884,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f884,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f883])).

fof(f1015,plain,
    ( ~ spl4_3
    | ~ spl4_4
    | spl4_7
    | ~ spl4_25 ),
    inference(avatar_contradiction_clause,[],[f1014])).

fof(f1014,plain,
    ( $false
    | ~ spl4_3
    | ~ spl4_4
    | spl4_7
    | ~ spl4_25 ),
    inference(subsumption_resolution,[],[f1013,f116])).

fof(f1013,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl4_3
    | spl4_7
    | ~ spl4_25 ),
    inference(subsumption_resolution,[],[f1012,f111])).

fof(f1012,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl4_7
    | ~ spl4_25 ),
    inference(subsumption_resolution,[],[f1010,f161])).

fof(f161,plain,
    ( k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | spl4_7 ),
    inference(avatar_component_clause,[],[f160])).

fof(f1010,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_25 ),
    inference(superposition,[],[f569,f889])).

fof(f889,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f887])).

fof(f569,plain,(
    ! [X2,X3] :
      ( k2_tops_1(X2,X3) = k4_xboole_0(k2_pre_topc(X2,X3),k1_tops_1(X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2) ) ),
    inference(subsumption_resolution,[],[f217,f214])).

fof(f214,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f213,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f213,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f212])).

fof(f212,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(superposition,[],[f70,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

fof(f70,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).

fof(f217,plain,(
    ! [X2,X3] :
      ( k2_tops_1(X2,X3) = k4_xboole_0(k2_pre_topc(X2,X3),k1_tops_1(X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(k2_pre_topc(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) ) ),
    inference(superposition,[],[f64,f59])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

fof(f984,plain,
    ( spl4_24
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f983,f114,f109,f883])).

fof(f983,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f971,f116])).

fof(f971,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl4_3 ),
    inference(resolution,[],[f369,f111])).

fof(f369,plain,(
    ! [X12,X11] :
      ( ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X12)))
      | r1_tarski(k1_tops_1(X12,X11),X11)
      | ~ l1_pre_topc(X12) ) ),
    inference(superposition,[],[f78,f210])).

fof(f78,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f893,plain,
    ( ~ spl4_7
    | spl4_2
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f892,f156,f103,f160])).

fof(f892,plain,
    ( k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | spl4_2
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f891,f157])).

fof(f891,plain,
    ( k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_2 ),
    inference(superposition,[],[f105,f59])).

fof(f105,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f103])).

fof(f710,plain,
    ( spl4_19
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f705,f114,f109,f99,f707])).

fof(f99,plain,
    ( spl4_1
  <=> v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f705,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f232,f90])).

fof(f90,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f232,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | ~ r1_tarski(sK1,sK1)
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(resolution,[],[f227,f111])).

fof(f227,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X0,sK0)
        | r1_tarski(X0,k1_tops_1(sK0,sK1))
        | ~ r1_tarski(X0,sK1) )
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f223,f116])).

fof(f223,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | ~ v3_pre_topc(X0,sK0)
        | r1_tarski(X0,k1_tops_1(sK0,sK1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl4_3 ),
    inference(resolution,[],[f69,f111])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X1,X2)
      | ~ v3_pre_topc(X1,X0)
      | r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_tarski(X1,X2)
                  & v3_pre_topc(X1,X0) )
               => r1_tarski(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_1)).

fof(f319,plain,
    ( ~ spl4_3
    | ~ spl4_4
    | spl4_6 ),
    inference(avatar_contradiction_clause,[],[f318])).

fof(f318,plain,
    ( $false
    | ~ spl4_3
    | ~ spl4_4
    | spl4_6 ),
    inference(subsumption_resolution,[],[f317,f116])).

fof(f317,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl4_3
    | spl4_6 ),
    inference(subsumption_resolution,[],[f310,f111])).

fof(f310,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl4_6 ),
    inference(resolution,[],[f214,f158])).

fof(f158,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_6 ),
    inference(avatar_component_clause,[],[f156])).

fof(f174,plain,
    ( spl4_8
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f169,f119,f114,f109,f171])).

fof(f171,plain,
    ( spl4_8
  <=> v3_pre_topc(k1_tops_1(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f119,plain,
    ( spl4_5
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f169,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f168,f121])).

fof(f121,plain,
    ( v2_pre_topc(sK0)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f119])).

fof(f168,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f165,f116])).

fof(f165,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl4_3 ),
    inference(resolution,[],[f68,f111])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

fof(f122,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f54,f119])).

fof(f54,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
      | ~ v3_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
      | v3_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f38,f40,f39])).

fof(f39,plain,
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

fof(f40,plain,
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
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_1)).

fof(f117,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f55,f114])).

fof(f55,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f112,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f56,f109])).

fof(f56,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f41])).

fof(f107,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f57,f103,f99])).

fof(f57,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f106,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f58,f103,f99])).

fof(f58,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f41])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:07:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.50  % (21249)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.50  % (21229)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.52  % (21242)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.52  % (21249)Refutation not found, incomplete strategy% (21249)------------------------------
% 0.20/0.52  % (21249)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (21249)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (21249)Memory used [KB]: 10746
% 0.20/0.52  % (21249)Time elapsed: 0.104 s
% 0.20/0.52  % (21249)------------------------------
% 0.20/0.52  % (21249)------------------------------
% 0.20/0.52  % (21224)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.53  % (21223)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.53  % (21232)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.54  % (21245)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.54  % (21222)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.54  % (21247)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.54  % (21238)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.54  % (21227)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.54  % (21226)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.55  % (21225)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.55  % (21236)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.55  % (21237)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.55  % (21246)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.55  % (21237)Refutation not found, incomplete strategy% (21237)------------------------------
% 0.20/0.55  % (21237)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (21237)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (21237)Memory used [KB]: 10746
% 0.20/0.55  % (21237)Time elapsed: 0.134 s
% 0.20/0.55  % (21237)------------------------------
% 0.20/0.55  % (21237)------------------------------
% 0.20/0.55  % (21243)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.55  % (21228)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.55  % (21231)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.56  % (21235)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.56  % (21233)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.56  % (21231)Refutation not found, incomplete strategy% (21231)------------------------------
% 0.20/0.56  % (21231)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (21231)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (21231)Memory used [KB]: 10746
% 0.20/0.56  % (21231)Time elapsed: 0.137 s
% 0.20/0.56  % (21231)------------------------------
% 0.20/0.56  % (21231)------------------------------
% 0.20/0.56  % (21240)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.56  % (21250)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.56  % (21250)Refutation not found, incomplete strategy% (21250)------------------------------
% 0.20/0.56  % (21250)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (21250)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (21250)Memory used [KB]: 1663
% 0.20/0.56  % (21250)Time elapsed: 0.001 s
% 0.20/0.56  % (21250)------------------------------
% 0.20/0.56  % (21250)------------------------------
% 0.20/0.56  % (21230)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.56  % (21221)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.56  % (21234)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.57  % (21244)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.57  % (21241)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.57  % (21239)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.57  % (21248)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.89/0.63  % (21242)Refutation found. Thanks to Tanya!
% 1.89/0.63  % SZS status Theorem for theBenchmark
% 1.89/0.64  % SZS output start Proof for theBenchmark
% 1.89/0.64  fof(f1507,plain,(
% 1.89/0.64    $false),
% 1.89/0.64    inference(avatar_sat_refutation,[],[f106,f107,f112,f117,f122,f174,f319,f710,f893,f984,f1015,f1020,f1149,f1471,f1505,f1506])).
% 1.89/0.64  fof(f1506,plain,(
% 1.89/0.64    sK1 != k1_tops_1(sK0,sK1) | v3_pre_topc(sK1,sK0) | ~v3_pre_topc(k1_tops_1(sK0,sK1),sK0)),
% 1.89/0.64    introduced(theory_tautology_sat_conflict,[])).
% 1.89/0.64  fof(f1505,plain,(
% 1.89/0.64    spl4_25 | ~spl4_3 | ~spl4_4 | ~spl4_41),
% 1.89/0.64    inference(avatar_split_clause,[],[f1504,f1468,f114,f109,f887])).
% 1.89/0.64  fof(f887,plain,(
% 1.89/0.64    spl4_25 <=> sK1 = k1_tops_1(sK0,sK1)),
% 1.89/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 1.89/0.64  fof(f109,plain,(
% 1.89/0.64    spl4_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.89/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.89/0.64  fof(f114,plain,(
% 1.89/0.64    spl4_4 <=> l1_pre_topc(sK0)),
% 1.89/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.89/0.64  fof(f1468,plain,(
% 1.89/0.64    spl4_41 <=> sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 1.89/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).
% 1.89/0.64  fof(f1504,plain,(
% 1.89/0.64    sK1 = k1_tops_1(sK0,sK1) | (~spl4_3 | ~spl4_4 | ~spl4_41)),
% 1.89/0.64    inference(subsumption_resolution,[],[f1503,f116])).
% 1.89/0.64  fof(f116,plain,(
% 1.89/0.64    l1_pre_topc(sK0) | ~spl4_4),
% 1.89/0.64    inference(avatar_component_clause,[],[f114])).
% 1.89/0.64  fof(f1503,plain,(
% 1.89/0.64    sK1 = k1_tops_1(sK0,sK1) | ~l1_pre_topc(sK0) | (~spl4_3 | ~spl4_41)),
% 1.89/0.64    inference(subsumption_resolution,[],[f1485,f111])).
% 1.89/0.64  fof(f111,plain,(
% 1.89/0.64    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_3),
% 1.89/0.64    inference(avatar_component_clause,[],[f109])).
% 1.89/0.64  fof(f1485,plain,(
% 1.89/0.64    sK1 = k1_tops_1(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl4_41),
% 1.89/0.64    inference(superposition,[],[f210,f1470])).
% 1.89/0.64  fof(f1470,plain,(
% 1.89/0.64    sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl4_41),
% 1.89/0.64    inference(avatar_component_clause,[],[f1468])).
% 1.89/0.64  fof(f210,plain,(
% 1.89/0.64    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.89/0.64    inference(duplicate_literal_removal,[],[f209])).
% 1.89/0.64  fof(f209,plain,(
% 1.89/0.64    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.89/0.64    inference(superposition,[],[f59,f65])).
% 1.89/0.64  fof(f65,plain,(
% 1.89/0.64    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.89/0.64    inference(cnf_transformation,[],[f27])).
% 1.89/0.64  fof(f27,plain,(
% 1.89/0.64    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.89/0.64    inference(ennf_transformation,[],[f19])).
% 1.89/0.64  fof(f19,axiom,(
% 1.89/0.64    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 1.89/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).
% 1.89/0.64  fof(f59,plain,(
% 1.89/0.64    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.89/0.64    inference(cnf_transformation,[],[f25])).
% 1.89/0.64  fof(f25,plain,(
% 1.89/0.64    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.89/0.64    inference(ennf_transformation,[],[f12])).
% 1.89/0.64  fof(f12,axiom,(
% 1.89/0.64    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 1.89/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 1.89/0.64  fof(f1471,plain,(
% 1.89/0.64    spl4_41 | ~spl4_7),
% 1.89/0.64    inference(avatar_split_clause,[],[f1466,f160,f1468])).
% 1.89/0.64  fof(f160,plain,(
% 1.89/0.64    spl4_7 <=> k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)),
% 1.89/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 1.89/0.64  fof(f1466,plain,(
% 1.89/0.64    sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl4_7),
% 1.89/0.64    inference(duplicate_literal_removal,[],[f1457])).
% 1.89/0.64  fof(f1457,plain,(
% 1.89/0.64    sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl4_7),
% 1.89/0.64    inference(resolution,[],[f1049,f181])).
% 1.89/0.64  fof(f181,plain,(
% 1.89/0.64    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1,X0),X0) | k4_xboole_0(X0,X1) = X0) )),
% 1.89/0.64    inference(factoring,[],[f74])).
% 1.89/0.64  fof(f74,plain,(
% 1.89/0.64    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,X1,X2),X2) | r2_hidden(sK2(X0,X1,X2),X0) | k4_xboole_0(X0,X1) = X2) )),
% 1.89/0.64    inference(cnf_transformation,[],[f48])).
% 1.89/0.64  fof(f48,plain,(
% 1.89/0.64    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.89/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f46,f47])).
% 1.89/0.64  fof(f47,plain,(
% 1.89/0.64    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 1.89/0.64    introduced(choice_axiom,[])).
% 1.89/0.64  fof(f46,plain,(
% 1.89/0.64    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.89/0.64    inference(rectify,[],[f45])).
% 1.89/0.64  fof(f45,plain,(
% 1.89/0.64    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.89/0.64    inference(flattening,[],[f44])).
% 1.89/0.64  fof(f44,plain,(
% 1.89/0.64    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.89/0.64    inference(nnf_transformation,[],[f2])).
% 1.89/0.64  fof(f2,axiom,(
% 1.89/0.64    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.89/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.89/0.64  fof(f1049,plain,(
% 1.89/0.64    ( ! [X1] : (~r2_hidden(sK2(X1,k2_tops_1(sK0,sK1),X1),sK1) | k4_xboole_0(X1,k2_tops_1(sK0,sK1)) = X1) ) | ~spl4_7),
% 1.89/0.64    inference(resolution,[],[f1029,f285])).
% 1.89/0.64  fof(f285,plain,(
% 1.89/0.64    ( ! [X2,X1] : (r2_hidden(sK2(X1,X2,X1),X2) | k4_xboole_0(X1,X2) = X1) )),
% 1.89/0.64    inference(subsumption_resolution,[],[f283,f74])).
% 1.89/0.64  fof(f283,plain,(
% 1.89/0.64    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = X1 | r2_hidden(sK2(X1,X2,X1),X2) | ~r2_hidden(sK2(X1,X2,X1),X1)) )),
% 1.89/0.64    inference(duplicate_literal_removal,[],[f277])).
% 1.89/0.64  fof(f277,plain,(
% 1.89/0.64    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = X1 | r2_hidden(sK2(X1,X2,X1),X2) | ~r2_hidden(sK2(X1,X2,X1),X1) | k4_xboole_0(X1,X2) = X1) )),
% 1.89/0.64    inference(resolution,[],[f181,f76])).
% 1.89/0.64  fof(f76,plain,(
% 1.89/0.64    ( ! [X2,X0,X1] : (~r2_hidden(sK2(X0,X1,X2),X2) | r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | k4_xboole_0(X0,X1) = X2) )),
% 1.89/0.64    inference(cnf_transformation,[],[f48])).
% 1.89/0.64  fof(f1029,plain,(
% 1.89/0.64    ( ! [X1] : (~r2_hidden(X1,k2_tops_1(sK0,sK1)) | ~r2_hidden(X1,sK1)) ) | ~spl4_7),
% 1.89/0.64    inference(superposition,[],[f93,f162])).
% 1.89/0.64  fof(f162,plain,(
% 1.89/0.64    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~spl4_7),
% 1.89/0.64    inference(avatar_component_clause,[],[f160])).
% 1.89/0.64  fof(f93,plain,(
% 1.89/0.64    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 1.89/0.64    inference(equality_resolution,[],[f72])).
% 1.89/0.64  fof(f72,plain,(
% 1.89/0.64    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.89/0.64    inference(cnf_transformation,[],[f48])).
% 1.89/0.64  fof(f1149,plain,(
% 1.89/0.64    spl4_7 | ~spl4_2 | ~spl4_6),
% 1.89/0.64    inference(avatar_split_clause,[],[f1148,f156,f103,f160])).
% 1.89/0.64  fof(f103,plain,(
% 1.89/0.64    spl4_2 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)),
% 1.89/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.89/0.64  fof(f156,plain,(
% 1.89/0.64    spl4_6 <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.89/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.89/0.64  fof(f1148,plain,(
% 1.89/0.64    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | (~spl4_2 | ~spl4_6)),
% 1.89/0.64    inference(subsumption_resolution,[],[f1145,f157])).
% 1.89/0.64  fof(f157,plain,(
% 1.89/0.64    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_6),
% 1.89/0.64    inference(avatar_component_clause,[],[f156])).
% 1.89/0.64  fof(f1145,plain,(
% 1.89/0.64    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_2),
% 1.89/0.64    inference(superposition,[],[f59,f104])).
% 1.89/0.64  fof(f104,plain,(
% 1.89/0.64    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~spl4_2),
% 1.89/0.64    inference(avatar_component_clause,[],[f103])).
% 1.89/0.64  fof(f1020,plain,(
% 1.89/0.64    ~spl4_19 | spl4_25 | ~spl4_24),
% 1.89/0.64    inference(avatar_split_clause,[],[f991,f883,f887,f707])).
% 1.89/0.64  fof(f707,plain,(
% 1.89/0.64    spl4_19 <=> r1_tarski(sK1,k1_tops_1(sK0,sK1))),
% 1.89/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 1.89/0.64  fof(f883,plain,(
% 1.89/0.64    spl4_24 <=> r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 1.89/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 1.89/0.64  fof(f991,plain,(
% 1.89/0.64    sK1 = k1_tops_1(sK0,sK1) | ~r1_tarski(sK1,k1_tops_1(sK0,sK1)) | ~spl4_24),
% 1.89/0.64    inference(resolution,[],[f884,f62])).
% 1.89/0.64  fof(f62,plain,(
% 1.89/0.64    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.89/0.64    inference(cnf_transformation,[],[f43])).
% 1.89/0.64  fof(f43,plain,(
% 1.89/0.64    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.89/0.64    inference(flattening,[],[f42])).
% 1.89/0.64  fof(f42,plain,(
% 1.89/0.64    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.89/0.64    inference(nnf_transformation,[],[f4])).
% 1.89/0.64  fof(f4,axiom,(
% 1.89/0.64    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.89/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.89/0.64  fof(f884,plain,(
% 1.89/0.64    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~spl4_24),
% 1.89/0.64    inference(avatar_component_clause,[],[f883])).
% 1.89/0.64  fof(f1015,plain,(
% 1.89/0.64    ~spl4_3 | ~spl4_4 | spl4_7 | ~spl4_25),
% 1.89/0.64    inference(avatar_contradiction_clause,[],[f1014])).
% 1.89/0.64  fof(f1014,plain,(
% 1.89/0.64    $false | (~spl4_3 | ~spl4_4 | spl4_7 | ~spl4_25)),
% 1.89/0.64    inference(subsumption_resolution,[],[f1013,f116])).
% 1.89/0.64  fof(f1013,plain,(
% 1.89/0.64    ~l1_pre_topc(sK0) | (~spl4_3 | spl4_7 | ~spl4_25)),
% 1.89/0.64    inference(subsumption_resolution,[],[f1012,f111])).
% 1.89/0.64  fof(f1012,plain,(
% 1.89/0.64    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (spl4_7 | ~spl4_25)),
% 1.89/0.64    inference(subsumption_resolution,[],[f1010,f161])).
% 1.89/0.64  fof(f161,plain,(
% 1.89/0.64    k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | spl4_7),
% 1.89/0.64    inference(avatar_component_clause,[],[f160])).
% 1.89/0.64  fof(f1010,plain,(
% 1.89/0.64    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl4_25),
% 1.89/0.64    inference(superposition,[],[f569,f889])).
% 1.89/0.64  fof(f889,plain,(
% 1.89/0.64    sK1 = k1_tops_1(sK0,sK1) | ~spl4_25),
% 1.89/0.64    inference(avatar_component_clause,[],[f887])).
% 1.89/0.64  fof(f569,plain,(
% 1.89/0.64    ( ! [X2,X3] : (k2_tops_1(X2,X3) = k4_xboole_0(k2_pre_topc(X2,X3),k1_tops_1(X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2)) )),
% 1.89/0.64    inference(subsumption_resolution,[],[f217,f214])).
% 1.89/0.64  fof(f214,plain,(
% 1.89/0.64    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.89/0.64    inference(subsumption_resolution,[],[f213,f67])).
% 1.89/0.64  fof(f67,plain,(
% 1.89/0.64    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.89/0.64    inference(cnf_transformation,[],[f30])).
% 1.89/0.64  fof(f30,plain,(
% 1.89/0.64    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 1.89/0.64    inference(flattening,[],[f29])).
% 1.89/0.64  fof(f29,plain,(
% 1.89/0.64    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 1.89/0.64    inference(ennf_transformation,[],[f14])).
% 1.89/0.64  fof(f14,axiom,(
% 1.89/0.64    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 1.89/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 1.89/0.64  fof(f213,plain,(
% 1.89/0.64    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.89/0.64    inference(duplicate_literal_removal,[],[f212])).
% 1.89/0.64  fof(f212,plain,(
% 1.89/0.64    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.89/0.64    inference(superposition,[],[f70,f66])).
% 1.89/0.64  fof(f66,plain,(
% 1.89/0.64    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.89/0.64    inference(cnf_transformation,[],[f28])).
% 1.89/0.64  fof(f28,plain,(
% 1.89/0.64    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.89/0.64    inference(ennf_transformation,[],[f18])).
% 1.89/0.64  fof(f18,axiom,(
% 1.89/0.64    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 1.89/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).
% 1.89/0.64  fof(f70,plain,(
% 1.89/0.64    ( ! [X2,X0,X1] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.89/0.64    inference(cnf_transformation,[],[f36])).
% 1.89/0.64  fof(f36,plain,(
% 1.89/0.64    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.89/0.64    inference(flattening,[],[f35])).
% 1.89/0.64  fof(f35,plain,(
% 1.89/0.64    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 1.89/0.64    inference(ennf_transformation,[],[f11])).
% 1.89/0.64  fof(f11,axiom,(
% 1.89/0.64    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 1.89/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).
% 1.89/0.64  fof(f217,plain,(
% 1.89/0.64    ( ! [X2,X3] : (k2_tops_1(X2,X3) = k4_xboole_0(k2_pre_topc(X2,X3),k1_tops_1(X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2) | ~m1_subset_1(k2_pre_topc(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))) )),
% 1.89/0.64    inference(superposition,[],[f64,f59])).
% 1.89/0.64  fof(f64,plain,(
% 1.89/0.64    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.89/0.64    inference(cnf_transformation,[],[f26])).
% 1.89/0.64  fof(f26,plain,(
% 1.89/0.64    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.89/0.64    inference(ennf_transformation,[],[f16])).
% 1.89/0.64  fof(f16,axiom,(
% 1.89/0.64    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 1.89/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).
% 1.89/0.64  fof(f984,plain,(
% 1.89/0.64    spl4_24 | ~spl4_3 | ~spl4_4),
% 1.89/0.64    inference(avatar_split_clause,[],[f983,f114,f109,f883])).
% 1.89/0.64  fof(f983,plain,(
% 1.89/0.64    r1_tarski(k1_tops_1(sK0,sK1),sK1) | (~spl4_3 | ~spl4_4)),
% 1.89/0.64    inference(subsumption_resolution,[],[f971,f116])).
% 1.89/0.64  fof(f971,plain,(
% 1.89/0.64    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~l1_pre_topc(sK0) | ~spl4_3),
% 1.89/0.64    inference(resolution,[],[f369,f111])).
% 1.89/0.64  fof(f369,plain,(
% 1.89/0.64    ( ! [X12,X11] : (~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X12))) | r1_tarski(k1_tops_1(X12,X11),X11) | ~l1_pre_topc(X12)) )),
% 1.89/0.64    inference(superposition,[],[f78,f210])).
% 1.89/0.64  fof(f78,plain,(
% 1.89/0.64    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.89/0.64    inference(cnf_transformation,[],[f8])).
% 1.89/0.64  fof(f8,axiom,(
% 1.89/0.64    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.89/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.89/0.64  fof(f893,plain,(
% 1.89/0.64    ~spl4_7 | spl4_2 | ~spl4_6),
% 1.89/0.64    inference(avatar_split_clause,[],[f892,f156,f103,f160])).
% 1.89/0.64  fof(f892,plain,(
% 1.89/0.64    k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | (spl4_2 | ~spl4_6)),
% 1.89/0.64    inference(subsumption_resolution,[],[f891,f157])).
% 1.89/0.64  fof(f891,plain,(
% 1.89/0.64    k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl4_2),
% 1.89/0.64    inference(superposition,[],[f105,f59])).
% 1.89/0.64  fof(f105,plain,(
% 1.89/0.64    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | spl4_2),
% 1.89/0.64    inference(avatar_component_clause,[],[f103])).
% 1.89/0.64  fof(f710,plain,(
% 1.89/0.64    spl4_19 | ~spl4_1 | ~spl4_3 | ~spl4_4),
% 1.89/0.64    inference(avatar_split_clause,[],[f705,f114,f109,f99,f707])).
% 1.89/0.64  fof(f99,plain,(
% 1.89/0.64    spl4_1 <=> v3_pre_topc(sK1,sK0)),
% 1.89/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.89/0.64  fof(f705,plain,(
% 1.89/0.64    ~v3_pre_topc(sK1,sK0) | r1_tarski(sK1,k1_tops_1(sK0,sK1)) | (~spl4_3 | ~spl4_4)),
% 1.89/0.64    inference(subsumption_resolution,[],[f232,f90])).
% 1.89/0.64  fof(f90,plain,(
% 1.89/0.64    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.89/0.64    inference(equality_resolution,[],[f61])).
% 1.89/0.64  fof(f61,plain,(
% 1.89/0.64    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.89/0.64    inference(cnf_transformation,[],[f43])).
% 1.89/0.64  fof(f232,plain,(
% 1.89/0.64    ~v3_pre_topc(sK1,sK0) | r1_tarski(sK1,k1_tops_1(sK0,sK1)) | ~r1_tarski(sK1,sK1) | (~spl4_3 | ~spl4_4)),
% 1.89/0.64    inference(resolution,[],[f227,f111])).
% 1.89/0.64  fof(f227,plain,(
% 1.89/0.64    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X0,sK0) | r1_tarski(X0,k1_tops_1(sK0,sK1)) | ~r1_tarski(X0,sK1)) ) | (~spl4_3 | ~spl4_4)),
% 1.89/0.64    inference(subsumption_resolution,[],[f223,f116])).
% 1.89/0.64  fof(f223,plain,(
% 1.89/0.64    ( ! [X0] : (~r1_tarski(X0,sK1) | ~v3_pre_topc(X0,sK0) | r1_tarski(X0,k1_tops_1(sK0,sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) ) | ~spl4_3),
% 1.89/0.64    inference(resolution,[],[f69,f111])).
% 1.89/0.64  fof(f69,plain,(
% 1.89/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | r1_tarski(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.89/0.64    inference(cnf_transformation,[],[f34])).
% 1.89/0.64  fof(f34,plain,(
% 1.89/0.64    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.89/0.64    inference(flattening,[],[f33])).
% 1.89/0.64  fof(f33,plain,(
% 1.89/0.64    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(X1,k1_tops_1(X0,X2)) | (~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.89/0.64    inference(ennf_transformation,[],[f17])).
% 1.89/0.64  fof(f17,axiom,(
% 1.89/0.64    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v3_pre_topc(X1,X0)) => r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 1.89/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_1)).
% 1.89/0.64  fof(f319,plain,(
% 1.89/0.64    ~spl4_3 | ~spl4_4 | spl4_6),
% 1.89/0.64    inference(avatar_contradiction_clause,[],[f318])).
% 1.89/0.64  fof(f318,plain,(
% 1.89/0.64    $false | (~spl4_3 | ~spl4_4 | spl4_6)),
% 1.89/0.64    inference(subsumption_resolution,[],[f317,f116])).
% 1.89/0.64  fof(f317,plain,(
% 1.89/0.64    ~l1_pre_topc(sK0) | (~spl4_3 | spl4_6)),
% 1.89/0.64    inference(subsumption_resolution,[],[f310,f111])).
% 1.89/0.64  fof(f310,plain,(
% 1.89/0.64    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl4_6),
% 1.89/0.64    inference(resolution,[],[f214,f158])).
% 1.89/0.64  fof(f158,plain,(
% 1.89/0.64    ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl4_6),
% 1.89/0.64    inference(avatar_component_clause,[],[f156])).
% 1.89/0.64  fof(f174,plain,(
% 1.89/0.64    spl4_8 | ~spl4_3 | ~spl4_4 | ~spl4_5),
% 1.89/0.64    inference(avatar_split_clause,[],[f169,f119,f114,f109,f171])).
% 1.89/0.64  fof(f171,plain,(
% 1.89/0.64    spl4_8 <=> v3_pre_topc(k1_tops_1(sK0,sK1),sK0)),
% 1.89/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 1.89/0.64  fof(f119,plain,(
% 1.89/0.64    spl4_5 <=> v2_pre_topc(sK0)),
% 1.89/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.89/0.64  fof(f169,plain,(
% 1.89/0.64    v3_pre_topc(k1_tops_1(sK0,sK1),sK0) | (~spl4_3 | ~spl4_4 | ~spl4_5)),
% 1.89/0.64    inference(subsumption_resolution,[],[f168,f121])).
% 1.89/0.64  fof(f121,plain,(
% 1.89/0.64    v2_pre_topc(sK0) | ~spl4_5),
% 1.89/0.64    inference(avatar_component_clause,[],[f119])).
% 1.89/0.64  fof(f168,plain,(
% 1.89/0.64    v3_pre_topc(k1_tops_1(sK0,sK1),sK0) | ~v2_pre_topc(sK0) | (~spl4_3 | ~spl4_4)),
% 1.89/0.64    inference(subsumption_resolution,[],[f165,f116])).
% 1.89/0.64  fof(f165,plain,(
% 1.89/0.64    v3_pre_topc(k1_tops_1(sK0,sK1),sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~spl4_3),
% 1.89/0.64    inference(resolution,[],[f68,f111])).
% 1.89/0.64  fof(f68,plain,(
% 1.89/0.64    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(k1_tops_1(X0,X1),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.89/0.64    inference(cnf_transformation,[],[f32])).
% 1.89/0.64  fof(f32,plain,(
% 1.89/0.64    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.89/0.64    inference(flattening,[],[f31])).
% 1.89/0.64  fof(f31,plain,(
% 1.89/0.64    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.89/0.64    inference(ennf_transformation,[],[f15])).
% 1.89/0.64  fof(f15,axiom,(
% 1.89/0.64    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 1.89/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).
% 1.89/0.64  fof(f122,plain,(
% 1.89/0.64    spl4_5),
% 1.89/0.64    inference(avatar_split_clause,[],[f54,f119])).
% 1.89/0.64  fof(f54,plain,(
% 1.89/0.64    v2_pre_topc(sK0)),
% 1.89/0.64    inference(cnf_transformation,[],[f41])).
% 1.89/0.64  fof(f41,plain,(
% 1.89/0.64    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 1.89/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f38,f40,f39])).
% 1.89/0.64  fof(f39,plain,(
% 1.89/0.64    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | ~v3_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 1.89/0.64    introduced(choice_axiom,[])).
% 1.89/0.64  fof(f40,plain,(
% 1.89/0.64    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | ~v3_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.89/0.64    introduced(choice_axiom,[])).
% 1.89/0.64  fof(f38,plain,(
% 1.89/0.64    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.89/0.64    inference(flattening,[],[f37])).
% 1.89/0.64  fof(f37,plain,(
% 1.89/0.64    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.89/0.64    inference(nnf_transformation,[],[f24])).
% 1.89/0.64  fof(f24,plain,(
% 1.89/0.64    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.89/0.64    inference(flattening,[],[f23])).
% 1.89/0.64  fof(f23,plain,(
% 1.89/0.64    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 1.89/0.64    inference(ennf_transformation,[],[f21])).
% 1.89/0.64  fof(f21,negated_conjecture,(
% 1.89/0.64    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 1.89/0.64    inference(negated_conjecture,[],[f20])).
% 1.89/0.64  fof(f20,conjecture,(
% 1.89/0.64    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 1.89/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_1)).
% 1.89/0.64  fof(f117,plain,(
% 1.89/0.64    spl4_4),
% 1.89/0.64    inference(avatar_split_clause,[],[f55,f114])).
% 1.89/0.64  fof(f55,plain,(
% 1.89/0.64    l1_pre_topc(sK0)),
% 1.89/0.64    inference(cnf_transformation,[],[f41])).
% 1.89/0.64  fof(f112,plain,(
% 1.89/0.64    spl4_3),
% 1.89/0.64    inference(avatar_split_clause,[],[f56,f109])).
% 1.89/0.64  fof(f56,plain,(
% 1.89/0.64    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.89/0.64    inference(cnf_transformation,[],[f41])).
% 1.89/0.64  fof(f107,plain,(
% 1.89/0.64    spl4_1 | spl4_2),
% 1.89/0.64    inference(avatar_split_clause,[],[f57,f103,f99])).
% 1.89/0.64  fof(f57,plain,(
% 1.89/0.64    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)),
% 1.89/0.64    inference(cnf_transformation,[],[f41])).
% 1.89/0.64  fof(f106,plain,(
% 1.89/0.64    ~spl4_1 | ~spl4_2),
% 1.89/0.64    inference(avatar_split_clause,[],[f58,f103,f99])).
% 1.89/0.64  fof(f58,plain,(
% 1.89/0.64    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)),
% 1.89/0.64    inference(cnf_transformation,[],[f41])).
% 1.89/0.64  % SZS output end Proof for theBenchmark
% 1.89/0.64  % (21242)------------------------------
% 1.89/0.64  % (21242)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.89/0.64  % (21242)Termination reason: Refutation
% 1.89/0.64  
% 1.89/0.64  % (21242)Memory used [KB]: 7164
% 1.89/0.64  % (21242)Time elapsed: 0.217 s
% 1.89/0.64  % (21242)------------------------------
% 1.89/0.64  % (21242)------------------------------
% 1.89/0.64  % (21220)Success in time 0.271 s
%------------------------------------------------------------------------------
