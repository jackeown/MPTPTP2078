%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:12:32 EST 2020

% Result     : Theorem 1.36s
% Output     : Refutation 1.36s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 306 expanded)
%              Number of leaves         :   34 ( 131 expanded)
%              Depth                    :   13
%              Number of atoms          :  564 (1762 expanded)
%              Number of equality atoms :   50 ( 217 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f674,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f83,f88,f93,f98,f102,f107,f112,f117,f158,f170,f186,f259,f277,f285,f288,f502,f519,f524,f673])).

fof(f673,plain,
    ( ~ spl5_43
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_12
    | spl5_42 ),
    inference(avatar_split_clause,[],[f669,f516,f160,f114,f109,f104,f95,f90,f85,f521])).

fof(f521,plain,
    ( spl5_43
  <=> r2_hidden(sK4(sK2,k1_xboole_0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_43])])).

fof(f85,plain,
    ( spl5_3
  <=> v3_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f90,plain,
    ( spl5_4
  <=> r1_tarski(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f95,plain,
    ( spl5_5
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f104,plain,
    ( spl5_7
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f109,plain,
    ( spl5_8
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f114,plain,
    ( spl5_9
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f160,plain,
    ( spl5_12
  <=> k1_xboole_0 = k1_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f516,plain,
    ( spl5_42
  <=> r2_hidden(sK4(sK2,k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_42])])).

fof(f669,plain,
    ( ~ r2_hidden(sK4(sK2,k1_xboole_0),sK2)
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_12
    | spl5_42 ),
    inference(unit_resulting_resolution,[],[f92,f87,f97,f518,f543])).

fof(f543,plain,
    ( ! [X4,X5] :
        ( ~ r2_hidden(X4,X5)
        | r2_hidden(X4,k1_xboole_0)
        | ~ r1_tarski(X5,sK1)
        | ~ v3_pre_topc(X5,sK0)
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_12 ),
    inference(forward_demodulation,[],[f175,f161])).

fof(f161,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f160])).

fof(f175,plain,
    ( ! [X4,X5] :
        ( r2_hidden(X4,k1_tops_1(sK0,sK1))
        | ~ r2_hidden(X4,X5)
        | ~ r1_tarski(X5,sK1)
        | ~ v3_pre_topc(X5,sK0)
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_9 ),
    inference(subsumption_resolution,[],[f174,f116])).

fof(f116,plain,
    ( v2_pre_topc(sK0)
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f114])).

fof(f174,plain,
    ( ! [X4,X5] :
        ( r2_hidden(X4,k1_tops_1(sK0,sK1))
        | ~ r2_hidden(X4,X5)
        | ~ r1_tarski(X5,sK1)
        | ~ v3_pre_topc(X5,sK0)
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_pre_topc(sK0) )
    | ~ spl5_7
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f145,f111])).

fof(f111,plain,
    ( l1_pre_topc(sK0)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f109])).

fof(f145,plain,
    ( ! [X4,X5] :
        ( r2_hidden(X4,k1_tops_1(sK0,sK1))
        | ~ r2_hidden(X4,X5)
        | ~ r1_tarski(X5,sK1)
        | ~ v3_pre_topc(X5,sK0)
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl5_7 ),
    inference(resolution,[],[f106,f61])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ r2_hidden(X1,X3)
      | ~ r1_tarski(X3,X2)
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_hidden(X1,k1_tops_1(X0,X2))
              | ! [X3] :
                  ( ~ r2_hidden(X1,X3)
                  | ~ r1_tarski(X3,X2)
                  | ~ v3_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ( r2_hidden(X1,sK3(X0,X1,X2))
                & r1_tarski(sK3(X0,X1,X2),X2)
                & v3_pre_topc(sK3(X0,X1,X2),X0)
                & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X1,k1_tops_1(X0,X2)) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f37,f38])).

fof(f38,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X1,X4)
          & r1_tarski(X4,X2)
          & v3_pre_topc(X4,X0)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( r2_hidden(X1,sK3(X0,X1,X2))
        & r1_tarski(sK3(X0,X1,X2),X2)
        & v3_pre_topc(sK3(X0,X1,X2),X0)
        & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_hidden(X1,k1_tops_1(X0,X2))
              | ! [X3] :
                  ( ~ r2_hidden(X1,X3)
                  | ~ r1_tarski(X3,X2)
                  | ~ v3_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ? [X4] :
                  ( r2_hidden(X1,X4)
                  & r1_tarski(X4,X2)
                  & v3_pre_topc(X4,X0)
                  & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X1,k1_tops_1(X0,X2)) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_hidden(X1,k1_tops_1(X0,X2))
              | ! [X3] :
                  ( ~ r2_hidden(X1,X3)
                  | ~ r1_tarski(X3,X2)
                  | ~ v3_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ? [X3] :
                  ( r2_hidden(X1,X3)
                  & r1_tarski(X3,X2)
                  & v3_pre_topc(X3,X0)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X1,k1_tops_1(X0,X2)) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_hidden(X1,k1_tops_1(X0,X2))
          <=> ? [X3] :
                ( r2_hidden(X1,X3)
                & r1_tarski(X3,X2)
                & v3_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_hidden(X1,k1_tops_1(X0,X2))
          <=> ? [X3] :
                ( r2_hidden(X1,X3)
                & r1_tarski(X3,X2)
                & v3_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1,X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
         => ( r2_hidden(X1,k1_tops_1(X0,X2))
          <=> ? [X3] :
                ( r2_hidden(X1,X3)
                & r1_tarski(X3,X2)
                & v3_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_tops_1)).

fof(f106,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f104])).

fof(f518,plain,
    ( ~ r2_hidden(sK4(sK2,k1_xboole_0),k1_xboole_0)
    | spl5_42 ),
    inference(avatar_component_clause,[],[f516])).

fof(f97,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f95])).

fof(f87,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f85])).

fof(f92,plain,
    ( r1_tarski(sK2,sK1)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f90])).

fof(f524,plain,
    ( spl5_43
    | spl5_41 ),
    inference(avatar_split_clause,[],[f508,f499,f521])).

fof(f499,plain,
    ( spl5_41
  <=> r1_tarski(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_41])])).

fof(f508,plain,
    ( r2_hidden(sK4(sK2,k1_xboole_0),sK2)
    | spl5_41 ),
    inference(unit_resulting_resolution,[],[f501,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK4(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f41,f42])).

fof(f42,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f501,plain,
    ( ~ r1_tarski(sK2,k1_xboole_0)
    | spl5_41 ),
    inference(avatar_component_clause,[],[f499])).

fof(f519,plain,
    ( ~ spl5_42
    | spl5_41 ),
    inference(avatar_split_clause,[],[f509,f499,f516])).

fof(f509,plain,
    ( ~ r2_hidden(sK4(sK2,k1_xboole_0),k1_xboole_0)
    | spl5_41 ),
    inference(unit_resulting_resolution,[],[f501,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK4(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f502,plain,
    ( ~ spl5_41
    | spl5_2 ),
    inference(avatar_split_clause,[],[f490,f80,f499])).

fof(f80,plain,
    ( spl5_2
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f490,plain,
    ( ~ r1_tarski(sK2,k1_xboole_0)
    | spl5_2 ),
    inference(unit_resulting_resolution,[],[f53,f289,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f289,plain,
    ( ! [X0] : ~ r1_tarski(sK2,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,sK2))))
    | spl5_2 ),
    inference(unit_resulting_resolution,[],[f82,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))) ) ),
    inference(definition_unfolding,[],[f64,f73])).

fof(f73,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f63,f62])).

fof(f62,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f63,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f64,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k4_xboole_0(X1,X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k4_xboole_0(X1,X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X0))
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).

fof(f82,plain,
    ( k1_xboole_0 != sK2
    | spl5_2 ),
    inference(avatar_component_clause,[],[f80])).

fof(f53,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f288,plain,
    ( spl5_12
    | ~ spl5_1
    | ~ spl5_7
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f286,f109,f104,f76,f160])).

fof(f76,plain,
    ( spl5_1
  <=> v2_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f286,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ spl5_1
    | ~ spl5_7
    | ~ spl5_8 ),
    inference(unit_resulting_resolution,[],[f111,f106,f77,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_tops_1(X0,X1)
      | ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | k1_xboole_0 != k1_tops_1(X0,X1) )
            & ( k1_xboole_0 = k1_tops_1(X0,X1)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).

fof(f77,plain,
    ( v2_tops_1(sK1,sK0)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f76])).

fof(f285,plain,
    ( ~ spl5_12
    | spl5_1
    | ~ spl5_7
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f284,f109,f104,f76,f160])).

fof(f284,plain,
    ( v2_tops_1(sK1,sK0)
    | k1_xboole_0 != k1_tops_1(sK0,sK1)
    | ~ spl5_7
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f140,f111])).

fof(f140,plain,
    ( v2_tops_1(sK1,sK0)
    | k1_xboole_0 != k1_tops_1(sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl5_7 ),
    inference(resolution,[],[f106,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v2_tops_1(X1,X0)
      | k1_xboole_0 != k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f277,plain,
    ( ~ spl5_23
    | ~ spl5_6
    | ~ spl5_11
    | spl5_12
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f268,f165,f160,f155,f100,f256])).

fof(f256,plain,
    ( spl5_23
  <=> r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f100,plain,
    ( spl5_6
  <=> ! [X3] :
        ( k1_xboole_0 = X3
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X3,sK1)
        | ~ v3_pre_topc(X3,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f155,plain,
    ( spl5_11
  <=> v3_pre_topc(k1_tops_1(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f165,plain,
    ( spl5_13
  <=> r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f268,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))
    | ~ spl5_6
    | ~ spl5_11
    | spl5_12
    | ~ spl5_13 ),
    inference(unit_resulting_resolution,[],[f162,f157,f167,f188])).

fof(f188,plain,
    ( ! [X2] :
        ( ~ r1_tarski(X2,u1_struct_0(sK0))
        | ~ r1_tarski(X2,sK1)
        | ~ v3_pre_topc(X2,sK0)
        | k1_xboole_0 = X2 )
    | ~ spl5_6 ),
    inference(resolution,[],[f101,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f101,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X3
        | ~ r1_tarski(X3,sK1)
        | ~ v3_pre_topc(X3,sK0) )
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f100])).

fof(f167,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f165])).

fof(f157,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f155])).

fof(f162,plain,
    ( k1_xboole_0 != k1_tops_1(sK0,sK1)
    | spl5_12 ),
    inference(avatar_component_clause,[],[f160])).

fof(f259,plain,
    ( spl5_23
    | ~ spl5_10
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f228,f165,f150,f256])).

fof(f150,plain,
    ( spl5_10
  <=> r1_tarski(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f228,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))
    | ~ spl5_10
    | ~ spl5_13 ),
    inference(unit_resulting_resolution,[],[f152,f167,f72])).

fof(f152,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f150])).

fof(f186,plain,
    ( spl5_10
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f148,f104,f150])).

fof(f148,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl5_7 ),
    inference(resolution,[],[f106,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f170,plain,
    ( spl5_13
    | ~ spl5_7
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f169,f109,f104,f165])).

fof(f169,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl5_7
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f138,f111])).

fof(f138,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl5_7 ),
    inference(resolution,[],[f106,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

fof(f158,plain,
    ( spl5_11
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f136,f114,f109,f104,f155])).

fof(f136,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_9 ),
    inference(unit_resulting_resolution,[],[f116,f111,f106,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

fof(f117,plain,(
    spl5_9 ),
    inference(avatar_split_clause,[],[f45,f114])).

fof(f45,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,
    ( ( ( k1_xboole_0 != sK2
        & v3_pre_topc(sK2,sK0)
        & r1_tarski(sK2,sK1)
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) )
      | ~ v2_tops_1(sK1,sK0) )
    & ( ! [X3] :
          ( k1_xboole_0 = X3
          | ~ v3_pre_topc(X3,sK0)
          | ~ r1_tarski(X3,sK1)
          | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
      | v2_tops_1(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f30,f33,f32,f31])).

fof(f31,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ? [X2] :
                  ( k1_xboole_0 != X2
                  & v3_pre_topc(X2,X0)
                  & r1_tarski(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tops_1(X1,X0) )
            & ( ! [X3] :
                  ( k1_xboole_0 = X3
                  | ~ v3_pre_topc(X3,X0)
                  | ~ r1_tarski(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | v2_tops_1(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ? [X2] :
                ( k1_xboole_0 != X2
                & v3_pre_topc(X2,sK0)
                & r1_tarski(X2,X1)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
            | ~ v2_tops_1(X1,sK0) )
          & ( ! [X3] :
                ( k1_xboole_0 = X3
                | ~ v3_pre_topc(X3,sK0)
                | ~ r1_tarski(X3,X1)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
            | v2_tops_1(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X1] :
        ( ( ? [X2] :
              ( k1_xboole_0 != X2
              & v3_pre_topc(X2,sK0)
              & r1_tarski(X2,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          | ~ v2_tops_1(X1,sK0) )
        & ( ! [X3] :
              ( k1_xboole_0 = X3
              | ~ v3_pre_topc(X3,sK0)
              | ~ r1_tarski(X3,X1)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
          | v2_tops_1(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( ? [X2] :
            ( k1_xboole_0 != X2
            & v3_pre_topc(X2,sK0)
            & r1_tarski(X2,sK1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        | ~ v2_tops_1(sK1,sK0) )
      & ( ! [X3] :
            ( k1_xboole_0 = X3
            | ~ v3_pre_topc(X3,sK0)
            | ~ r1_tarski(X3,sK1)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
        | v2_tops_1(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X2] :
        ( k1_xboole_0 != X2
        & v3_pre_topc(X2,sK0)
        & r1_tarski(X2,sK1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( k1_xboole_0 != sK2
      & v3_pre_topc(sK2,sK0)
      & r1_tarski(sK2,sK1)
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( k1_xboole_0 != X2
                & v3_pre_topc(X2,X0)
                & r1_tarski(X2,X1)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ v2_tops_1(X1,X0) )
          & ( ! [X3] :
                ( k1_xboole_0 = X3
                | ~ v3_pre_topc(X3,X0)
                | ~ r1_tarski(X3,X1)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( k1_xboole_0 != X2
                & v3_pre_topc(X2,X0)
                & r1_tarski(X2,X1)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ v2_tops_1(X1,X0) )
          & ( ! [X2] :
                ( k1_xboole_0 = X2
                | ~ v3_pre_topc(X2,X0)
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( k1_xboole_0 != X2
                & v3_pre_topc(X2,X0)
                & r1_tarski(X2,X1)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ v2_tops_1(X1,X0) )
          & ( ! [X2] :
                ( k1_xboole_0 = X2
                | ~ v3_pre_topc(X2,X0)
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tops_1(X1,X0)
          <~> ! [X2] :
                ( k1_xboole_0 = X2
                | ~ v3_pre_topc(X2,X0)
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tops_1(X1,X0)
          <~> ! [X2] :
                ( k1_xboole_0 = X2
                | ~ v3_pre_topc(X2,X0)
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
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
           => ( v2_tops_1(X1,X0)
            <=> ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( v3_pre_topc(X2,X0)
                      & r1_tarski(X2,X1) )
                   => k1_xboole_0 = X2 ) ) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v3_pre_topc(X2,X0)
                    & r1_tarski(X2,X1) )
                 => k1_xboole_0 = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_tops_1)).

fof(f112,plain,(
    spl5_8 ),
    inference(avatar_split_clause,[],[f46,f109])).

fof(f46,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f107,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f47,f104])).

fof(f47,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f34])).

fof(f102,plain,
    ( spl5_1
    | spl5_6 ),
    inference(avatar_split_clause,[],[f48,f100,f76])).

fof(f48,plain,(
    ! [X3] :
      ( k1_xboole_0 = X3
      | ~ v3_pre_topc(X3,sK0)
      | ~ r1_tarski(X3,sK1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_tops_1(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f98,plain,
    ( ~ spl5_1
    | spl5_5 ),
    inference(avatar_split_clause,[],[f49,f95,f76])).

fof(f49,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f93,plain,
    ( ~ spl5_1
    | spl5_4 ),
    inference(avatar_split_clause,[],[f50,f90,f76])).

fof(f50,plain,
    ( r1_tarski(sK2,sK1)
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f88,plain,
    ( ~ spl5_1
    | spl5_3 ),
    inference(avatar_split_clause,[],[f51,f85,f76])).

fof(f51,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f83,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f52,f80,f76])).

fof(f52,plain,
    ( k1_xboole_0 != sK2
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:09:56 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.46  % (3062)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.47  % (3067)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.49  % (3074)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.49  % (3078)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.49  % (3082)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.50  % (3070)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.21/0.51  % (3069)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.21/0.52  % (3057)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.21/0.52  % (3079)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.21/0.52  % (3081)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.36/0.53  % (3073)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.36/0.53  % (3058)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.36/0.53  % (3059)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.36/0.53  % (3060)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.36/0.53  % (3071)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.36/0.54  % (3086)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.36/0.54  % (3061)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.36/0.54  % (3082)Refutation found. Thanks to Tanya!
% 1.36/0.54  % SZS status Theorem for theBenchmark
% 1.36/0.54  % SZS output start Proof for theBenchmark
% 1.36/0.54  fof(f674,plain,(
% 1.36/0.54    $false),
% 1.36/0.54    inference(avatar_sat_refutation,[],[f83,f88,f93,f98,f102,f107,f112,f117,f158,f170,f186,f259,f277,f285,f288,f502,f519,f524,f673])).
% 1.36/0.54  fof(f673,plain,(
% 1.36/0.54    ~spl5_43 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_7 | ~spl5_8 | ~spl5_9 | ~spl5_12 | spl5_42),
% 1.36/0.54    inference(avatar_split_clause,[],[f669,f516,f160,f114,f109,f104,f95,f90,f85,f521])).
% 1.36/0.54  fof(f521,plain,(
% 1.36/0.54    spl5_43 <=> r2_hidden(sK4(sK2,k1_xboole_0),sK2)),
% 1.36/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_43])])).
% 1.36/0.54  fof(f85,plain,(
% 1.36/0.54    spl5_3 <=> v3_pre_topc(sK2,sK0)),
% 1.36/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.36/0.54  fof(f90,plain,(
% 1.36/0.54    spl5_4 <=> r1_tarski(sK2,sK1)),
% 1.36/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.36/0.54  fof(f95,plain,(
% 1.36/0.54    spl5_5 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.36/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 1.36/0.54  fof(f104,plain,(
% 1.36/0.54    spl5_7 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.36/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 1.36/0.54  fof(f109,plain,(
% 1.36/0.54    spl5_8 <=> l1_pre_topc(sK0)),
% 1.36/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 1.36/0.54  fof(f114,plain,(
% 1.36/0.54    spl5_9 <=> v2_pre_topc(sK0)),
% 1.36/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 1.36/0.54  fof(f160,plain,(
% 1.36/0.54    spl5_12 <=> k1_xboole_0 = k1_tops_1(sK0,sK1)),
% 1.36/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 1.36/0.54  fof(f516,plain,(
% 1.36/0.54    spl5_42 <=> r2_hidden(sK4(sK2,k1_xboole_0),k1_xboole_0)),
% 1.36/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_42])])).
% 1.36/0.54  fof(f669,plain,(
% 1.36/0.54    ~r2_hidden(sK4(sK2,k1_xboole_0),sK2) | (~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_7 | ~spl5_8 | ~spl5_9 | ~spl5_12 | spl5_42)),
% 1.36/0.54    inference(unit_resulting_resolution,[],[f92,f87,f97,f518,f543])).
% 1.36/0.54  fof(f543,plain,(
% 1.36/0.54    ( ! [X4,X5] : (~r2_hidden(X4,X5) | r2_hidden(X4,k1_xboole_0) | ~r1_tarski(X5,sK1) | ~v3_pre_topc(X5,sK0) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl5_7 | ~spl5_8 | ~spl5_9 | ~spl5_12)),
% 1.36/0.54    inference(forward_demodulation,[],[f175,f161])).
% 1.36/0.54  fof(f161,plain,(
% 1.36/0.54    k1_xboole_0 = k1_tops_1(sK0,sK1) | ~spl5_12),
% 1.36/0.54    inference(avatar_component_clause,[],[f160])).
% 1.36/0.54  fof(f175,plain,(
% 1.36/0.54    ( ! [X4,X5] : (r2_hidden(X4,k1_tops_1(sK0,sK1)) | ~r2_hidden(X4,X5) | ~r1_tarski(X5,sK1) | ~v3_pre_topc(X5,sK0) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl5_7 | ~spl5_8 | ~spl5_9)),
% 1.36/0.54    inference(subsumption_resolution,[],[f174,f116])).
% 1.36/0.54  fof(f116,plain,(
% 1.36/0.54    v2_pre_topc(sK0) | ~spl5_9),
% 1.36/0.54    inference(avatar_component_clause,[],[f114])).
% 1.36/0.54  fof(f174,plain,(
% 1.36/0.54    ( ! [X4,X5] : (r2_hidden(X4,k1_tops_1(sK0,sK1)) | ~r2_hidden(X4,X5) | ~r1_tarski(X5,sK1) | ~v3_pre_topc(X5,sK0) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0)) ) | (~spl5_7 | ~spl5_8)),
% 1.36/0.54    inference(subsumption_resolution,[],[f145,f111])).
% 1.36/0.54  fof(f111,plain,(
% 1.36/0.54    l1_pre_topc(sK0) | ~spl5_8),
% 1.36/0.54    inference(avatar_component_clause,[],[f109])).
% 1.36/0.54  fof(f145,plain,(
% 1.36/0.54    ( ! [X4,X5] : (r2_hidden(X4,k1_tops_1(sK0,sK1)) | ~r2_hidden(X4,X5) | ~r1_tarski(X5,sK1) | ~v3_pre_topc(X5,sK0) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) ) | ~spl5_7),
% 1.36/0.54    inference(resolution,[],[f106,f61])).
% 1.36/0.54  fof(f61,plain,(
% 1.36/0.54    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,k1_tops_1(X0,X2)) | ~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f39])).
% 1.36/0.54  fof(f39,plain,(
% 1.36/0.54    ! [X0] : (! [X1,X2] : (((r2_hidden(X1,k1_tops_1(X0,X2)) | ! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & ((r2_hidden(X1,sK3(X0,X1,X2)) & r1_tarski(sK3(X0,X1,X2),X2) & v3_pre_topc(sK3(X0,X1,X2),X0) & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X1,k1_tops_1(X0,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.36/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f37,f38])).
% 1.36/0.54  fof(f38,plain,(
% 1.36/0.54    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) => (r2_hidden(X1,sK3(X0,X1,X2)) & r1_tarski(sK3(X0,X1,X2),X2) & v3_pre_topc(sK3(X0,X1,X2),X0) & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.36/0.54    introduced(choice_axiom,[])).
% 1.36/0.54  fof(f37,plain,(
% 1.36/0.54    ! [X0] : (! [X1,X2] : (((r2_hidden(X1,k1_tops_1(X0,X2)) | ! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X1,k1_tops_1(X0,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.36/0.54    inference(rectify,[],[f36])).
% 1.36/0.54  fof(f36,plain,(
% 1.36/0.54    ! [X0] : (! [X1,X2] : (((r2_hidden(X1,k1_tops_1(X0,X2)) | ! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X1,k1_tops_1(X0,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.36/0.54    inference(nnf_transformation,[],[f20])).
% 1.36/0.54  fof(f20,plain,(
% 1.36/0.54    ! [X0] : (! [X1,X2] : ((r2_hidden(X1,k1_tops_1(X0,X2)) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.36/0.54    inference(flattening,[],[f19])).
% 1.36/0.54  fof(f19,plain,(
% 1.36/0.54    ! [X0] : (! [X1,X2] : ((r2_hidden(X1,k1_tops_1(X0,X2)) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.36/0.54    inference(ennf_transformation,[],[f11])).
% 1.36/0.54  fof(f11,axiom,(
% 1.36/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,k1_tops_1(X0,X2)) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))))),
% 1.36/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_tops_1)).
% 1.36/0.54  fof(f106,plain,(
% 1.36/0.54    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_7),
% 1.36/0.54    inference(avatar_component_clause,[],[f104])).
% 1.36/0.54  fof(f518,plain,(
% 1.36/0.54    ~r2_hidden(sK4(sK2,k1_xboole_0),k1_xboole_0) | spl5_42),
% 1.36/0.54    inference(avatar_component_clause,[],[f516])).
% 1.36/0.54  fof(f97,plain,(
% 1.36/0.54    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_5),
% 1.36/0.54    inference(avatar_component_clause,[],[f95])).
% 1.36/0.54  fof(f87,plain,(
% 1.36/0.54    v3_pre_topc(sK2,sK0) | ~spl5_3),
% 1.36/0.54    inference(avatar_component_clause,[],[f85])).
% 1.36/0.54  fof(f92,plain,(
% 1.36/0.54    r1_tarski(sK2,sK1) | ~spl5_4),
% 1.36/0.54    inference(avatar_component_clause,[],[f90])).
% 1.36/0.54  fof(f524,plain,(
% 1.36/0.54    spl5_43 | spl5_41),
% 1.36/0.54    inference(avatar_split_clause,[],[f508,f499,f521])).
% 1.36/0.54  fof(f499,plain,(
% 1.36/0.54    spl5_41 <=> r1_tarski(sK2,k1_xboole_0)),
% 1.36/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_41])])).
% 1.36/0.54  fof(f508,plain,(
% 1.36/0.54    r2_hidden(sK4(sK2,k1_xboole_0),sK2) | spl5_41),
% 1.36/0.54    inference(unit_resulting_resolution,[],[f501,f67])).
% 1.36/0.54  fof(f67,plain,(
% 1.36/0.54    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK4(X0,X1),X0)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f43])).
% 1.36/0.54  fof(f43,plain,(
% 1.36/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.36/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f41,f42])).
% 1.36/0.54  fof(f42,plain,(
% 1.36/0.54    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 1.36/0.54    introduced(choice_axiom,[])).
% 1.36/0.54  fof(f41,plain,(
% 1.36/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.36/0.54    inference(rectify,[],[f40])).
% 1.36/0.54  fof(f40,plain,(
% 1.36/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.36/0.54    inference(nnf_transformation,[],[f24])).
% 1.36/0.54  fof(f24,plain,(
% 1.36/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.36/0.54    inference(ennf_transformation,[],[f1])).
% 1.36/0.54  fof(f1,axiom,(
% 1.36/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.36/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.36/0.54  fof(f501,plain,(
% 1.36/0.54    ~r1_tarski(sK2,k1_xboole_0) | spl5_41),
% 1.36/0.54    inference(avatar_component_clause,[],[f499])).
% 1.36/0.54  fof(f519,plain,(
% 1.36/0.54    ~spl5_42 | spl5_41),
% 1.36/0.54    inference(avatar_split_clause,[],[f509,f499,f516])).
% 1.36/0.54  fof(f509,plain,(
% 1.36/0.54    ~r2_hidden(sK4(sK2,k1_xboole_0),k1_xboole_0) | spl5_41),
% 1.36/0.54    inference(unit_resulting_resolution,[],[f501,f68])).
% 1.36/0.54  fof(f68,plain,(
% 1.36/0.54    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK4(X0,X1),X1)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f43])).
% 1.36/0.54  fof(f502,plain,(
% 1.36/0.54    ~spl5_41 | spl5_2),
% 1.36/0.54    inference(avatar_split_clause,[],[f490,f80,f499])).
% 1.36/0.54  fof(f80,plain,(
% 1.36/0.54    spl5_2 <=> k1_xboole_0 = sK2),
% 1.36/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.36/0.54  fof(f490,plain,(
% 1.36/0.54    ~r1_tarski(sK2,k1_xboole_0) | spl5_2),
% 1.36/0.54    inference(unit_resulting_resolution,[],[f53,f289,f72])).
% 1.36/0.54  fof(f72,plain,(
% 1.36/0.54    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f27])).
% 1.36/0.54  fof(f27,plain,(
% 1.36/0.54    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 1.36/0.54    inference(flattening,[],[f26])).
% 1.36/0.54  fof(f26,plain,(
% 1.36/0.54    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.36/0.54    inference(ennf_transformation,[],[f3])).
% 1.36/0.54  fof(f3,axiom,(
% 1.36/0.54    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 1.36/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 1.36/0.54  fof(f289,plain,(
% 1.36/0.54    ( ! [X0] : (~r1_tarski(sK2,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,sK2))))) ) | spl5_2),
% 1.36/0.54    inference(unit_resulting_resolution,[],[f82,f74])).
% 1.36/0.54  fof(f74,plain,(
% 1.36/0.54    ( ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))))) )),
% 1.36/0.54    inference(definition_unfolding,[],[f64,f73])).
% 1.36/0.54  fof(f73,plain,(
% 1.36/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 1.36/0.54    inference(definition_unfolding,[],[f63,f62])).
% 1.36/0.54  fof(f62,plain,(
% 1.36/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.36/0.54    inference(cnf_transformation,[],[f6])).
% 1.36/0.54  fof(f6,axiom,(
% 1.36/0.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.36/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.36/0.54  fof(f63,plain,(
% 1.36/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.36/0.54    inference(cnf_transformation,[],[f2])).
% 1.36/0.54  fof(f2,axiom,(
% 1.36/0.54    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.36/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.36/0.54  fof(f64,plain,(
% 1.36/0.54    ( ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k4_xboole_0(X1,X0))) )),
% 1.36/0.54    inference(cnf_transformation,[],[f21])).
% 1.36/0.54  fof(f21,plain,(
% 1.36/0.54    ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k4_xboole_0(X1,X0)))),
% 1.36/0.54    inference(ennf_transformation,[],[f5])).
% 1.36/0.54  fof(f5,axiom,(
% 1.36/0.54    ! [X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X0)) => k1_xboole_0 = X0)),
% 1.36/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).
% 1.36/0.54  fof(f82,plain,(
% 1.36/0.54    k1_xboole_0 != sK2 | spl5_2),
% 1.36/0.54    inference(avatar_component_clause,[],[f80])).
% 1.36/0.54  fof(f53,plain,(
% 1.36/0.54    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f4])).
% 1.36/0.54  fof(f4,axiom,(
% 1.36/0.54    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.36/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.36/0.54  fof(f288,plain,(
% 1.36/0.54    spl5_12 | ~spl5_1 | ~spl5_7 | ~spl5_8),
% 1.36/0.54    inference(avatar_split_clause,[],[f286,f109,f104,f76,f160])).
% 1.36/0.54  fof(f76,plain,(
% 1.36/0.54    spl5_1 <=> v2_tops_1(sK1,sK0)),
% 1.36/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.36/0.54  fof(f286,plain,(
% 1.36/0.54    k1_xboole_0 = k1_tops_1(sK0,sK1) | (~spl5_1 | ~spl5_7 | ~spl5_8)),
% 1.36/0.54    inference(unit_resulting_resolution,[],[f111,f106,f77,f55])).
% 1.36/0.54  fof(f55,plain,(
% 1.36/0.54    ( ! [X0,X1] : (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f35])).
% 1.36/0.54  fof(f35,plain,(
% 1.36/0.54    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | k1_xboole_0 != k1_tops_1(X0,X1)) & (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.36/0.54    inference(nnf_transformation,[],[f18])).
% 1.36/0.54  fof(f18,plain,(
% 1.36/0.54    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.36/0.54    inference(ennf_transformation,[],[f12])).
% 1.36/0.54  fof(f12,axiom,(
% 1.36/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 1.36/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).
% 1.36/0.54  fof(f77,plain,(
% 1.36/0.54    v2_tops_1(sK1,sK0) | ~spl5_1),
% 1.36/0.54    inference(avatar_component_clause,[],[f76])).
% 1.36/0.54  fof(f285,plain,(
% 1.36/0.54    ~spl5_12 | spl5_1 | ~spl5_7 | ~spl5_8),
% 1.36/0.54    inference(avatar_split_clause,[],[f284,f109,f104,f76,f160])).
% 1.36/0.54  fof(f284,plain,(
% 1.36/0.54    v2_tops_1(sK1,sK0) | k1_xboole_0 != k1_tops_1(sK0,sK1) | (~spl5_7 | ~spl5_8)),
% 1.36/0.54    inference(subsumption_resolution,[],[f140,f111])).
% 1.36/0.54  fof(f140,plain,(
% 1.36/0.54    v2_tops_1(sK1,sK0) | k1_xboole_0 != k1_tops_1(sK0,sK1) | ~l1_pre_topc(sK0) | ~spl5_7),
% 1.36/0.54    inference(resolution,[],[f106,f56])).
% 1.36/0.54  fof(f56,plain,(
% 1.36/0.54    ( ! [X0,X1] : (v2_tops_1(X1,X0) | k1_xboole_0 != k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f35])).
% 1.36/0.54  fof(f277,plain,(
% 1.36/0.54    ~spl5_23 | ~spl5_6 | ~spl5_11 | spl5_12 | ~spl5_13),
% 1.36/0.54    inference(avatar_split_clause,[],[f268,f165,f160,f155,f100,f256])).
% 1.36/0.54  fof(f256,plain,(
% 1.36/0.54    spl5_23 <=> r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))),
% 1.36/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).
% 1.36/0.54  fof(f100,plain,(
% 1.36/0.54    spl5_6 <=> ! [X3] : (k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X3,sK1) | ~v3_pre_topc(X3,sK0))),
% 1.36/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 1.36/0.54  fof(f155,plain,(
% 1.36/0.54    spl5_11 <=> v3_pre_topc(k1_tops_1(sK0,sK1),sK0)),
% 1.36/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 1.36/0.54  fof(f165,plain,(
% 1.36/0.54    spl5_13 <=> r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 1.36/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 1.36/0.54  fof(f268,plain,(
% 1.36/0.54    ~r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) | (~spl5_6 | ~spl5_11 | spl5_12 | ~spl5_13)),
% 1.36/0.54    inference(unit_resulting_resolution,[],[f162,f157,f167,f188])).
% 1.36/0.54  fof(f188,plain,(
% 1.36/0.54    ( ! [X2] : (~r1_tarski(X2,u1_struct_0(sK0)) | ~r1_tarski(X2,sK1) | ~v3_pre_topc(X2,sK0) | k1_xboole_0 = X2) ) | ~spl5_6),
% 1.36/0.54    inference(resolution,[],[f101,f70])).
% 1.36/0.54  fof(f70,plain,(
% 1.36/0.54    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f44])).
% 1.36/0.54  fof(f44,plain,(
% 1.36/0.54    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.36/0.54    inference(nnf_transformation,[],[f7])).
% 1.36/0.54  fof(f7,axiom,(
% 1.36/0.54    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.36/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.36/0.54  fof(f101,plain,(
% 1.36/0.54    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = X3 | ~r1_tarski(X3,sK1) | ~v3_pre_topc(X3,sK0)) ) | ~spl5_6),
% 1.36/0.54    inference(avatar_component_clause,[],[f100])).
% 1.36/0.54  fof(f167,plain,(
% 1.36/0.54    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~spl5_13),
% 1.36/0.54    inference(avatar_component_clause,[],[f165])).
% 1.36/0.54  fof(f157,plain,(
% 1.36/0.54    v3_pre_topc(k1_tops_1(sK0,sK1),sK0) | ~spl5_11),
% 1.36/0.54    inference(avatar_component_clause,[],[f155])).
% 1.36/0.54  fof(f162,plain,(
% 1.36/0.54    k1_xboole_0 != k1_tops_1(sK0,sK1) | spl5_12),
% 1.36/0.54    inference(avatar_component_clause,[],[f160])).
% 1.36/0.54  fof(f259,plain,(
% 1.36/0.54    spl5_23 | ~spl5_10 | ~spl5_13),
% 1.36/0.54    inference(avatar_split_clause,[],[f228,f165,f150,f256])).
% 1.36/0.54  fof(f150,plain,(
% 1.36/0.54    spl5_10 <=> r1_tarski(sK1,u1_struct_0(sK0))),
% 1.36/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 1.36/0.54  fof(f228,plain,(
% 1.36/0.54    r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) | (~spl5_10 | ~spl5_13)),
% 1.36/0.54    inference(unit_resulting_resolution,[],[f152,f167,f72])).
% 1.36/0.54  fof(f152,plain,(
% 1.36/0.54    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl5_10),
% 1.36/0.54    inference(avatar_component_clause,[],[f150])).
% 1.36/0.54  fof(f186,plain,(
% 1.36/0.54    spl5_10 | ~spl5_7),
% 1.36/0.54    inference(avatar_split_clause,[],[f148,f104,f150])).
% 1.36/0.54  fof(f148,plain,(
% 1.36/0.54    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl5_7),
% 1.36/0.54    inference(resolution,[],[f106,f69])).
% 1.36/0.54  fof(f69,plain,(
% 1.36/0.54    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.36/0.54    inference(cnf_transformation,[],[f44])).
% 1.36/0.54  fof(f170,plain,(
% 1.36/0.54    spl5_13 | ~spl5_7 | ~spl5_8),
% 1.36/0.54    inference(avatar_split_clause,[],[f169,f109,f104,f165])).
% 1.36/0.54  fof(f169,plain,(
% 1.36/0.54    r1_tarski(k1_tops_1(sK0,sK1),sK1) | (~spl5_7 | ~spl5_8)),
% 1.36/0.54    inference(subsumption_resolution,[],[f138,f111])).
% 1.36/0.54  fof(f138,plain,(
% 1.36/0.54    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~l1_pre_topc(sK0) | ~spl5_7),
% 1.36/0.54    inference(resolution,[],[f106,f54])).
% 1.36/0.54  fof(f54,plain,(
% 1.36/0.54    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f17])).
% 1.36/0.54  fof(f17,plain,(
% 1.36/0.54    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.36/0.54    inference(ennf_transformation,[],[f10])).
% 1.36/0.54  fof(f10,axiom,(
% 1.36/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 1.36/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).
% 1.36/0.54  fof(f158,plain,(
% 1.36/0.54    spl5_11 | ~spl5_7 | ~spl5_8 | ~spl5_9),
% 1.36/0.54    inference(avatar_split_clause,[],[f136,f114,f109,f104,f155])).
% 1.36/0.54  fof(f136,plain,(
% 1.36/0.54    v3_pre_topc(k1_tops_1(sK0,sK1),sK0) | (~spl5_7 | ~spl5_8 | ~spl5_9)),
% 1.36/0.54    inference(unit_resulting_resolution,[],[f116,f111,f106,f65])).
% 1.36/0.54  fof(f65,plain,(
% 1.36/0.54    ( ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f23])).
% 1.36/0.54  fof(f23,plain,(
% 1.36/0.54    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.36/0.54    inference(flattening,[],[f22])).
% 1.36/0.54  fof(f22,plain,(
% 1.36/0.54    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.36/0.54    inference(ennf_transformation,[],[f9])).
% 1.36/0.54  fof(f9,axiom,(
% 1.36/0.54    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 1.36/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).
% 1.36/0.54  fof(f117,plain,(
% 1.36/0.54    spl5_9),
% 1.36/0.54    inference(avatar_split_clause,[],[f45,f114])).
% 1.36/0.54  fof(f45,plain,(
% 1.36/0.54    v2_pre_topc(sK0)),
% 1.36/0.54    inference(cnf_transformation,[],[f34])).
% 1.36/0.54  fof(f34,plain,(
% 1.36/0.54    (((k1_xboole_0 != sK2 & v3_pre_topc(sK2,sK0) & r1_tarski(sK2,sK1) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) | ~v2_tops_1(sK1,sK0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,sK0) | ~r1_tarski(X3,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_1(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 1.36/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f30,f33,f32,f31])).
% 1.36/0.54  fof(f31,plain,(
% 1.36/0.54    ? [X0] : (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,X0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,sK0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) | ~v2_tops_1(X1,sK0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,sK0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_1(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 1.36/0.54    introduced(choice_axiom,[])).
% 1.36/0.54  fof(f32,plain,(
% 1.36/0.54    ? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,sK0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) | ~v2_tops_1(X1,sK0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,sK0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_1(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,sK0) & r1_tarski(X2,sK1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) | ~v2_tops_1(sK1,sK0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,sK0) | ~r1_tarski(X3,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_1(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.36/0.54    introduced(choice_axiom,[])).
% 1.36/0.54  fof(f33,plain,(
% 1.36/0.54    ? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,sK0) & r1_tarski(X2,sK1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (k1_xboole_0 != sK2 & v3_pre_topc(sK2,sK0) & r1_tarski(sK2,sK1) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.36/0.54    introduced(choice_axiom,[])).
% 1.36/0.54  fof(f30,plain,(
% 1.36/0.54    ? [X0] : (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,X0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.36/0.54    inference(rectify,[],[f29])).
% 1.36/0.54  fof(f29,plain,(
% 1.36/0.54    ? [X0] : (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X2] : (k1_xboole_0 = X2 | ~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.36/0.54    inference(flattening,[],[f28])).
% 1.36/0.54  fof(f28,plain,(
% 1.36/0.54    ? [X0] : (? [X1] : (((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X2] : (k1_xboole_0 = X2 | ~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.36/0.54    inference(nnf_transformation,[],[f16])).
% 1.36/0.54  fof(f16,plain,(
% 1.36/0.54    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> ! [X2] : (k1_xboole_0 = X2 | ~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.36/0.54    inference(flattening,[],[f15])).
% 1.36/0.54  fof(f15,plain,(
% 1.36/0.54    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> ! [X2] : ((k1_xboole_0 = X2 | (~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 1.36/0.54    inference(ennf_transformation,[],[f14])).
% 1.36/0.54  fof(f14,negated_conjecture,(
% 1.36/0.54    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X2,X0) & r1_tarski(X2,X1)) => k1_xboole_0 = X2)))))),
% 1.36/0.54    inference(negated_conjecture,[],[f13])).
% 1.36/0.54  fof(f13,conjecture,(
% 1.36/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X2,X0) & r1_tarski(X2,X1)) => k1_xboole_0 = X2)))))),
% 1.36/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_tops_1)).
% 1.36/0.54  fof(f112,plain,(
% 1.36/0.54    spl5_8),
% 1.36/0.54    inference(avatar_split_clause,[],[f46,f109])).
% 1.36/0.54  fof(f46,plain,(
% 1.36/0.54    l1_pre_topc(sK0)),
% 1.36/0.54    inference(cnf_transformation,[],[f34])).
% 1.36/0.54  fof(f107,plain,(
% 1.36/0.54    spl5_7),
% 1.36/0.54    inference(avatar_split_clause,[],[f47,f104])).
% 1.36/0.54  fof(f47,plain,(
% 1.36/0.54    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.36/0.54    inference(cnf_transformation,[],[f34])).
% 1.36/0.54  fof(f102,plain,(
% 1.36/0.54    spl5_1 | spl5_6),
% 1.36/0.54    inference(avatar_split_clause,[],[f48,f100,f76])).
% 1.36/0.54  fof(f48,plain,(
% 1.36/0.54    ( ! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,sK0) | ~r1_tarski(X3,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tops_1(sK1,sK0)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f34])).
% 1.36/0.54  fof(f98,plain,(
% 1.36/0.54    ~spl5_1 | spl5_5),
% 1.36/0.54    inference(avatar_split_clause,[],[f49,f95,f76])).
% 1.36/0.54  fof(f49,plain,(
% 1.36/0.54    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tops_1(sK1,sK0)),
% 1.36/0.54    inference(cnf_transformation,[],[f34])).
% 1.36/0.54  fof(f93,plain,(
% 1.36/0.54    ~spl5_1 | spl5_4),
% 1.36/0.54    inference(avatar_split_clause,[],[f50,f90,f76])).
% 1.36/0.54  fof(f50,plain,(
% 1.36/0.54    r1_tarski(sK2,sK1) | ~v2_tops_1(sK1,sK0)),
% 1.36/0.54    inference(cnf_transformation,[],[f34])).
% 1.36/0.54  fof(f88,plain,(
% 1.36/0.54    ~spl5_1 | spl5_3),
% 1.36/0.54    inference(avatar_split_clause,[],[f51,f85,f76])).
% 1.36/0.54  fof(f51,plain,(
% 1.36/0.54    v3_pre_topc(sK2,sK0) | ~v2_tops_1(sK1,sK0)),
% 1.36/0.54    inference(cnf_transformation,[],[f34])).
% 1.36/0.54  fof(f83,plain,(
% 1.36/0.54    ~spl5_1 | ~spl5_2),
% 1.36/0.54    inference(avatar_split_clause,[],[f52,f80,f76])).
% 1.36/0.54  fof(f52,plain,(
% 1.36/0.54    k1_xboole_0 != sK2 | ~v2_tops_1(sK1,sK0)),
% 1.36/0.54    inference(cnf_transformation,[],[f34])).
% 1.36/0.54  % SZS output end Proof for theBenchmark
% 1.36/0.54  % (3082)------------------------------
% 1.36/0.54  % (3082)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.54  % (3082)Termination reason: Refutation
% 1.36/0.54  
% 1.36/0.54  % (3082)Memory used [KB]: 6652
% 1.36/0.54  % (3082)Time elapsed: 0.139 s
% 1.36/0.54  % (3082)------------------------------
% 1.36/0.54  % (3082)------------------------------
% 1.36/0.54  % (3064)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.36/0.54  % (3068)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.36/0.54  % (3056)Success in time 0.18 s
%------------------------------------------------------------------------------
