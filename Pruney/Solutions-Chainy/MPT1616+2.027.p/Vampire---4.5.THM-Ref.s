%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:47 EST 2020

% Result     : Theorem 1.20s
% Output     : Refutation 1.20s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 176 expanded)
%              Number of leaves         :   28 (  67 expanded)
%              Depth                    :    9
%              Number of atoms          :  404 ( 682 expanded)
%              Number of equality atoms :   30 (  59 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f259,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f82,f87,f93,f99,f121,f136,f148,f157,f182,f187,f192,f250,f258])).

fof(f258,plain,
    ( spl6_3
    | ~ spl6_7
    | spl6_10
    | ~ spl6_16 ),
    inference(avatar_contradiction_clause,[],[f257])).

fof(f257,plain,
    ( $false
    | spl6_3
    | ~ spl6_7
    | spl6_10
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f256,f186])).

fof(f186,plain,
    ( ~ v1_xboole_0(u1_pre_topc(sK2))
    | spl6_10 ),
    inference(avatar_component_clause,[],[f184])).

fof(f184,plain,
    ( spl6_10
  <=> v1_xboole_0(u1_pre_topc(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f256,plain,
    ( v1_xboole_0(u1_pre_topc(sK2))
    | spl6_3
    | ~ spl6_7
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f255,f92])).

fof(f92,plain,
    ( u1_struct_0(sK2) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK2)))
    | spl6_3 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl6_3
  <=> u1_struct_0(sK2) = k4_yellow_0(k2_yellow_1(u1_pre_topc(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f255,plain,
    ( u1_struct_0(sK2) = k4_yellow_0(k2_yellow_1(u1_pre_topc(sK2)))
    | v1_xboole_0(u1_pre_topc(sK2))
    | ~ spl6_7
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f254,f147])).

fof(f147,plain,
    ( r2_hidden(u1_struct_0(sK2),u1_pre_topc(sK2))
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f145])).

fof(f145,plain,
    ( spl6_7
  <=> r2_hidden(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f254,plain,
    ( ~ r2_hidden(u1_struct_0(sK2),u1_pre_topc(sK2))
    | u1_struct_0(sK2) = k4_yellow_0(k2_yellow_1(u1_pre_topc(sK2)))
    | v1_xboole_0(u1_pre_topc(sK2))
    | ~ spl6_16 ),
    inference(superposition,[],[f45,f249])).

fof(f249,plain,
    ( u1_struct_0(sK2) = k3_tarski(u1_pre_topc(sK2))
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f247])).

fof(f247,plain,
    ( spl6_16
  <=> u1_struct_0(sK2) = k3_tarski(u1_pre_topc(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f45,plain,(
    ! [X0] :
      ( ~ r2_hidden(k3_tarski(X0),X0)
      | k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k3_tarski(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k3_tarski(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( r2_hidden(k3_tarski(X0),X0)
       => k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_yellow_1)).

fof(f250,plain,
    ( spl6_16
    | ~ spl6_9
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f197,f189,f179,f247])).

fof(f179,plain,
    ( spl6_9
  <=> r1_tarski(u1_struct_0(sK2),k3_tarski(u1_pre_topc(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f189,plain,
    ( spl6_11
  <=> r1_tarski(k3_tarski(u1_pre_topc(sK2)),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f197,plain,
    ( u1_struct_0(sK2) = k3_tarski(u1_pre_topc(sK2))
    | ~ spl6_9
    | ~ spl6_11 ),
    inference(subsumption_resolution,[],[f195,f191])).

fof(f191,plain,
    ( r1_tarski(k3_tarski(u1_pre_topc(sK2)),u1_struct_0(sK2))
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f189])).

fof(f195,plain,
    ( ~ r1_tarski(k3_tarski(u1_pre_topc(sK2)),u1_struct_0(sK2))
    | u1_struct_0(sK2) = k3_tarski(u1_pre_topc(sK2))
    | ~ spl6_9 ),
    inference(resolution,[],[f181,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f181,plain,
    ( r1_tarski(u1_struct_0(sK2),k3_tarski(u1_pre_topc(sK2)))
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f179])).

fof(f192,plain,
    ( spl6_11
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f162,f154,f189])).

fof(f154,plain,
    ( spl6_8
  <=> r1_tarski(u1_pre_topc(sK2),k1_zfmisc_1(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f162,plain,
    ( r1_tarski(k3_tarski(u1_pre_topc(sK2)),u1_struct_0(sK2))
    | ~ spl6_8 ),
    inference(forward_demodulation,[],[f158,f44])).

fof(f44,plain,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

fof(f158,plain,
    ( r1_tarski(k3_tarski(u1_pre_topc(sK2)),k3_tarski(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ spl6_8 ),
    inference(unit_resulting_resolution,[],[f156,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(k3_tarski(X0),k3_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),k3_tarski(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_tarski(X0),k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_zfmisc_1)).

fof(f156,plain,
    ( r1_tarski(u1_pre_topc(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f154])).

fof(f187,plain,
    ( ~ spl6_10
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f168,f145,f184])).

fof(f168,plain,
    ( ~ v1_xboole_0(u1_pre_topc(sK2))
    | ~ spl6_7 ),
    inference(unit_resulting_resolution,[],[f100,f147,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f100,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f76,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f76,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f182,plain,
    ( spl6_9
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f149,f118,f179])).

fof(f118,plain,
    ( spl6_5
  <=> sP0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f149,plain,
    ( r1_tarski(u1_struct_0(sK2),k3_tarski(u1_pre_topc(sK2)))
    | ~ spl6_5 ),
    inference(unit_resulting_resolution,[],[f120,f76,f110])).

fof(f110,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0)
      | ~ r1_tarski(k3_tarski(u1_pre_topc(X0)),X1)
      | r1_tarski(u1_struct_0(X0),X1) ) ),
    inference(resolution,[],[f74,f49])).

fof(f49,plain,(
    ! [X0] :
      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),sK3(X0),sK4(X0)),u1_pre_topc(X0))
          & r2_hidden(sK4(X0),u1_pre_topc(X0))
          & r2_hidden(sK3(X0),u1_pre_topc(X0))
          & m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0)))
          & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))) )
        | ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK5(X0)),u1_pre_topc(X0))
          & r1_tarski(sK5(X0),u1_pre_topc(X0))
          & m1_subset_1(sK5(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
      & ( ( ! [X4] :
              ( ! [X5] :
                  ( r2_hidden(k9_subset_1(u1_struct_0(X0),X4,X5),u1_pre_topc(X0))
                  | ~ r2_hidden(X5,u1_pre_topc(X0))
                  | ~ r2_hidden(X4,u1_pre_topc(X0))
                  | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
          & ! [X6] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X6),u1_pre_topc(X0))
              | ~ r1_tarski(X6,u1_pre_topc(X0))
              | ~ m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        | ~ sP0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f33,f36,f35,f34])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
              & r2_hidden(X2,u1_pre_topc(X0))
              & r2_hidden(X1,u1_pre_topc(X0))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),sK3(X0),X2),u1_pre_topc(X0))
            & r2_hidden(X2,u1_pre_topc(X0))
            & r2_hidden(sK3(X0),u1_pre_topc(X0))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( ? [X2] :
          ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),sK3(X0),X2),u1_pre_topc(X0))
          & r2_hidden(X2,u1_pre_topc(X0))
          & r2_hidden(sK3(X0),u1_pre_topc(X0))
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),sK3(X0),sK4(X0)),u1_pre_topc(X0))
        & r2_hidden(sK4(X0),u1_pre_topc(X0))
        & r2_hidden(sK3(X0),u1_pre_topc(X0))
        & m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X3] :
          ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
          & r1_tarski(X3,u1_pre_topc(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK5(X0)),u1_pre_topc(X0))
        & r1_tarski(sK5(X0),u1_pre_topc(X0))
        & m1_subset_1(sK5(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ? [X1] :
            ( ? [X2] :
                ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                & r2_hidden(X2,u1_pre_topc(X0))
                & r2_hidden(X1,u1_pre_topc(X0))
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        | ? [X3] :
            ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
            & r1_tarski(X3,u1_pre_topc(X0))
            & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
      & ( ( ! [X4] :
              ( ! [X5] :
                  ( r2_hidden(k9_subset_1(u1_struct_0(X0),X4,X5),u1_pre_topc(X0))
                  | ~ r2_hidden(X5,u1_pre_topc(X0))
                  | ~ r2_hidden(X4,u1_pre_topc(X0))
                  | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
          & ! [X6] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X6),u1_pre_topc(X0))
              | ~ r1_tarski(X6,u1_pre_topc(X0))
              | ~ m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        | ~ sP0(X0) ) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ? [X1] :
            ( ? [X2] :
                ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                & r2_hidden(X2,u1_pre_topc(X0))
                & r2_hidden(X1,u1_pre_topc(X0))
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        | ? [X3] :
            ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
            & r1_tarski(X3,u1_pre_topc(X0))
            & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
      & ( ( ! [X1] :
              ( ! [X2] :
                  ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                  | ~ r2_hidden(X2,u1_pre_topc(X0))
                  | ~ r2_hidden(X1,u1_pre_topc(X0))
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        | ~ sP0(X0) ) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ? [X1] :
            ( ? [X2] :
                ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                & r2_hidden(X2,u1_pre_topc(X0))
                & r2_hidden(X1,u1_pre_topc(X0))
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        | ? [X3] :
            ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
            & r1_tarski(X3,u1_pre_topc(X0))
            & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
      & ( ( ! [X1] :
              ( ! [X2] :
                  ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                  | ~ r2_hidden(X2,u1_pre_topc(X0))
                  | ~ r2_hidden(X1,u1_pre_topc(X0))
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        | ~ sP0(X0) ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( sP0(X0)
    <=> ( ! [X1] :
            ( ! [X2] :
                ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                | ~ r2_hidden(X2,u1_pre_topc(X0))
                | ~ r2_hidden(X1,u1_pre_topc(X0))
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & ! [X3] :
            ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
            | ~ r1_tarski(X3,u1_pre_topc(X0))
            | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r1_tarski(X2,X1)
      | ~ r1_tarski(k3_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(k3_tarski(X0),X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(k3_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X2,X0)
        & r1_tarski(k3_tarski(X0),X1) )
     => r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_setfam_1)).

fof(f120,plain,
    ( sP0(sK2)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f118])).

fof(f157,plain,
    ( spl6_8
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f138,f133,f154])).

fof(f133,plain,
    ( spl6_6
  <=> m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f138,plain,
    ( r1_tarski(u1_pre_topc(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl6_6 ),
    inference(unit_resulting_resolution,[],[f135,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f135,plain,
    ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f133])).

fof(f148,plain,
    ( spl6_7
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f125,f118,f145])).

fof(f125,plain,
    ( r2_hidden(u1_struct_0(sK2),u1_pre_topc(sK2))
    | ~ spl6_5 ),
    inference(unit_resulting_resolution,[],[f120,f49])).

fof(f136,plain,
    ( spl6_6
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f104,f84,f133])).

fof(f84,plain,
    ( spl6_2
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f104,plain,
    ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f86,f46])).

fof(f46,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f86,plain,
    ( l1_pre_topc(sK2)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f84])).

fof(f121,plain,
    ( spl6_5
    | ~ spl6_1
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f108,f96,f79,f118])).

fof(f79,plain,
    ( spl6_1
  <=> v2_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f96,plain,
    ( spl6_4
  <=> sP1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f108,plain,
    ( sP0(sK2)
    | ~ spl6_1
    | ~ spl6_4 ),
    inference(unit_resulting_resolution,[],[f81,f98,f47])).

fof(f47,plain,(
    ! [X0] :
      ( ~ sP1(X0)
      | ~ v2_pre_topc(X0)
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( ( v2_pre_topc(X0)
          | ~ sP0(X0) )
        & ( sP0(X0)
          | ~ v2_pre_topc(X0) ) )
      | ~ sP1(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> sP0(X0) )
      | ~ sP1(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f98,plain,
    ( sP1(sK2)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f96])).

fof(f81,plain,
    ( v2_pre_topc(sK2)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f79])).

fof(f99,plain,
    ( spl6_4
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f88,f84,f96])).

fof(f88,plain,
    ( sP1(sK2)
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f86,f67])).

fof(f67,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f20,f26,f25])).

fof(f20,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( ! [X2] :
                  ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                  | ~ r2_hidden(X2,u1_pre_topc(X0))
                  | ~ r2_hidden(X1,u1_pre_topc(X0))
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

% (24026)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
fof(f19,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( ! [X2] :
                  ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                  | ~ r2_hidden(X2,u1_pre_topc(X0))
                  | ~ r2_hidden(X1,u1_pre_topc(X0))
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r2_hidden(X2,u1_pre_topc(X0))
                      & r2_hidden(X1,u1_pre_topc(X0)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) ) ) )
          & ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( r1_tarski(X3,u1_pre_topc(X0))
               => r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) ) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) ) ) ),
    inference(rectify,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r2_hidden(X2,u1_pre_topc(X0))
                      & r2_hidden(X1,u1_pre_topc(X0)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) ) ) )
          & ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( r1_tarski(X1,u1_pre_topc(X0))
               => r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) ) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_pre_topc)).

fof(f93,plain,(
    ~ spl6_3 ),
    inference(avatar_split_clause,[],[f43,f90])).

fof(f43,plain,(
    u1_struct_0(sK2) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK2))) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( u1_struct_0(sK2) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK2)))
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f15,f28])).

fof(f28,plain,
    ( ? [X0] :
        ( u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( u1_struct_0(sK2) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK2)))
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0] :
      ( u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0)))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0)))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_yellow_1)).

fof(f87,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f42,f84])).

fof(f42,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f82,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f41,f79])).

fof(f41,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n018.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 13:03:27 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.50  % (24016)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.50  % (24012)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.50  % (24015)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.50  % (24012)Refutation not found, incomplete strategy% (24012)------------------------------
% 0.22/0.50  % (24012)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (24012)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (24012)Memory used [KB]: 10618
% 0.22/0.50  % (24012)Time elapsed: 0.084 s
% 0.22/0.50  % (24012)------------------------------
% 0.22/0.50  % (24012)------------------------------
% 0.22/0.50  % (24035)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.51  % (24024)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.20/0.51  % (24035)Refutation found. Thanks to Tanya!
% 1.20/0.51  % SZS status Theorem for theBenchmark
% 1.20/0.51  % SZS output start Proof for theBenchmark
% 1.20/0.51  fof(f259,plain,(
% 1.20/0.51    $false),
% 1.20/0.51    inference(avatar_sat_refutation,[],[f82,f87,f93,f99,f121,f136,f148,f157,f182,f187,f192,f250,f258])).
% 1.20/0.51  fof(f258,plain,(
% 1.20/0.51    spl6_3 | ~spl6_7 | spl6_10 | ~spl6_16),
% 1.20/0.51    inference(avatar_contradiction_clause,[],[f257])).
% 1.20/0.51  fof(f257,plain,(
% 1.20/0.51    $false | (spl6_3 | ~spl6_7 | spl6_10 | ~spl6_16)),
% 1.20/0.51    inference(subsumption_resolution,[],[f256,f186])).
% 1.20/0.51  fof(f186,plain,(
% 1.20/0.51    ~v1_xboole_0(u1_pre_topc(sK2)) | spl6_10),
% 1.20/0.51    inference(avatar_component_clause,[],[f184])).
% 1.20/0.51  fof(f184,plain,(
% 1.20/0.51    spl6_10 <=> v1_xboole_0(u1_pre_topc(sK2))),
% 1.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 1.20/0.51  fof(f256,plain,(
% 1.20/0.51    v1_xboole_0(u1_pre_topc(sK2)) | (spl6_3 | ~spl6_7 | ~spl6_16)),
% 1.20/0.51    inference(subsumption_resolution,[],[f255,f92])).
% 1.20/0.51  fof(f92,plain,(
% 1.20/0.51    u1_struct_0(sK2) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK2))) | spl6_3),
% 1.20/0.51    inference(avatar_component_clause,[],[f90])).
% 1.20/0.51  fof(f90,plain,(
% 1.20/0.51    spl6_3 <=> u1_struct_0(sK2) = k4_yellow_0(k2_yellow_1(u1_pre_topc(sK2)))),
% 1.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 1.20/0.51  fof(f255,plain,(
% 1.20/0.51    u1_struct_0(sK2) = k4_yellow_0(k2_yellow_1(u1_pre_topc(sK2))) | v1_xboole_0(u1_pre_topc(sK2)) | (~spl6_7 | ~spl6_16)),
% 1.20/0.51    inference(subsumption_resolution,[],[f254,f147])).
% 1.20/0.51  fof(f147,plain,(
% 1.20/0.51    r2_hidden(u1_struct_0(sK2),u1_pre_topc(sK2)) | ~spl6_7),
% 1.20/0.51    inference(avatar_component_clause,[],[f145])).
% 1.20/0.51  fof(f145,plain,(
% 1.20/0.51    spl6_7 <=> r2_hidden(u1_struct_0(sK2),u1_pre_topc(sK2))),
% 1.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 1.20/0.51  fof(f254,plain,(
% 1.20/0.51    ~r2_hidden(u1_struct_0(sK2),u1_pre_topc(sK2)) | u1_struct_0(sK2) = k4_yellow_0(k2_yellow_1(u1_pre_topc(sK2))) | v1_xboole_0(u1_pre_topc(sK2)) | ~spl6_16),
% 1.20/0.51    inference(superposition,[],[f45,f249])).
% 1.20/0.51  fof(f249,plain,(
% 1.20/0.51    u1_struct_0(sK2) = k3_tarski(u1_pre_topc(sK2)) | ~spl6_16),
% 1.20/0.51    inference(avatar_component_clause,[],[f247])).
% 1.20/0.51  fof(f247,plain,(
% 1.20/0.51    spl6_16 <=> u1_struct_0(sK2) = k3_tarski(u1_pre_topc(sK2))),
% 1.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 1.20/0.51  fof(f45,plain,(
% 1.20/0.51    ( ! [X0] : (~r2_hidden(k3_tarski(X0),X0) | k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) | v1_xboole_0(X0)) )),
% 1.20/0.51    inference(cnf_transformation,[],[f17])).
% 1.20/0.51  fof(f17,plain,(
% 1.20/0.51    ! [X0] : (k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k3_tarski(X0),X0) | v1_xboole_0(X0))),
% 1.20/0.51    inference(flattening,[],[f16])).
% 1.20/0.51  fof(f16,plain,(
% 1.20/0.51    ! [X0] : ((k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k3_tarski(X0),X0)) | v1_xboole_0(X0))),
% 1.20/0.51    inference(ennf_transformation,[],[f9])).
% 1.20/0.51  fof(f9,axiom,(
% 1.20/0.51    ! [X0] : (~v1_xboole_0(X0) => (r2_hidden(k3_tarski(X0),X0) => k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))))),
% 1.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_yellow_1)).
% 1.20/0.51  fof(f250,plain,(
% 1.20/0.51    spl6_16 | ~spl6_9 | ~spl6_11),
% 1.20/0.51    inference(avatar_split_clause,[],[f197,f189,f179,f247])).
% 1.20/0.51  fof(f179,plain,(
% 1.20/0.51    spl6_9 <=> r1_tarski(u1_struct_0(sK2),k3_tarski(u1_pre_topc(sK2)))),
% 1.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 1.20/0.51  fof(f189,plain,(
% 1.20/0.51    spl6_11 <=> r1_tarski(k3_tarski(u1_pre_topc(sK2)),u1_struct_0(sK2))),
% 1.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 1.20/0.51  fof(f197,plain,(
% 1.20/0.51    u1_struct_0(sK2) = k3_tarski(u1_pre_topc(sK2)) | (~spl6_9 | ~spl6_11)),
% 1.20/0.51    inference(subsumption_resolution,[],[f195,f191])).
% 1.20/0.51  fof(f191,plain,(
% 1.20/0.51    r1_tarski(k3_tarski(u1_pre_topc(sK2)),u1_struct_0(sK2)) | ~spl6_11),
% 1.20/0.51    inference(avatar_component_clause,[],[f189])).
% 1.20/0.51  fof(f195,plain,(
% 1.20/0.51    ~r1_tarski(k3_tarski(u1_pre_topc(sK2)),u1_struct_0(sK2)) | u1_struct_0(sK2) = k3_tarski(u1_pre_topc(sK2)) | ~spl6_9),
% 1.20/0.51    inference(resolution,[],[f181,f71])).
% 1.20/0.51  fof(f71,plain,(
% 1.20/0.51    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.20/0.51    inference(cnf_transformation,[],[f39])).
% 1.20/0.51  fof(f39,plain,(
% 1.20/0.51    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.20/0.51    inference(flattening,[],[f38])).
% 1.20/0.51  fof(f38,plain,(
% 1.20/0.51    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.20/0.51    inference(nnf_transformation,[],[f1])).
% 1.20/0.51  fof(f1,axiom,(
% 1.20/0.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.20/0.51  fof(f181,plain,(
% 1.20/0.51    r1_tarski(u1_struct_0(sK2),k3_tarski(u1_pre_topc(sK2))) | ~spl6_9),
% 1.20/0.51    inference(avatar_component_clause,[],[f179])).
% 1.20/0.51  fof(f192,plain,(
% 1.20/0.51    spl6_11 | ~spl6_8),
% 1.20/0.51    inference(avatar_split_clause,[],[f162,f154,f189])).
% 1.20/0.51  fof(f154,plain,(
% 1.20/0.51    spl6_8 <=> r1_tarski(u1_pre_topc(sK2),k1_zfmisc_1(u1_struct_0(sK2)))),
% 1.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 1.20/0.51  fof(f162,plain,(
% 1.20/0.51    r1_tarski(k3_tarski(u1_pre_topc(sK2)),u1_struct_0(sK2)) | ~spl6_8),
% 1.20/0.51    inference(forward_demodulation,[],[f158,f44])).
% 1.20/0.51  fof(f44,plain,(
% 1.20/0.51    ( ! [X0] : (k3_tarski(k1_zfmisc_1(X0)) = X0) )),
% 1.20/0.51    inference(cnf_transformation,[],[f3])).
% 1.20/0.51  fof(f3,axiom,(
% 1.20/0.51    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0),
% 1.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).
% 1.20/0.51  fof(f158,plain,(
% 1.20/0.51    r1_tarski(k3_tarski(u1_pre_topc(sK2)),k3_tarski(k1_zfmisc_1(u1_struct_0(sK2)))) | ~spl6_8),
% 1.20/0.51    inference(unit_resulting_resolution,[],[f156,f68])).
% 1.20/0.51  fof(f68,plain,(
% 1.20/0.51    ( ! [X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k3_tarski(X0),k3_tarski(X1))) )),
% 1.20/0.51    inference(cnf_transformation,[],[f21])).
% 1.20/0.51  fof(f21,plain,(
% 1.20/0.51    ! [X0,X1] : (r1_tarski(k3_tarski(X0),k3_tarski(X1)) | ~r1_tarski(X0,X1))),
% 1.20/0.51    inference(ennf_transformation,[],[f2])).
% 1.20/0.51  fof(f2,axiom,(
% 1.20/0.51    ! [X0,X1] : (r1_tarski(X0,X1) => r1_tarski(k3_tarski(X0),k3_tarski(X1)))),
% 1.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_zfmisc_1)).
% 1.20/0.51  fof(f156,plain,(
% 1.20/0.51    r1_tarski(u1_pre_topc(sK2),k1_zfmisc_1(u1_struct_0(sK2))) | ~spl6_8),
% 1.20/0.51    inference(avatar_component_clause,[],[f154])).
% 1.20/0.51  fof(f187,plain,(
% 1.20/0.51    ~spl6_10 | ~spl6_7),
% 1.20/0.51    inference(avatar_split_clause,[],[f168,f145,f184])).
% 1.20/0.51  fof(f168,plain,(
% 1.20/0.51    ~v1_xboole_0(u1_pre_topc(sK2)) | ~spl6_7),
% 1.20/0.51    inference(unit_resulting_resolution,[],[f100,f147,f75])).
% 1.20/0.51  fof(f75,plain,(
% 1.20/0.51    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 1.20/0.51    inference(cnf_transformation,[],[f24])).
% 1.20/0.51  fof(f24,plain,(
% 1.20/0.51    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.20/0.51    inference(ennf_transformation,[],[f6])).
% 1.20/0.51  fof(f6,axiom,(
% 1.20/0.51    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 1.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 1.20/0.51  fof(f100,plain,(
% 1.20/0.51    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 1.20/0.51    inference(unit_resulting_resolution,[],[f76,f73])).
% 1.20/0.51  fof(f73,plain,(
% 1.20/0.51    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.20/0.51    inference(cnf_transformation,[],[f40])).
% 1.20/0.51  fof(f40,plain,(
% 1.20/0.51    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.20/0.51    inference(nnf_transformation,[],[f4])).
% 1.20/0.51  fof(f4,axiom,(
% 1.20/0.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.20/0.51  fof(f76,plain,(
% 1.20/0.51    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.20/0.51    inference(equality_resolution,[],[f70])).
% 1.20/0.51  fof(f70,plain,(
% 1.20/0.51    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.20/0.51    inference(cnf_transformation,[],[f39])).
% 1.20/0.51  fof(f182,plain,(
% 1.20/0.51    spl6_9 | ~spl6_5),
% 1.20/0.51    inference(avatar_split_clause,[],[f149,f118,f179])).
% 1.20/0.51  fof(f118,plain,(
% 1.20/0.51    spl6_5 <=> sP0(sK2)),
% 1.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 1.20/0.51  fof(f149,plain,(
% 1.20/0.51    r1_tarski(u1_struct_0(sK2),k3_tarski(u1_pre_topc(sK2))) | ~spl6_5),
% 1.20/0.51    inference(unit_resulting_resolution,[],[f120,f76,f110])).
% 1.20/0.51  fof(f110,plain,(
% 1.20/0.51    ( ! [X0,X1] : (~sP0(X0) | ~r1_tarski(k3_tarski(u1_pre_topc(X0)),X1) | r1_tarski(u1_struct_0(X0),X1)) )),
% 1.20/0.51    inference(resolution,[],[f74,f49])).
% 1.20/0.51  fof(f49,plain,(
% 1.20/0.51    ( ! [X0] : (r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) | ~sP0(X0)) )),
% 1.20/0.51    inference(cnf_transformation,[],[f37])).
% 1.20/0.51  fof(f37,plain,(
% 1.20/0.51    ! [X0] : ((sP0(X0) | ((~r2_hidden(k9_subset_1(u1_struct_0(X0),sK3(X0),sK4(X0)),u1_pre_topc(X0)) & r2_hidden(sK4(X0),u1_pre_topc(X0)) & r2_hidden(sK3(X0),u1_pre_topc(X0)) & m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))) | (~r2_hidden(k5_setfam_1(u1_struct_0(X0),sK5(X0)),u1_pre_topc(X0)) & r1_tarski(sK5(X0),u1_pre_topc(X0)) & m1_subset_1(sK5(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((! [X4] : (! [X5] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X4,X5),u1_pre_topc(X0)) | ~r2_hidden(X5,u1_pre_topc(X0)) | ~r2_hidden(X4,u1_pre_topc(X0)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X6] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X6),u1_pre_topc(X0)) | ~r1_tarski(X6,u1_pre_topc(X0)) | ~m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~sP0(X0)))),
% 1.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f33,f36,f35,f34])).
% 1.20/0.51  fof(f34,plain,(
% 1.20/0.51    ! [X0] : (? [X1] : (? [X2] : (~r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) & r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (~r2_hidden(k9_subset_1(u1_struct_0(X0),sK3(X0),X2),u1_pre_topc(X0)) & r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(sK3(X0),u1_pre_topc(X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.20/0.51    introduced(choice_axiom,[])).
% 1.20/0.51  fof(f35,plain,(
% 1.20/0.51    ! [X0] : (? [X2] : (~r2_hidden(k9_subset_1(u1_struct_0(X0),sK3(X0),X2),u1_pre_topc(X0)) & r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(sK3(X0),u1_pre_topc(X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~r2_hidden(k9_subset_1(u1_struct_0(X0),sK3(X0),sK4(X0)),u1_pre_topc(X0)) & r2_hidden(sK4(X0),u1_pre_topc(X0)) & r2_hidden(sK3(X0),u1_pre_topc(X0)) & m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.20/0.51    introduced(choice_axiom,[])).
% 1.20/0.51  fof(f36,plain,(
% 1.20/0.51    ! [X0] : (? [X3] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) & r1_tarski(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (~r2_hidden(k5_setfam_1(u1_struct_0(X0),sK5(X0)),u1_pre_topc(X0)) & r1_tarski(sK5(X0),u1_pre_topc(X0)) & m1_subset_1(sK5(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))))),
% 1.20/0.51    introduced(choice_axiom,[])).
% 1.20/0.51  fof(f33,plain,(
% 1.20/0.51    ! [X0] : ((sP0(X0) | ? [X1] : (? [X2] : (~r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) & r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ? [X3] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) & r1_tarski(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((! [X4] : (! [X5] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X4,X5),u1_pre_topc(X0)) | ~r2_hidden(X5,u1_pre_topc(X0)) | ~r2_hidden(X4,u1_pre_topc(X0)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X6] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X6),u1_pre_topc(X0)) | ~r1_tarski(X6,u1_pre_topc(X0)) | ~m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~sP0(X0)))),
% 1.20/0.51    inference(rectify,[],[f32])).
% 1.20/0.51  fof(f32,plain,(
% 1.20/0.51    ! [X0] : ((sP0(X0) | ? [X1] : (? [X2] : (~r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) & r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ? [X3] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) & r1_tarski(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~sP0(X0)))),
% 1.20/0.51    inference(flattening,[],[f31])).
% 1.20/0.51  fof(f31,plain,(
% 1.20/0.51    ! [X0] : ((sP0(X0) | (? [X1] : (? [X2] : (~r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) & r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ? [X3] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) & r1_tarski(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) & ((! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~sP0(X0)))),
% 1.20/0.51    inference(nnf_transformation,[],[f25])).
% 1.20/0.51  fof(f25,plain,(
% 1.20/0.51    ! [X0] : (sP0(X0) <=> (! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))))),
% 1.20/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.20/0.51  fof(f74,plain,(
% 1.20/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r1_tarski(X2,X1) | ~r1_tarski(k3_tarski(X0),X1)) )),
% 1.20/0.51    inference(cnf_transformation,[],[f23])).
% 1.20/0.51  fof(f23,plain,(
% 1.20/0.51    ! [X0,X1,X2] : (r1_tarski(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(k3_tarski(X0),X1))),
% 1.20/0.51    inference(flattening,[],[f22])).
% 1.20/0.51  fof(f22,plain,(
% 1.20/0.51    ! [X0,X1,X2] : (r1_tarski(X2,X1) | (~r2_hidden(X2,X0) | ~r1_tarski(k3_tarski(X0),X1)))),
% 1.20/0.51    inference(ennf_transformation,[],[f5])).
% 1.20/0.51  fof(f5,axiom,(
% 1.20/0.51    ! [X0,X1,X2] : ((r2_hidden(X2,X0) & r1_tarski(k3_tarski(X0),X1)) => r1_tarski(X2,X1))),
% 1.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_setfam_1)).
% 1.20/0.51  fof(f120,plain,(
% 1.20/0.51    sP0(sK2) | ~spl6_5),
% 1.20/0.51    inference(avatar_component_clause,[],[f118])).
% 1.20/0.51  fof(f157,plain,(
% 1.20/0.51    spl6_8 | ~spl6_6),
% 1.20/0.51    inference(avatar_split_clause,[],[f138,f133,f154])).
% 1.20/0.51  fof(f133,plain,(
% 1.20/0.51    spl6_6 <=> m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))),
% 1.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 1.20/0.51  fof(f138,plain,(
% 1.20/0.51    r1_tarski(u1_pre_topc(sK2),k1_zfmisc_1(u1_struct_0(sK2))) | ~spl6_6),
% 1.20/0.51    inference(unit_resulting_resolution,[],[f135,f72])).
% 1.20/0.51  fof(f72,plain,(
% 1.20/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.20/0.51    inference(cnf_transformation,[],[f40])).
% 1.20/0.51  fof(f135,plain,(
% 1.20/0.51    m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) | ~spl6_6),
% 1.20/0.51    inference(avatar_component_clause,[],[f133])).
% 1.20/0.51  fof(f148,plain,(
% 1.20/0.51    spl6_7 | ~spl6_5),
% 1.20/0.51    inference(avatar_split_clause,[],[f125,f118,f145])).
% 1.20/0.51  fof(f125,plain,(
% 1.20/0.51    r2_hidden(u1_struct_0(sK2),u1_pre_topc(sK2)) | ~spl6_5),
% 1.20/0.51    inference(unit_resulting_resolution,[],[f120,f49])).
% 1.20/0.51  fof(f136,plain,(
% 1.20/0.51    spl6_6 | ~spl6_2),
% 1.20/0.51    inference(avatar_split_clause,[],[f104,f84,f133])).
% 1.20/0.51  fof(f84,plain,(
% 1.20/0.51    spl6_2 <=> l1_pre_topc(sK2)),
% 1.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.20/0.51  fof(f104,plain,(
% 1.20/0.51    m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) | ~spl6_2),
% 1.20/0.51    inference(unit_resulting_resolution,[],[f86,f46])).
% 1.20/0.51  fof(f46,plain,(
% 1.20/0.51    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 1.20/0.51    inference(cnf_transformation,[],[f18])).
% 1.20/0.51  fof(f18,plain,(
% 1.20/0.51    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.20/0.51    inference(ennf_transformation,[],[f8])).
% 1.20/0.51  fof(f8,axiom,(
% 1.20/0.51    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).
% 1.20/0.51  fof(f86,plain,(
% 1.20/0.51    l1_pre_topc(sK2) | ~spl6_2),
% 1.20/0.51    inference(avatar_component_clause,[],[f84])).
% 1.20/0.51  fof(f121,plain,(
% 1.20/0.51    spl6_5 | ~spl6_1 | ~spl6_4),
% 1.20/0.51    inference(avatar_split_clause,[],[f108,f96,f79,f118])).
% 1.20/0.51  fof(f79,plain,(
% 1.20/0.51    spl6_1 <=> v2_pre_topc(sK2)),
% 1.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.20/0.51  fof(f96,plain,(
% 1.20/0.51    spl6_4 <=> sP1(sK2)),
% 1.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 1.20/0.51  fof(f108,plain,(
% 1.20/0.51    sP0(sK2) | (~spl6_1 | ~spl6_4)),
% 1.20/0.51    inference(unit_resulting_resolution,[],[f81,f98,f47])).
% 1.20/0.51  fof(f47,plain,(
% 1.20/0.51    ( ! [X0] : (~sP1(X0) | ~v2_pre_topc(X0) | sP0(X0)) )),
% 1.20/0.51    inference(cnf_transformation,[],[f30])).
% 1.20/0.51  fof(f30,plain,(
% 1.20/0.51    ! [X0] : (((v2_pre_topc(X0) | ~sP0(X0)) & (sP0(X0) | ~v2_pre_topc(X0))) | ~sP1(X0))),
% 1.20/0.51    inference(nnf_transformation,[],[f26])).
% 1.20/0.51  fof(f26,plain,(
% 1.20/0.51    ! [X0] : ((v2_pre_topc(X0) <=> sP0(X0)) | ~sP1(X0))),
% 1.20/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.20/0.51  fof(f98,plain,(
% 1.20/0.51    sP1(sK2) | ~spl6_4),
% 1.20/0.51    inference(avatar_component_clause,[],[f96])).
% 1.20/0.51  fof(f81,plain,(
% 1.20/0.51    v2_pre_topc(sK2) | ~spl6_1),
% 1.20/0.51    inference(avatar_component_clause,[],[f79])).
% 1.20/0.51  fof(f99,plain,(
% 1.20/0.51    spl6_4 | ~spl6_2),
% 1.20/0.51    inference(avatar_split_clause,[],[f88,f84,f96])).
% 1.20/0.51  fof(f88,plain,(
% 1.20/0.51    sP1(sK2) | ~spl6_2),
% 1.20/0.51    inference(unit_resulting_resolution,[],[f86,f67])).
% 1.20/0.51  fof(f67,plain,(
% 1.20/0.51    ( ! [X0] : (sP1(X0) | ~l1_pre_topc(X0)) )),
% 1.20/0.51    inference(cnf_transformation,[],[f27])).
% 1.20/0.51  fof(f27,plain,(
% 1.20/0.51    ! [X0] : (sP1(X0) | ~l1_pre_topc(X0))),
% 1.20/0.51    inference(definition_folding,[],[f20,f26,f25])).
% 1.20/0.51  fof(f20,plain,(
% 1.20/0.51    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 1.20/0.51    inference(flattening,[],[f19])).
% 1.20/0.51  % (24026)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.20/0.51  fof(f19,plain,(
% 1.20/0.51    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : ((r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | (~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : ((r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 1.20/0.51    inference(ennf_transformation,[],[f12])).
% 1.20/0.51  fof(f12,plain,(
% 1.20/0.51    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X3,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 1.20/0.51    inference(rectify,[],[f7])).
% 1.20/0.51  fof(f7,axiom,(
% 1.20/0.51    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X1,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 1.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_pre_topc)).
% 1.20/0.51  fof(f93,plain,(
% 1.20/0.51    ~spl6_3),
% 1.20/0.51    inference(avatar_split_clause,[],[f43,f90])).
% 1.20/0.51  fof(f43,plain,(
% 1.20/0.51    u1_struct_0(sK2) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK2)))),
% 1.20/0.51    inference(cnf_transformation,[],[f29])).
% 1.20/0.51  fof(f29,plain,(
% 1.20/0.51    u1_struct_0(sK2) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK2))) & l1_pre_topc(sK2) & v2_pre_topc(sK2)),
% 1.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f15,f28])).
% 1.20/0.51  fof(f28,plain,(
% 1.20/0.51    ? [X0] : (u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (u1_struct_0(sK2) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK2))) & l1_pre_topc(sK2) & v2_pre_topc(sK2))),
% 1.20/0.51    introduced(choice_axiom,[])).
% 1.20/0.51  fof(f15,plain,(
% 1.20/0.51    ? [X0] : (u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.20/0.51    inference(flattening,[],[f14])).
% 1.20/0.51  fof(f14,plain,(
% 1.20/0.51    ? [X0] : (u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 1.20/0.51    inference(ennf_transformation,[],[f13])).
% 1.20/0.51  fof(f13,plain,(
% 1.20/0.51    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))))),
% 1.20/0.51    inference(pure_predicate_removal,[],[f11])).
% 1.20/0.51  fof(f11,negated_conjecture,(
% 1.20/0.51    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))))),
% 1.20/0.51    inference(negated_conjecture,[],[f10])).
% 1.20/0.51  fof(f10,conjecture,(
% 1.20/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))))),
% 1.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_yellow_1)).
% 1.20/0.51  fof(f87,plain,(
% 1.20/0.51    spl6_2),
% 1.20/0.51    inference(avatar_split_clause,[],[f42,f84])).
% 1.20/0.51  fof(f42,plain,(
% 1.20/0.51    l1_pre_topc(sK2)),
% 1.20/0.51    inference(cnf_transformation,[],[f29])).
% 1.20/0.51  fof(f82,plain,(
% 1.20/0.51    spl6_1),
% 1.20/0.51    inference(avatar_split_clause,[],[f41,f79])).
% 1.20/0.51  fof(f41,plain,(
% 1.20/0.51    v2_pre_topc(sK2)),
% 1.20/0.51    inference(cnf_transformation,[],[f29])).
% 1.20/0.51  % SZS output end Proof for theBenchmark
% 1.20/0.51  % (24035)------------------------------
% 1.20/0.51  % (24035)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.20/0.51  % (24035)Termination reason: Refutation
% 1.20/0.51  
% 1.20/0.51  % (24035)Memory used [KB]: 10746
% 1.20/0.51  % (24035)Time elapsed: 0.101 s
% 1.20/0.51  % (24035)------------------------------
% 1.20/0.51  % (24035)------------------------------
% 1.20/0.51  % (24030)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.20/0.51  % (24022)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.20/0.51  % (24025)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.20/0.51  % (24017)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.20/0.52  % (24011)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.20/0.52  % (24010)Success in time 0.157 s
%------------------------------------------------------------------------------
