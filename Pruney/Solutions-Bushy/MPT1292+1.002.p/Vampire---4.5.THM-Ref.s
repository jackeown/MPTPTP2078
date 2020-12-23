%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1292+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:39 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 218 expanded)
%              Number of leaves         :   32 (  94 expanded)
%              Depth                    :   12
%              Number of atoms          :  327 ( 753 expanded)
%              Number of equality atoms :   44 ( 112 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f354,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f70,f74,f78,f82,f86,f90,f95,f100,f116,f122,f135,f141,f147,f234,f313,f327,f353])).

fof(f353,plain,
    ( spl6_5
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_27 ),
    inference(avatar_split_clause,[],[f336,f319,f88,f80,f84])).

fof(f84,plain,
    ( spl6_5
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f80,plain,
    ( spl6_4
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f88,plain,
    ( spl6_6
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f319,plain,
    ( spl6_27
  <=> k1_xboole_0 = u1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f336,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_27 ),
    inference(superposition,[],[f48,f320])).

fof(f320,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | ~ spl6_27 ),
    inference(avatar_component_clause,[],[f319])).

fof(f48,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f327,plain,
    ( ~ spl6_8
    | spl6_27
    | ~ spl6_14
    | ~ spl6_26 ),
    inference(avatar_split_clause,[],[f326,f309,f145,f319,f98])).

fof(f98,plain,
    ( spl6_8
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f145,plain,
    ( spl6_14
  <=> k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f309,plain,
    ( spl6_26
  <=> u1_struct_0(sK0) = k5_setfam_1(u1_struct_0(sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f326,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl6_14
    | ~ spl6_26 ),
    inference(forward_demodulation,[],[f316,f146])).

fof(f146,plain,
    ( k1_xboole_0 = k3_tarski(k1_xboole_0)
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f145])).

fof(f316,plain,
    ( u1_struct_0(sK0) = k3_tarski(k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl6_26 ),
    inference(superposition,[],[f52,f310])).

fof(f310,plain,
    ( u1_struct_0(sK0) = k5_setfam_1(u1_struct_0(sK0),k1_xboole_0)
    | ~ spl6_26 ),
    inference(avatar_component_clause,[],[f309])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k5_setfam_1(X0,X1) = k3_tarski(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k5_setfam_1(X0,X1) = k3_tarski(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k5_setfam_1(X0,X1) = k3_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

fof(f313,plain,
    ( ~ spl6_8
    | spl6_26
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f305,f93,f309,f98])).

fof(f93,plain,
    ( spl6_7
  <=> m1_setfam_1(k1_xboole_0,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f305,plain,
    ( u1_struct_0(sK0) = k5_setfam_1(u1_struct_0(sK0),k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl6_7 ),
    inference(resolution,[],[f54,f94])).

fof(f94,plain,
    ( m1_setfam_1(k1_xboole_0,u1_struct_0(sK0))
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f93])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ m1_setfam_1(X1,X0)
      | k5_setfam_1(X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ( m1_setfam_1(X1,X0)
          | k5_setfam_1(X0,X1) != X0 )
        & ( k5_setfam_1(X0,X1) = X0
          | ~ m1_setfam_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( m1_setfam_1(X1,X0)
      <=> k5_setfam_1(X0,X1) = X0 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( m1_setfam_1(X1,X0)
      <=> k5_setfam_1(X0,X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_setfam_1)).

fof(f234,plain,(
    ~ spl6_9 ),
    inference(avatar_contradiction_clause,[],[f232])).

fof(f232,plain,
    ( $false
    | ~ spl6_9 ),
    inference(resolution,[],[f112,f49])).

fof(f49,plain,(
    ! [X0] : m1_subset_1(sK2(X0),X0) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] : m1_subset_1(sK2(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f4,f32])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f4,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f112,plain,
    ( ! [X0] : ~ m1_subset_1(X0,k3_tarski(sK2(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl6_9
  <=> ! [X0] : ~ m1_subset_1(X0,k3_tarski(sK2(k1_zfmisc_1(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f147,plain,
    ( spl6_14
    | ~ spl6_13 ),
    inference(avatar_split_clause,[],[f143,f133,f145])).

fof(f133,plain,
    ( spl6_13
  <=> v1_xboole_0(k3_tarski(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f143,plain,
    ( k1_xboole_0 = k3_tarski(k1_xboole_0)
    | ~ spl6_13 ),
    inference(resolution,[],[f134,f47])).

fof(f47,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

fof(f134,plain,
    ( v1_xboole_0(k3_tarski(k1_xboole_0))
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f133])).

fof(f141,plain,(
    ~ spl6_12 ),
    inference(avatar_contradiction_clause,[],[f139])).

fof(f139,plain,
    ( $false
    | ~ spl6_12 ),
    inference(resolution,[],[f131,f49])).

fof(f131,plain,
    ( ! [X0] : ~ m1_subset_1(X0,k3_tarski(k1_xboole_0))
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f130])).

fof(f130,plain,
    ( spl6_12
  <=> ! [X0] : ~ m1_subset_1(X0,k3_tarski(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f135,plain,
    ( spl6_12
    | spl6_13
    | ~ spl6_6
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f127,f120,f88,f133,f130])).

fof(f120,plain,
    ( spl6_11
  <=> k1_xboole_0 = k3_tarski(sK2(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f127,plain,
    ( ! [X0] :
        ( v1_xboole_0(k3_tarski(k1_xboole_0))
        | ~ m1_subset_1(X0,k3_tarski(k1_xboole_0)) )
    | ~ spl6_6
    | ~ spl6_11 ),
    inference(resolution,[],[f126,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f126,plain,
    ( ! [X1] : ~ r2_hidden(X1,k3_tarski(k1_xboole_0))
    | ~ spl6_6
    | ~ spl6_11 ),
    inference(resolution,[],[f124,f65])).

fof(f65,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK5(X0,X5),X0)
      | ~ r2_hidden(X5,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK5(X0,X5),X0)
      | ~ r2_hidden(X5,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(sK3(X0,X1),X3) )
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( ( r2_hidden(sK4(X0,X1),X0)
              & r2_hidden(sK3(X0,X1),sK4(X0,X1)) )
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ( r2_hidden(sK5(X0,X5),X0)
                & r2_hidden(X5,sK5(X0,X5)) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f36,f39,f38,f37])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X3) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( r2_hidden(X4,X0)
                & r2_hidden(X2,X4) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( ~ r2_hidden(X3,X0)
              | ~ r2_hidden(sK3(X0,X1),X3) )
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( ? [X4] :
              ( r2_hidden(X4,X0)
              & r2_hidden(sK3(X0,X1),X4) )
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X0)
          & r2_hidden(sK3(X0,X1),X4) )
     => ( r2_hidden(sK4(X0,X1),X0)
        & r2_hidden(sK3(X0,X1),sK4(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( r2_hidden(X7,X0)
          & r2_hidden(X5,X7) )
     => ( r2_hidden(sK5(X0,X5),X0)
        & r2_hidden(X5,sK5(X0,X5)) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] :
                  ( r2_hidden(X4,X0)
                  & r2_hidden(X2,X4) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ? [X7] :
                  ( r2_hidden(X7,X0)
                  & r2_hidden(X5,X7) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] :
                  ( r2_hidden(X3,X0)
                  & r2_hidden(X2,X3) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) ) )
            & ( ? [X3] :
                  ( r2_hidden(X3,X0)
                  & r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).

fof(f124,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl6_6
    | ~ spl6_11 ),
    inference(superposition,[],[f106,f121])).

fof(f121,plain,
    ( k1_xboole_0 = k3_tarski(sK2(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f120])).

fof(f106,plain,
    ( ! [X0] : ~ r2_hidden(X0,k3_tarski(sK2(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl6_6 ),
    inference(resolution,[],[f104,f49])).

fof(f104,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
        | ~ r2_hidden(X0,k3_tarski(X1)) )
    | ~ spl6_6 ),
    inference(resolution,[],[f65,f102])).

fof(f102,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) )
    | ~ spl6_6 ),
    inference(resolution,[],[f63,f89])).

fof(f89,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f88])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f122,plain,
    ( spl6_11
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f118,f114,f120])).

fof(f114,plain,
    ( spl6_10
  <=> v1_xboole_0(k3_tarski(sK2(k1_zfmisc_1(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f118,plain,
    ( k1_xboole_0 = k3_tarski(sK2(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl6_10 ),
    inference(resolution,[],[f115,f47])).

fof(f115,plain,
    ( v1_xboole_0(k3_tarski(sK2(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f114])).

fof(f116,plain,
    ( spl6_9
    | spl6_10
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f108,f88,f114,f111])).

fof(f108,plain,
    ( ! [X0] :
        ( v1_xboole_0(k3_tarski(sK2(k1_zfmisc_1(k1_xboole_0))))
        | ~ m1_subset_1(X0,k3_tarski(sK2(k1_zfmisc_1(k1_xboole_0)))) )
    | ~ spl6_6 ),
    inference(resolution,[],[f106,f51])).

fof(f100,plain,
    ( spl6_8
    | ~ spl6_1
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f96,f76,f68,f98])).

fof(f68,plain,
    ( spl6_1
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f76,plain,
    ( spl6_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f96,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl6_1
    | ~ spl6_3 ),
    inference(superposition,[],[f77,f69])).

fof(f69,plain,
    ( k1_xboole_0 = sK1
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f68])).

fof(f77,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f76])).

fof(f95,plain,
    ( spl6_7
    | ~ spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f91,f72,f68,f93])).

fof(f72,plain,
    ( spl6_2
  <=> m1_setfam_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f91,plain,
    ( m1_setfam_1(k1_xboole_0,u1_struct_0(sK0))
    | ~ spl6_1
    | ~ spl6_2 ),
    inference(superposition,[],[f73,f69])).

fof(f73,plain,
    ( m1_setfam_1(sK1,u1_struct_0(sK0))
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f72])).

fof(f90,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f46,f88])).

fof(f46,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f86,plain,(
    ~ spl6_5 ),
    inference(avatar_split_clause,[],[f41,f84])).

fof(f41,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( k1_xboole_0 = sK1
    & m1_setfam_1(sK1,u1_struct_0(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & l1_struct_0(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f30,f29])).

fof(f29,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k1_xboole_0 = X1
            & m1_setfam_1(X1,u1_struct_0(X0))
            & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( k1_xboole_0 = X1
          & m1_setfam_1(X1,u1_struct_0(sK0))
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
      & l1_struct_0(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X1] :
        ( k1_xboole_0 = X1
        & m1_setfam_1(X1,u1_struct_0(sK0))
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
   => ( k1_xboole_0 = sK1
      & m1_setfam_1(sK1,u1_struct_0(sK0))
      & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 = X1
          & m1_setfam_1(X1,u1_struct_0(X0))
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 = X1
          & m1_setfam_1(X1,u1_struct_0(X0))
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ~ ( k1_xboole_0 = X1
                & m1_setfam_1(X1,u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ~ ( k1_xboole_0 = X1
              & m1_setfam_1(X1,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_tops_2)).

fof(f82,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f42,f80])).

fof(f42,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f78,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f43,f76])).

fof(f43,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f31])).

fof(f74,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f44,f72])).

fof(f44,plain,(
    m1_setfam_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f31])).

fof(f70,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f45,f68])).

fof(f45,plain,(
    k1_xboole_0 = sK1 ),
    inference(cnf_transformation,[],[f31])).

%------------------------------------------------------------------------------
