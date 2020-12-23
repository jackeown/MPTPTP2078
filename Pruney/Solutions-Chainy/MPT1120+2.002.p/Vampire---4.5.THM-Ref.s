%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:15 EST 2020

% Result     : Theorem 8.38s
% Output     : Refutation 8.38s
% Verified   : 
% Statistics : Number of formulae       :  249 ( 642 expanded)
%              Number of leaves         :   55 ( 207 expanded)
%              Depth                    :   15
%              Number of atoms          :  621 (1599 expanded)
%              Number of equality atoms :   84 ( 311 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14408,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f136,f141,f146,f158,f177,f213,f260,f321,f330,f403,f429,f434,f449,f651,f723,f1034,f1764,f2050,f2964,f3078,f13612,f14027,f14307,f14319,f14407])).

fof(f14407,plain,
    ( ~ spl5_1
    | ~ spl5_3
    | ~ spl5_94
    | ~ spl5_264
    | spl5_291 ),
    inference(avatar_contradiction_clause,[],[f14406])).

fof(f14406,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_3
    | ~ spl5_94
    | ~ spl5_264
    | spl5_291 ),
    inference(subsumption_resolution,[],[f14405,f135])).

fof(f135,plain,
    ( l1_pre_topc(sK0)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f133])).

fof(f133,plain,
    ( spl5_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f14405,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl5_3
    | ~ spl5_94
    | ~ spl5_264
    | spl5_291 ),
    inference(subsumption_resolution,[],[f14404,f13611])).

fof(f13611,plain,
    ( ! [X25] : m1_subset_1(k3_xboole_0(sK1,X25),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_264 ),
    inference(avatar_component_clause,[],[f13610])).

fof(f13610,plain,
    ( spl5_264
  <=> ! [X25] : m1_subset_1(k3_xboole_0(sK1,X25),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_264])])).

fof(f14404,plain,
    ( ~ m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl5_3
    | ~ spl5_94
    | spl5_291 ),
    inference(subsumption_resolution,[],[f14403,f145])).

fof(f145,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f143])).

fof(f143,plain,
    ( spl5_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f14403,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl5_94
    | spl5_291 ),
    inference(subsumption_resolution,[],[f14401,f2049])).

fof(f2049,plain,
    ( ! [X6,X5] : r1_tarski(k3_xboole_0(X5,X6),X6)
    | ~ spl5_94 ),
    inference(avatar_component_clause,[],[f2048])).

fof(f2048,plain,
    ( spl5_94
  <=> ! [X5,X6] : r1_tarski(k3_xboole_0(X5,X6),X6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_94])])).

fof(f14401,plain,
    ( ~ r1_tarski(k3_xboole_0(sK1,sK2),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl5_291 ),
    inference(resolution,[],[f14306,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_pre_topc)).

fof(f14306,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),k2_pre_topc(sK0,sK2))
    | spl5_291 ),
    inference(avatar_component_clause,[],[f14304])).

fof(f14304,plain,
    ( spl5_291
  <=> r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),k2_pre_topc(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_291])])).

fof(f14319,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | ~ spl5_264
    | spl5_290 ),
    inference(avatar_contradiction_clause,[],[f14318])).

fof(f14318,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_264
    | spl5_290 ),
    inference(subsumption_resolution,[],[f14317,f135])).

fof(f14317,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl5_2
    | ~ spl5_264
    | spl5_290 ),
    inference(subsumption_resolution,[],[f14316,f13611])).

fof(f14316,plain,
    ( ~ m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl5_2
    | spl5_290 ),
    inference(subsumption_resolution,[],[f14315,f140])).

fof(f140,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f138])).

fof(f138,plain,
    ( spl5_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f14315,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl5_290 ),
    inference(subsumption_resolution,[],[f14313,f87])).

fof(f87,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f14313,plain,
    ( ~ r1_tarski(k3_xboole_0(sK1,sK2),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl5_290 ),
    inference(resolution,[],[f14302,f84])).

fof(f14302,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),k2_pre_topc(sK0,sK1))
    | spl5_290 ),
    inference(avatar_component_clause,[],[f14300])).

fof(f14300,plain,
    ( spl5_290
  <=> r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_290])])).

fof(f14307,plain,
    ( ~ spl5_290
    | ~ spl5_291
    | spl5_286 ),
    inference(avatar_split_clause,[],[f14133,f14024,f14304,f14300])).

fof(f14024,plain,
    ( spl5_286
  <=> r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_286])])).

fof(f14133,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),k2_pre_topc(sK0,sK2))
    | ~ r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),k2_pre_topc(sK0,sK1))
    | spl5_286 ),
    inference(resolution,[],[f14026,f119])).

fof(f119,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

fof(f14026,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)))
    | spl5_286 ),
    inference(avatar_component_clause,[],[f14024])).

fof(f14027,plain,
    ( ~ spl5_286
    | spl5_25
    | ~ spl5_43 ),
    inference(avatar_split_clause,[],[f13919,f720,f431,f14024])).

fof(f431,plain,
    ( spl5_25
  <=> r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f720,plain,
    ( spl5_43
  <=> m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_43])])).

fof(f13919,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)))
    | spl5_25
    | ~ spl5_43 ),
    inference(backward_demodulation,[],[f433,f800])).

fof(f800,plain,
    ( ! [X0] : k3_xboole_0(X0,k2_pre_topc(sK0,sK2)) = k9_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,sK2))
    | ~ spl5_43 ),
    inference(resolution,[],[f722,f113])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f722,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_43 ),
    inference(avatar_component_clause,[],[f720])).

fof(f433,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)))
    | spl5_25 ),
    inference(avatar_component_clause,[],[f431])).

fof(f13612,plain,
    ( spl5_264
    | ~ spl5_119 ),
    inference(avatar_split_clause,[],[f13590,f3075,f13610])).

fof(f3075,plain,
    ( spl5_119
  <=> sK1 = k3_xboole_0(u1_struct_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_119])])).

fof(f13590,plain,
    ( ! [X25] : m1_subset_1(k3_xboole_0(sK1,X25),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_119 ),
    inference(superposition,[],[f12275,f3077])).

fof(f3077,plain,
    ( sK1 = k3_xboole_0(u1_struct_0(sK0),sK1)
    | ~ spl5_119 ),
    inference(avatar_component_clause,[],[f3075])).

fof(f12275,plain,(
    ! [X6,X7,X5] : m1_subset_1(k3_xboole_0(k3_xboole_0(X5,X6),X7),k1_zfmisc_1(X5)) ),
    inference(resolution,[],[f7011,f87])).

fof(f7011,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(X2,k3_xboole_0(X3,X4))
      | m1_subset_1(X2,k1_zfmisc_1(X3)) ) ),
    inference(resolution,[],[f1510,f87])).

fof(f1510,plain,(
    ! [X10,X11,X9] :
      ( ~ r1_tarski(X10,X11)
      | m1_subset_1(X9,k1_zfmisc_1(X11))
      | ~ r1_tarski(X9,X10) ) ),
    inference(resolution,[],[f584,f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_zfmisc_1)).

fof(f584,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k1_zfmisc_1(X2),X1)
      | ~ r1_tarski(X0,X2)
      | m1_subset_1(X0,X1) ) ),
    inference(resolution,[],[f235,f110])).

fof(f110,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f235,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
      | m1_subset_1(X2,X1)
      | ~ r1_tarski(X2,X0) ) ),
    inference(resolution,[],[f118,f128])).

fof(f128,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f106])).

fof(f106,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK3(X0,X1),X0)
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( r1_tarski(sK3(X0,X1),X0)
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f74,f75])).

fof(f75,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK3(X0,X1),X0)
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( r1_tarski(sK3(X0,X1),X0)
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f3078,plain,
    ( spl5_119
    | ~ spl5_4
    | ~ spl5_118 ),
    inference(avatar_split_clause,[],[f3069,f2962,f155,f3075])).

fof(f155,plain,
    ( spl5_4
  <=> r1_tarski(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f2962,plain,
    ( spl5_118
  <=> ! [X1,X0] :
        ( ~ r1_tarski(X0,X1)
        | k3_xboole_0(X1,X0) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_118])])).

fof(f3069,plain,
    ( sK1 = k3_xboole_0(u1_struct_0(sK0),sK1)
    | ~ spl5_4
    | ~ spl5_118 ),
    inference(resolution,[],[f2963,f157])).

fof(f157,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f155])).

fof(f2963,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k3_xboole_0(X1,X0) = X0 )
    | ~ spl5_118 ),
    inference(avatar_component_clause,[],[f2962])).

fof(f2964,plain,
    ( spl5_118
    | ~ spl5_94 ),
    inference(avatar_split_clause,[],[f2069,f2048,f2962])).

fof(f2069,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k3_xboole_0(X1,X0) = X0 )
    | ~ spl5_94 ),
    inference(subsumption_resolution,[],[f2051,f126])).

fof(f126,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f71])).

fof(f71,plain,(
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

fof(f2051,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | ~ r1_tarski(X0,X0)
        | k3_xboole_0(X1,X0) = X0 )
    | ~ spl5_94 ),
    inference(resolution,[],[f2049,f261])).

fof(f261,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k3_xboole_0(X2,X1),X0)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1)
      | k3_xboole_0(X2,X1) = X0 ) ),
    inference(resolution,[],[f119,f104])).

fof(f104,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f72])).

fof(f2050,plain,
    ( spl5_94
    | ~ spl5_88 ),
    inference(avatar_split_clause,[],[f2013,f1762,f2048])).

fof(f1762,plain,
    ( spl5_88
  <=> ! [X5,X6] : r1_tarski(k2_subset_1(k3_xboole_0(X5,X6)),X6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_88])])).

fof(f2013,plain,
    ( ! [X6,X5] : r1_tarski(k3_xboole_0(X5,X6),X6)
    | ~ spl5_88 ),
    inference(backward_demodulation,[],[f1763,f1968])).

fof(f1968,plain,(
    ! [X5] : k2_subset_1(X5) = X5 ),
    inference(subsumption_resolution,[],[f1954,f1659])).

fof(f1659,plain,(
    ! [X2] : r1_tarski(k2_subset_1(X2),X2) ),
    inference(backward_demodulation,[],[f930,f1653])).

fof(f1653,plain,(
    ! [X0] : k2_subset_1(X0) = k2_xboole_0(k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f1622,f926])).

fof(f926,plain,(
    ! [X2] : k2_subset_1(X2) = k4_subset_1(X2,k1_xboole_0,X2) ),
    inference(backward_demodulation,[],[f522,f923])).

fof(f923,plain,(
    ! [X2] : k4_xboole_0(X2,k1_xboole_0) = X2 ),
    inference(backward_demodulation,[],[f245,f921])).

fof(f921,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f562,f560])).

fof(f560,plain,(
    ! [X0] : k1_xboole_0 = k3_subset_1(X0,X0) ),
    inference(forward_demodulation,[],[f543,f270])).

fof(f270,plain,(
    ! [X2] : k1_xboole_0 = k4_xboole_0(X2,X2) ),
    inference(resolution,[],[f227,f85])).

fof(f85,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f227,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X0),X1) ),
    inference(resolution,[],[f114,f86])).

fof(f86,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
      | r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f543,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k3_subset_1(X0,X0) ),
    inference(resolution,[],[f244,f126])).

fof(f244,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(resolution,[],[f96,f110])).

fof(f96,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f562,plain,(
    ! [X0] : k3_subset_1(X0,k3_subset_1(X0,X0)) = X0 ),
    inference(resolution,[],[f249,f126])).

fof(f249,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(resolution,[],[f97,f110])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f245,plain,(
    ! [X2] : k4_xboole_0(X2,k1_xboole_0) = k3_subset_1(X2,k1_xboole_0) ),
    inference(resolution,[],[f96,f83])).

fof(f83,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f522,plain,(
    ! [X2] : k2_subset_1(X2) = k4_subset_1(X2,k1_xboole_0,k4_xboole_0(X2,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f281,f245])).

fof(f281,plain,(
    ! [X2] : k4_subset_1(X2,k1_xboole_0,k3_subset_1(X2,k1_xboole_0)) = k2_subset_1(X2) ),
    inference(resolution,[],[f98,f83])).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = k2_subset_1(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = k2_subset_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = k2_subset_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).

fof(f1622,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = k4_subset_1(X0,k1_xboole_0,X0) ),
    inference(resolution,[],[f708,f126])).

fof(f708,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(k1_xboole_0,X0) = k4_subset_1(X1,k1_xboole_0,X0) ) ),
    inference(resolution,[],[f312,f110])).

fof(f312,plain,(
    ! [X4,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(X4))
      | k2_xboole_0(k1_xboole_0,X3) = k4_subset_1(X4,k1_xboole_0,X3) ) ),
    inference(resolution,[],[f120,f83])).

fof(f120,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f930,plain,(
    ! [X2] : r1_tarski(k2_xboole_0(k1_xboole_0,X2),X2) ),
    inference(superposition,[],[f228,f923])).

fof(f228,plain,(
    ! [X2,X3] : r1_tarski(k4_xboole_0(k2_xboole_0(X2,X3),X2),X3) ),
    inference(resolution,[],[f114,f126])).

fof(f1954,plain,(
    ! [X5] :
      ( ~ r1_tarski(k2_subset_1(X5),X5)
      | k2_subset_1(X5) = X5 ) ),
    inference(superposition,[],[f193,f1920])).

fof(f1920,plain,(
    ! [X0] : k2_subset_1(X0) = k2_xboole_0(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f1890,f699])).

fof(f699,plain,(
    ! [X0] : k2_subset_1(X0) = k4_subset_1(X0,X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f681,f560])).

fof(f681,plain,(
    ! [X0] : k2_subset_1(X0) = k4_subset_1(X0,X0,k3_subset_1(X0,X0)) ),
    inference(resolution,[],[f280,f126])).

fof(f280,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = k2_subset_1(X0) ) ),
    inference(resolution,[],[f98,f110])).

fof(f1890,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = k4_subset_1(X0,X0,k1_xboole_0) ),
    inference(resolution,[],[f805,f126])).

fof(f805,plain,(
    ! [X4,X3] :
      ( ~ r1_tarski(X3,X4)
      | k2_xboole_0(X3,k1_xboole_0) = k4_subset_1(X4,X3,k1_xboole_0) ) ),
    inference(resolution,[],[f311,f83])).

fof(f311,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | k2_xboole_0(X2,X0) = k4_subset_1(X1,X2,X0)
      | ~ r1_tarski(X2,X1) ) ),
    inference(resolution,[],[f120,f110])).

fof(f193,plain,(
    ! [X4,X5] :
      ( ~ r1_tarski(k2_xboole_0(X4,X5),X4)
      | k2_xboole_0(X4,X5) = X4 ) ),
    inference(resolution,[],[f104,f86])).

fof(f1763,plain,
    ( ! [X6,X5] : r1_tarski(k2_subset_1(k3_xboole_0(X5,X6)),X6)
    | ~ spl5_88 ),
    inference(avatar_component_clause,[],[f1762])).

fof(f1764,plain,
    ( spl5_88
    | ~ spl5_50 ),
    inference(avatar_split_clause,[],[f1661,f1032,f1762])).

fof(f1032,plain,
    ( spl5_50
  <=> ! [X5,X6] : r1_tarski(k2_xboole_0(k1_xboole_0,k3_xboole_0(X5,X6)),X6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_50])])).

fof(f1661,plain,
    ( ! [X6,X5] : r1_tarski(k2_subset_1(k3_xboole_0(X5,X6)),X6)
    | ~ spl5_50 ),
    inference(backward_demodulation,[],[f1033,f1653])).

fof(f1033,plain,
    ( ! [X6,X5] : r1_tarski(k2_xboole_0(k1_xboole_0,k3_xboole_0(X5,X6)),X6)
    | ~ spl5_50 ),
    inference(avatar_component_clause,[],[f1032])).

fof(f1034,plain,
    ( spl5_50
    | ~ spl5_26 ),
    inference(avatar_split_clause,[],[f934,f442,f1032])).

fof(f442,plain,
    ( spl5_26
  <=> ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f934,plain,
    ( ! [X6,X5] : r1_tarski(k2_xboole_0(k1_xboole_0,k3_xboole_0(X5,X6)),X6)
    | ~ spl5_26 ),
    inference(forward_demodulation,[],[f933,f443])).

fof(f443,plain,
    ( ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)
    | ~ spl5_26 ),
    inference(avatar_component_clause,[],[f442])).

fof(f933,plain,(
    ! [X6,X5] : r1_tarski(k2_xboole_0(k3_xboole_0(X5,k1_xboole_0),k3_xboole_0(X5,X6)),X6) ),
    inference(superposition,[],[f254,f923])).

fof(f254,plain,(
    ! [X2,X0,X1] : r1_tarski(k4_xboole_0(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),X1),X2) ),
    inference(resolution,[],[f111,f114])).

fof(f111,plain,(
    ! [X2,X0,X1] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_xboole_1)).

fof(f723,plain,
    ( spl5_43
    | ~ spl5_3
    | ~ spl5_37 ),
    inference(avatar_split_clause,[],[f674,f649,f143,f720])).

fof(f649,plain,
    ( spl5_37
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).

fof(f674,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_3
    | ~ spl5_37 ),
    inference(resolution,[],[f650,f145])).

fof(f650,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_37 ),
    inference(avatar_component_clause,[],[f649])).

fof(f651,plain,
    ( spl5_37
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f295,f133,f649])).

fof(f295,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_1 ),
    inference(resolution,[],[f101,f135])).

fof(f101,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f449,plain,
    ( spl5_26
    | ~ spl5_23 ),
    inference(avatar_split_clause,[],[f438,f421,f442])).

fof(f421,plain,
    ( spl5_23
  <=> ! [X1] : r1_tarski(k3_xboole_0(X1,k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f438,plain,
    ( ! [X1] : k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0)
    | ~ spl5_23 ),
    inference(subsumption_resolution,[],[f436,f82])).

fof(f82,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f436,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k1_xboole_0,k3_xboole_0(X1,k1_xboole_0))
        | k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0) )
    | ~ spl5_23 ),
    inference(resolution,[],[f422,f104])).

fof(f422,plain,
    ( ! [X1] : r1_tarski(k3_xboole_0(X1,k1_xboole_0),k1_xboole_0)
    | ~ spl5_23 ),
    inference(avatar_component_clause,[],[f421])).

fof(f434,plain,
    ( ~ spl5_25
    | ~ spl5_3
    | spl5_11 ),
    inference(avatar_split_clause,[],[f424,f318,f143,f431])).

fof(f318,plain,
    ( spl5_11
  <=> r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f424,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)))
    | ~ spl5_3
    | spl5_11 ),
    inference(backward_demodulation,[],[f320,f268])).

fof(f268,plain,
    ( ! [X6] : k3_xboole_0(X6,sK2) = k9_subset_1(u1_struct_0(sK0),X6,sK2)
    | ~ spl5_3 ),
    inference(resolution,[],[f113,f145])).

fof(f320,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)))
    | spl5_11 ),
    inference(avatar_component_clause,[],[f318])).

fof(f429,plain,
    ( spl5_23
    | ~ spl5_6
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f415,f339,f174,f421])).

fof(f174,plain,
    ( spl5_6
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f339,plain,
    ( spl5_13
  <=> ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f415,plain,
    ( ! [X3] : r1_tarski(k3_xboole_0(X3,k1_xboole_0),k1_xboole_0)
    | ~ spl5_6
    | ~ spl5_13 ),
    inference(forward_demodulation,[],[f414,f340])).

fof(f340,plain,
    ( ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f339])).

fof(f414,plain,
    ( ! [X4,X3] : r1_tarski(k3_xboole_0(X3,k10_relat_1(k1_xboole_0,X4)),k1_xboole_0)
    | ~ spl5_6
    | ~ spl5_13 ),
    inference(subsumption_resolution,[],[f411,f176])).

fof(f176,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f174])).

fof(f411,plain,
    ( ! [X4,X3] :
        ( r1_tarski(k3_xboole_0(X3,k10_relat_1(k1_xboole_0,X4)),k1_xboole_0)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl5_13 ),
    inference(superposition,[],[f112,f340])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_xboole_0(X0,k10_relat_1(X2,X1)),k10_relat_1(X2,k3_xboole_0(k9_relat_1(X2,X0),X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k3_xboole_0(X0,k10_relat_1(X2,X1)),k10_relat_1(X2,k3_xboole_0(k9_relat_1(X2,X0),X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k3_xboole_0(X0,k10_relat_1(X2,X1)),k10_relat_1(X2,k3_xboole_0(k9_relat_1(X2,X0),X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_funct_1)).

fof(f403,plain,
    ( spl5_13
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f335,f328,f339])).

fof(f328,plain,
    ( spl5_12
  <=> ! [X0] : r1_tarski(k10_relat_1(k1_xboole_0,X0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f335,plain,
    ( ! [X1] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X1)
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f334,f82])).

fof(f334,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k1_xboole_0,k10_relat_1(k1_xboole_0,X1))
        | k1_xboole_0 = k10_relat_1(k1_xboole_0,X1) )
    | ~ spl5_12 ),
    inference(resolution,[],[f329,f104])).

fof(f329,plain,
    ( ! [X0] : r1_tarski(k10_relat_1(k1_xboole_0,X0),k1_xboole_0)
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f328])).

fof(f330,plain,
    ( spl5_12
    | ~ spl5_6
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f264,f240,f174,f328])).

fof(f240,plain,
    ( spl5_10
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f264,plain,
    ( ! [X0] : r1_tarski(k10_relat_1(k1_xboole_0,X0),k1_xboole_0)
    | ~ spl5_6
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f263,f176])).

fof(f263,plain,
    ( ! [X0] :
        ( r1_tarski(k10_relat_1(k1_xboole_0,X0),k1_xboole_0)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl5_10 ),
    inference(superposition,[],[f89,f242])).

fof(f242,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f240])).

fof(f89,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

fof(f321,plain,(
    ~ spl5_11 ),
    inference(avatar_split_clause,[],[f81,f318])).

fof(f81,plain,(
    ~ r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f34,f66,f65,f64])).

fof(f64,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)))
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X1,X2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X1,X2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X2)))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ~ r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,X2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,X2)))
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,X2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,X2)))
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)))
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))) ) ) ) ),
    inference(negated_conjecture,[],[f32])).

fof(f32,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_pre_topc)).

fof(f260,plain,
    ( spl5_10
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f221,f211,f240])).

fof(f211,plain,
    ( spl5_8
  <=> ! [X0] : r1_tarski(k1_relat_1(k1_xboole_0),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f221,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl5_8 ),
    inference(resolution,[],[f123,f212])).

fof(f212,plain,
    ( ! [X0] : r1_tarski(k1_relat_1(k1_xboole_0),X0)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f211])).

fof(f123,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k3_zfmisc_1(X2,X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ( ~ r1_tarski(X0,k3_zfmisc_1(X2,X0,X1))
        & ~ r1_tarski(X0,k3_zfmisc_1(X1,X2,X0))
        & ~ r1_tarski(X0,k3_zfmisc_1(X0,X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( ~ r1_tarski(X0,k3_zfmisc_1(X2,X0,X1))
          & ~ r1_tarski(X0,k3_zfmisc_1(X1,X2,X0))
          & ~ r1_tarski(X0,k3_zfmisc_1(X0,X1,X2)) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_mcart_1)).

fof(f213,plain,
    ( spl5_8
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f206,f174,f211])).

fof(f206,plain,
    ( ! [X0] : r1_tarski(k1_relat_1(k1_xboole_0),X0)
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f205,f176])).

fof(f205,plain,(
    ! [X0] :
      ( r1_tarski(k1_relat_1(k1_xboole_0),X0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[],[f204,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f204,plain,(
    ! [X3] : v4_relat_1(k1_xboole_0,X3) ),
    inference(resolution,[],[f116,f83])).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f177,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f172,f174])).

fof(f172,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f115,f83])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f158,plain,
    ( spl5_4
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f152,f138,f155])).

fof(f152,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl5_2 ),
    inference(resolution,[],[f109,f140])).

fof(f109,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f146,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f80,f143])).

fof(f80,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f67])).

fof(f141,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f79,f138])).

fof(f79,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f67])).

fof(f136,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f78,f133])).

fof(f78,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f67])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n021.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:41:49 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.53  % (21201)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.54  % (21193)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.55  % (21196)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.29/0.56  % (21192)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.29/0.56  % (21192)Refutation not found, incomplete strategy% (21192)------------------------------
% 1.29/0.56  % (21192)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.56  % (21192)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.56  
% 1.29/0.56  % (21192)Memory used [KB]: 10618
% 1.29/0.56  % (21192)Time elapsed: 0.121 s
% 1.29/0.56  % (21192)------------------------------
% 1.29/0.56  % (21192)------------------------------
% 1.29/0.56  % (21189)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 1.66/0.58  % (21206)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.66/0.58  % (21208)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.66/0.58  % (21200)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.66/0.59  % (21187)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.66/0.59  % (21195)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.66/0.59  % (21205)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.66/0.59  % (21210)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.66/0.59  % (21188)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.66/0.60  % (21191)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 1.66/0.60  % (21211)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.66/0.60  % (21194)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.66/0.61  % (21190)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 1.66/0.61  % (21209)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.66/0.61  % (21207)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.66/0.62  % (21186)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.66/0.63  % (21199)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.66/0.64  % (21203)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.66/0.65  % (21202)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.66/0.65  % (21198)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.66/0.65  % (21197)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.66/0.65  % (21204)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 2.88/0.77  % (21195)Refutation not found, incomplete strategy% (21195)------------------------------
% 2.88/0.77  % (21195)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.88/0.77  % (21195)Termination reason: Refutation not found, incomplete strategy
% 2.88/0.77  
% 2.88/0.77  % (21195)Memory used [KB]: 6140
% 2.88/0.77  % (21195)Time elapsed: 0.335 s
% 2.88/0.77  % (21195)------------------------------
% 2.88/0.77  % (21195)------------------------------
% 4.01/0.95  % (21186)Time limit reached!
% 4.01/0.95  % (21186)------------------------------
% 4.01/0.95  % (21186)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.01/0.95  % (21199)Time limit reached!
% 4.01/0.95  % (21199)------------------------------
% 4.01/0.95  % (21199)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.01/0.95  % (21199)Termination reason: Time limit
% 4.01/0.95  % (21199)Termination phase: Saturation
% 4.01/0.95  
% 4.01/0.95  % (21199)Memory used [KB]: 15607
% 4.01/0.95  % (21199)Time elapsed: 0.500 s
% 4.01/0.95  % (21199)------------------------------
% 4.01/0.95  % (21199)------------------------------
% 4.01/0.95  % (21200)Time limit reached!
% 4.01/0.95  % (21200)------------------------------
% 4.01/0.95  % (21200)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.01/0.95  % (21200)Termination reason: Time limit
% 4.01/0.95  
% 4.01/0.95  % (21200)Memory used [KB]: 8059
% 4.01/0.95  % (21200)Time elapsed: 0.522 s
% 4.01/0.95  % (21200)------------------------------
% 4.01/0.95  % (21200)------------------------------
% 4.01/0.96  % (21186)Termination reason: Time limit
% 4.01/0.96  
% 4.01/0.96  % (21186)Memory used [KB]: 14200
% 4.01/0.96  % (21186)Time elapsed: 0.511 s
% 4.01/0.96  % (21186)------------------------------
% 4.01/0.96  % (21186)------------------------------
% 7.66/1.35  % (21194)Time limit reached!
% 7.66/1.35  % (21194)------------------------------
% 7.66/1.35  % (21194)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.66/1.36  % (21194)Termination reason: Time limit
% 7.66/1.36  % (21194)Termination phase: Saturation
% 7.66/1.36  
% 7.66/1.36  % (21194)Memory used [KB]: 6908
% 7.66/1.36  % (21194)Time elapsed: 0.900 s
% 7.66/1.36  % (21194)------------------------------
% 7.66/1.36  % (21194)------------------------------
% 8.38/1.43  % (21188)Refutation found. Thanks to Tanya!
% 8.38/1.43  % SZS status Theorem for theBenchmark
% 8.38/1.43  % SZS output start Proof for theBenchmark
% 8.38/1.43  fof(f14408,plain,(
% 8.38/1.43    $false),
% 8.38/1.43    inference(avatar_sat_refutation,[],[f136,f141,f146,f158,f177,f213,f260,f321,f330,f403,f429,f434,f449,f651,f723,f1034,f1764,f2050,f2964,f3078,f13612,f14027,f14307,f14319,f14407])).
% 8.38/1.43  fof(f14407,plain,(
% 8.38/1.43    ~spl5_1 | ~spl5_3 | ~spl5_94 | ~spl5_264 | spl5_291),
% 8.38/1.43    inference(avatar_contradiction_clause,[],[f14406])).
% 8.38/1.43  fof(f14406,plain,(
% 8.38/1.43    $false | (~spl5_1 | ~spl5_3 | ~spl5_94 | ~spl5_264 | spl5_291)),
% 8.38/1.43    inference(subsumption_resolution,[],[f14405,f135])).
% 8.38/1.43  fof(f135,plain,(
% 8.38/1.43    l1_pre_topc(sK0) | ~spl5_1),
% 8.38/1.43    inference(avatar_component_clause,[],[f133])).
% 8.38/1.43  fof(f133,plain,(
% 8.38/1.43    spl5_1 <=> l1_pre_topc(sK0)),
% 8.38/1.43    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 8.38/1.43  fof(f14405,plain,(
% 8.38/1.43    ~l1_pre_topc(sK0) | (~spl5_3 | ~spl5_94 | ~spl5_264 | spl5_291)),
% 8.38/1.43    inference(subsumption_resolution,[],[f14404,f13611])).
% 8.38/1.43  fof(f13611,plain,(
% 8.38/1.43    ( ! [X25] : (m1_subset_1(k3_xboole_0(sK1,X25),k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl5_264),
% 8.38/1.43    inference(avatar_component_clause,[],[f13610])).
% 8.38/1.43  fof(f13610,plain,(
% 8.38/1.43    spl5_264 <=> ! [X25] : m1_subset_1(k3_xboole_0(sK1,X25),k1_zfmisc_1(u1_struct_0(sK0)))),
% 8.38/1.43    introduced(avatar_definition,[new_symbols(naming,[spl5_264])])).
% 8.38/1.43  fof(f14404,plain,(
% 8.38/1.43    ~m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl5_3 | ~spl5_94 | spl5_291)),
% 8.38/1.43    inference(subsumption_resolution,[],[f14403,f145])).
% 8.38/1.43  fof(f145,plain,(
% 8.38/1.43    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_3),
% 8.38/1.43    inference(avatar_component_clause,[],[f143])).
% 8.38/1.43  fof(f143,plain,(
% 8.38/1.43    spl5_3 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 8.38/1.43    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 8.38/1.43  fof(f14403,plain,(
% 8.38/1.43    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl5_94 | spl5_291)),
% 8.38/1.43    inference(subsumption_resolution,[],[f14401,f2049])).
% 8.38/1.43  fof(f2049,plain,(
% 8.38/1.43    ( ! [X6,X5] : (r1_tarski(k3_xboole_0(X5,X6),X6)) ) | ~spl5_94),
% 8.38/1.43    inference(avatar_component_clause,[],[f2048])).
% 8.38/1.43  fof(f2048,plain,(
% 8.38/1.43    spl5_94 <=> ! [X5,X6] : r1_tarski(k3_xboole_0(X5,X6),X6)),
% 8.38/1.43    introduced(avatar_definition,[new_symbols(naming,[spl5_94])])).
% 8.38/1.43  fof(f14401,plain,(
% 8.38/1.43    ~r1_tarski(k3_xboole_0(sK1,sK2),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl5_291),
% 8.38/1.43    inference(resolution,[],[f14306,f84])).
% 8.38/1.43  fof(f84,plain,(
% 8.38/1.43    ( ! [X2,X0,X1] : (r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 8.38/1.43    inference(cnf_transformation,[],[f36])).
% 8.38/1.43  fof(f36,plain,(
% 8.38/1.43    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 8.38/1.43    inference(flattening,[],[f35])).
% 8.38/1.43  fof(f35,plain,(
% 8.38/1.43    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 8.38/1.43    inference(ennf_transformation,[],[f31])).
% 8.38/1.43  fof(f31,axiom,(
% 8.38/1.43    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))))))),
% 8.38/1.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_pre_topc)).
% 8.38/1.43  fof(f14306,plain,(
% 8.38/1.43    ~r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),k2_pre_topc(sK0,sK2)) | spl5_291),
% 8.38/1.43    inference(avatar_component_clause,[],[f14304])).
% 8.38/1.43  fof(f14304,plain,(
% 8.38/1.43    spl5_291 <=> r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),k2_pre_topc(sK0,sK2))),
% 8.38/1.43    introduced(avatar_definition,[new_symbols(naming,[spl5_291])])).
% 8.38/1.43  fof(f14319,plain,(
% 8.38/1.43    ~spl5_1 | ~spl5_2 | ~spl5_264 | spl5_290),
% 8.38/1.43    inference(avatar_contradiction_clause,[],[f14318])).
% 8.38/1.43  fof(f14318,plain,(
% 8.38/1.43    $false | (~spl5_1 | ~spl5_2 | ~spl5_264 | spl5_290)),
% 8.38/1.43    inference(subsumption_resolution,[],[f14317,f135])).
% 8.38/1.43  fof(f14317,plain,(
% 8.38/1.43    ~l1_pre_topc(sK0) | (~spl5_2 | ~spl5_264 | spl5_290)),
% 8.38/1.43    inference(subsumption_resolution,[],[f14316,f13611])).
% 8.38/1.43  fof(f14316,plain,(
% 8.38/1.43    ~m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl5_2 | spl5_290)),
% 8.38/1.43    inference(subsumption_resolution,[],[f14315,f140])).
% 8.38/1.43  fof(f140,plain,(
% 8.38/1.43    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_2),
% 8.38/1.43    inference(avatar_component_clause,[],[f138])).
% 8.38/1.43  fof(f138,plain,(
% 8.38/1.43    spl5_2 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 8.38/1.43    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 8.38/1.43  fof(f14315,plain,(
% 8.38/1.43    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl5_290),
% 8.38/1.43    inference(subsumption_resolution,[],[f14313,f87])).
% 8.38/1.43  fof(f87,plain,(
% 8.38/1.43    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 8.38/1.43    inference(cnf_transformation,[],[f2])).
% 8.38/1.43  fof(f2,axiom,(
% 8.38/1.43    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 8.38/1.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 8.38/1.43  fof(f14313,plain,(
% 8.38/1.43    ~r1_tarski(k3_xboole_0(sK1,sK2),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl5_290),
% 8.38/1.43    inference(resolution,[],[f14302,f84])).
% 8.38/1.43  fof(f14302,plain,(
% 8.38/1.43    ~r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),k2_pre_topc(sK0,sK1)) | spl5_290),
% 8.38/1.43    inference(avatar_component_clause,[],[f14300])).
% 8.38/1.43  fof(f14300,plain,(
% 8.38/1.43    spl5_290 <=> r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),k2_pre_topc(sK0,sK1))),
% 8.38/1.43    introduced(avatar_definition,[new_symbols(naming,[spl5_290])])).
% 8.38/1.43  fof(f14307,plain,(
% 8.38/1.43    ~spl5_290 | ~spl5_291 | spl5_286),
% 8.38/1.43    inference(avatar_split_clause,[],[f14133,f14024,f14304,f14300])).
% 8.38/1.43  fof(f14024,plain,(
% 8.38/1.43    spl5_286 <=> r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)))),
% 8.38/1.43    introduced(avatar_definition,[new_symbols(naming,[spl5_286])])).
% 8.38/1.43  fof(f14133,plain,(
% 8.38/1.43    ~r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),k2_pre_topc(sK0,sK2)) | ~r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),k2_pre_topc(sK0,sK1)) | spl5_286),
% 8.38/1.43    inference(resolution,[],[f14026,f119])).
% 8.38/1.43  fof(f119,plain,(
% 8.38/1.43    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 8.38/1.43    inference(cnf_transformation,[],[f59])).
% 8.38/1.43  fof(f59,plain,(
% 8.38/1.43    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 8.38/1.43    inference(flattening,[],[f58])).
% 8.38/1.43  fof(f58,plain,(
% 8.38/1.43    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 8.38/1.43    inference(ennf_transformation,[],[f3])).
% 8.38/1.43  fof(f3,axiom,(
% 8.38/1.43    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 8.38/1.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).
% 8.38/1.43  fof(f14026,plain,(
% 8.38/1.43    ~r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))) | spl5_286),
% 8.38/1.43    inference(avatar_component_clause,[],[f14024])).
% 8.38/1.43  fof(f14027,plain,(
% 8.38/1.43    ~spl5_286 | spl5_25 | ~spl5_43),
% 8.38/1.43    inference(avatar_split_clause,[],[f13919,f720,f431,f14024])).
% 8.38/1.43  fof(f431,plain,(
% 8.38/1.43    spl5_25 <=> r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)))),
% 8.38/1.43    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).
% 8.38/1.43  fof(f720,plain,(
% 8.38/1.43    spl5_43 <=> m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 8.38/1.43    introduced(avatar_definition,[new_symbols(naming,[spl5_43])])).
% 8.38/1.43  fof(f13919,plain,(
% 8.38/1.43    ~r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))) | (spl5_25 | ~spl5_43)),
% 8.38/1.43    inference(backward_demodulation,[],[f433,f800])).
% 8.38/1.43  fof(f800,plain,(
% 8.38/1.43    ( ! [X0] : (k3_xboole_0(X0,k2_pre_topc(sK0,sK2)) = k9_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,sK2))) ) | ~spl5_43),
% 8.38/1.43    inference(resolution,[],[f722,f113])).
% 8.38/1.43  fof(f113,plain,(
% 8.38/1.43    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)) )),
% 8.38/1.43    inference(cnf_transformation,[],[f52])).
% 8.38/1.43  fof(f52,plain,(
% 8.38/1.43    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 8.38/1.43    inference(ennf_transformation,[],[f14])).
% 8.38/1.43  fof(f14,axiom,(
% 8.38/1.43    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 8.38/1.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 8.38/1.43  fof(f722,plain,(
% 8.38/1.43    m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_43),
% 8.38/1.43    inference(avatar_component_clause,[],[f720])).
% 8.38/1.43  fof(f433,plain,(
% 8.38/1.43    ~r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))) | spl5_25),
% 8.38/1.43    inference(avatar_component_clause,[],[f431])).
% 8.38/1.43  fof(f13612,plain,(
% 8.38/1.43    spl5_264 | ~spl5_119),
% 8.38/1.43    inference(avatar_split_clause,[],[f13590,f3075,f13610])).
% 8.38/1.43  fof(f3075,plain,(
% 8.38/1.43    spl5_119 <=> sK1 = k3_xboole_0(u1_struct_0(sK0),sK1)),
% 8.38/1.43    introduced(avatar_definition,[new_symbols(naming,[spl5_119])])).
% 8.38/1.43  fof(f13590,plain,(
% 8.38/1.43    ( ! [X25] : (m1_subset_1(k3_xboole_0(sK1,X25),k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl5_119),
% 8.38/1.43    inference(superposition,[],[f12275,f3077])).
% 8.38/1.43  fof(f3077,plain,(
% 8.38/1.43    sK1 = k3_xboole_0(u1_struct_0(sK0),sK1) | ~spl5_119),
% 8.38/1.43    inference(avatar_component_clause,[],[f3075])).
% 8.38/1.43  fof(f12275,plain,(
% 8.38/1.43    ( ! [X6,X7,X5] : (m1_subset_1(k3_xboole_0(k3_xboole_0(X5,X6),X7),k1_zfmisc_1(X5))) )),
% 8.38/1.43    inference(resolution,[],[f7011,f87])).
% 8.38/1.43  fof(f7011,plain,(
% 8.38/1.43    ( ! [X4,X2,X3] : (~r1_tarski(X2,k3_xboole_0(X3,X4)) | m1_subset_1(X2,k1_zfmisc_1(X3))) )),
% 8.38/1.43    inference(resolution,[],[f1510,f87])).
% 8.38/1.43  fof(f1510,plain,(
% 8.38/1.43    ( ! [X10,X11,X9] : (~r1_tarski(X10,X11) | m1_subset_1(X9,k1_zfmisc_1(X11)) | ~r1_tarski(X9,X10)) )),
% 8.38/1.43    inference(resolution,[],[f584,f95])).
% 8.38/1.43  fof(f95,plain,(
% 8.38/1.43    ( ! [X0,X1] : (r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 8.38/1.43    inference(cnf_transformation,[],[f44])).
% 8.38/1.43  fof(f44,plain,(
% 8.38/1.43    ! [X0,X1] : (r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 8.38/1.43    inference(ennf_transformation,[],[f10])).
% 8.38/1.43  fof(f10,axiom,(
% 8.38/1.43    ! [X0,X1] : (r1_tarski(X0,X1) => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)))),
% 8.38/1.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_zfmisc_1)).
% 8.38/1.43  fof(f584,plain,(
% 8.38/1.43    ( ! [X2,X0,X1] : (~r1_tarski(k1_zfmisc_1(X2),X1) | ~r1_tarski(X0,X2) | m1_subset_1(X0,X1)) )),
% 8.38/1.43    inference(resolution,[],[f235,f110])).
% 8.38/1.43  fof(f110,plain,(
% 8.38/1.43    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 8.38/1.43    inference(cnf_transformation,[],[f77])).
% 8.38/1.43  fof(f77,plain,(
% 8.38/1.43    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 8.38/1.43    inference(nnf_transformation,[],[f19])).
% 8.38/1.43  fof(f19,axiom,(
% 8.38/1.43    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 8.38/1.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 8.38/1.43  fof(f235,plain,(
% 8.38/1.43    ( ! [X2,X0,X1] : (~m1_subset_1(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) | m1_subset_1(X2,X1) | ~r1_tarski(X2,X0)) )),
% 8.38/1.43    inference(resolution,[],[f118,f128])).
% 8.38/1.43  fof(f128,plain,(
% 8.38/1.43    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 8.38/1.43    inference(equality_resolution,[],[f106])).
% 8.38/1.43  fof(f106,plain,(
% 8.38/1.43    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 8.38/1.43    inference(cnf_transformation,[],[f76])).
% 8.38/1.43  fof(f76,plain,(
% 8.38/1.43    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 8.38/1.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f74,f75])).
% 8.38/1.43  fof(f75,plain,(
% 8.38/1.43    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 8.38/1.43    introduced(choice_axiom,[])).
% 8.38/1.43  fof(f74,plain,(
% 8.38/1.43    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 8.38/1.43    inference(rectify,[],[f73])).
% 8.38/1.43  fof(f73,plain,(
% 8.38/1.43    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 8.38/1.43    inference(nnf_transformation,[],[f9])).
% 8.38/1.43  fof(f9,axiom,(
% 8.38/1.43    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 8.38/1.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 8.38/1.43  fof(f118,plain,(
% 8.38/1.43    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2)) )),
% 8.38/1.43    inference(cnf_transformation,[],[f57])).
% 8.38/1.43  fof(f57,plain,(
% 8.38/1.43    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 8.38/1.43    inference(flattening,[],[f56])).
% 8.38/1.43  fof(f56,plain,(
% 8.38/1.43    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 8.38/1.43    inference(ennf_transformation,[],[f20])).
% 8.38/1.43  fof(f20,axiom,(
% 8.38/1.43    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 8.38/1.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 8.38/1.43  fof(f3078,plain,(
% 8.38/1.43    spl5_119 | ~spl5_4 | ~spl5_118),
% 8.38/1.43    inference(avatar_split_clause,[],[f3069,f2962,f155,f3075])).
% 8.38/1.43  fof(f155,plain,(
% 8.38/1.43    spl5_4 <=> r1_tarski(sK1,u1_struct_0(sK0))),
% 8.38/1.43    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 8.38/1.43  fof(f2962,plain,(
% 8.38/1.43    spl5_118 <=> ! [X1,X0] : (~r1_tarski(X0,X1) | k3_xboole_0(X1,X0) = X0)),
% 8.38/1.43    introduced(avatar_definition,[new_symbols(naming,[spl5_118])])).
% 8.38/1.43  fof(f3069,plain,(
% 8.38/1.43    sK1 = k3_xboole_0(u1_struct_0(sK0),sK1) | (~spl5_4 | ~spl5_118)),
% 8.38/1.43    inference(resolution,[],[f2963,f157])).
% 8.38/1.43  fof(f157,plain,(
% 8.38/1.43    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl5_4),
% 8.38/1.43    inference(avatar_component_clause,[],[f155])).
% 8.38/1.43  fof(f2963,plain,(
% 8.38/1.43    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X1,X0) = X0) ) | ~spl5_118),
% 8.38/1.43    inference(avatar_component_clause,[],[f2962])).
% 8.38/1.43  fof(f2964,plain,(
% 8.38/1.43    spl5_118 | ~spl5_94),
% 8.38/1.43    inference(avatar_split_clause,[],[f2069,f2048,f2962])).
% 8.38/1.43  fof(f2069,plain,(
% 8.38/1.43    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X1,X0) = X0) ) | ~spl5_94),
% 8.38/1.43    inference(subsumption_resolution,[],[f2051,f126])).
% 8.38/1.43  fof(f126,plain,(
% 8.38/1.43    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 8.38/1.43    inference(equality_resolution,[],[f103])).
% 8.38/1.43  fof(f103,plain,(
% 8.38/1.43    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 8.38/1.43    inference(cnf_transformation,[],[f72])).
% 8.38/1.43  fof(f72,plain,(
% 8.38/1.43    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 8.38/1.43    inference(flattening,[],[f71])).
% 8.38/1.43  fof(f71,plain,(
% 8.38/1.43    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 8.38/1.43    inference(nnf_transformation,[],[f1])).
% 8.38/1.43  fof(f1,axiom,(
% 8.38/1.43    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 8.38/1.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 8.38/1.43  fof(f2051,plain,(
% 8.38/1.43    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X0,X0) | k3_xboole_0(X1,X0) = X0) ) | ~spl5_94),
% 8.38/1.43    inference(resolution,[],[f2049,f261])).
% 8.38/1.43  fof(f261,plain,(
% 8.38/1.43    ( ! [X2,X0,X1] : (~r1_tarski(k3_xboole_0(X2,X1),X0) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1) | k3_xboole_0(X2,X1) = X0) )),
% 8.38/1.43    inference(resolution,[],[f119,f104])).
% 8.38/1.43  fof(f104,plain,(
% 8.38/1.43    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 8.38/1.43    inference(cnf_transformation,[],[f72])).
% 8.38/1.43  fof(f2050,plain,(
% 8.38/1.43    spl5_94 | ~spl5_88),
% 8.38/1.43    inference(avatar_split_clause,[],[f2013,f1762,f2048])).
% 8.38/1.43  fof(f1762,plain,(
% 8.38/1.43    spl5_88 <=> ! [X5,X6] : r1_tarski(k2_subset_1(k3_xboole_0(X5,X6)),X6)),
% 8.38/1.43    introduced(avatar_definition,[new_symbols(naming,[spl5_88])])).
% 8.38/1.43  fof(f2013,plain,(
% 8.38/1.43    ( ! [X6,X5] : (r1_tarski(k3_xboole_0(X5,X6),X6)) ) | ~spl5_88),
% 8.38/1.43    inference(backward_demodulation,[],[f1763,f1968])).
% 8.38/1.43  fof(f1968,plain,(
% 8.38/1.43    ( ! [X5] : (k2_subset_1(X5) = X5) )),
% 8.38/1.43    inference(subsumption_resolution,[],[f1954,f1659])).
% 8.38/1.43  fof(f1659,plain,(
% 8.38/1.43    ( ! [X2] : (r1_tarski(k2_subset_1(X2),X2)) )),
% 8.38/1.43    inference(backward_demodulation,[],[f930,f1653])).
% 8.38/1.43  fof(f1653,plain,(
% 8.38/1.43    ( ! [X0] : (k2_subset_1(X0) = k2_xboole_0(k1_xboole_0,X0)) )),
% 8.38/1.43    inference(forward_demodulation,[],[f1622,f926])).
% 8.38/1.43  fof(f926,plain,(
% 8.38/1.43    ( ! [X2] : (k2_subset_1(X2) = k4_subset_1(X2,k1_xboole_0,X2)) )),
% 8.38/1.43    inference(backward_demodulation,[],[f522,f923])).
% 8.38/1.43  fof(f923,plain,(
% 8.38/1.43    ( ! [X2] : (k4_xboole_0(X2,k1_xboole_0) = X2) )),
% 8.38/1.43    inference(backward_demodulation,[],[f245,f921])).
% 8.38/1.43  fof(f921,plain,(
% 8.38/1.43    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 8.38/1.43    inference(forward_demodulation,[],[f562,f560])).
% 8.38/1.43  fof(f560,plain,(
% 8.38/1.43    ( ! [X0] : (k1_xboole_0 = k3_subset_1(X0,X0)) )),
% 8.38/1.43    inference(forward_demodulation,[],[f543,f270])).
% 8.38/1.43  fof(f270,plain,(
% 8.38/1.43    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(X2,X2)) )),
% 8.38/1.43    inference(resolution,[],[f227,f85])).
% 8.38/1.43  fof(f85,plain,(
% 8.38/1.43    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 8.38/1.43    inference(cnf_transformation,[],[f37])).
% 8.38/1.43  fof(f37,plain,(
% 8.38/1.43    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 8.38/1.43    inference(ennf_transformation,[],[f6])).
% 8.38/1.43  fof(f6,axiom,(
% 8.38/1.43    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 8.38/1.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).
% 8.38/1.43  fof(f227,plain,(
% 8.38/1.43    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X0),X1)) )),
% 8.38/1.43    inference(resolution,[],[f114,f86])).
% 8.38/1.43  fof(f86,plain,(
% 8.38/1.43    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 8.38/1.43    inference(cnf_transformation,[],[f8])).
% 8.38/1.43  fof(f8,axiom,(
% 8.38/1.43    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 8.38/1.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 8.38/1.43  fof(f114,plain,(
% 8.38/1.43    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_xboole_0(X1,X2)) | r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 8.38/1.43    inference(cnf_transformation,[],[f53])).
% 8.38/1.43  fof(f53,plain,(
% 8.38/1.43    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 8.38/1.43    inference(ennf_transformation,[],[f7])).
% 8.38/1.43  fof(f7,axiom,(
% 8.38/1.43    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 8.38/1.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).
% 8.38/1.43  fof(f543,plain,(
% 8.38/1.43    ( ! [X0] : (k4_xboole_0(X0,X0) = k3_subset_1(X0,X0)) )),
% 8.38/1.43    inference(resolution,[],[f244,f126])).
% 8.38/1.43  fof(f244,plain,(
% 8.38/1.43    ( ! [X0,X1] : (~r1_tarski(X1,X0) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 8.38/1.43    inference(resolution,[],[f96,f110])).
% 8.38/1.43  fof(f96,plain,(
% 8.38/1.43    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 8.38/1.43    inference(cnf_transformation,[],[f45])).
% 8.38/1.43  fof(f45,plain,(
% 8.38/1.43    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 8.38/1.43    inference(ennf_transformation,[],[f11])).
% 8.38/1.43  fof(f11,axiom,(
% 8.38/1.43    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 8.38/1.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 8.38/1.43  fof(f562,plain,(
% 8.38/1.43    ( ! [X0] : (k3_subset_1(X0,k3_subset_1(X0,X0)) = X0) )),
% 8.38/1.43    inference(resolution,[],[f249,f126])).
% 8.38/1.43  fof(f249,plain,(
% 8.38/1.43    ( ! [X0,X1] : (~r1_tarski(X1,X0) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 8.38/1.43    inference(resolution,[],[f97,f110])).
% 8.38/1.43  fof(f97,plain,(
% 8.38/1.43    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 8.38/1.43    inference(cnf_transformation,[],[f46])).
% 8.38/1.43  fof(f46,plain,(
% 8.38/1.43    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 8.38/1.43    inference(ennf_transformation,[],[f12])).
% 8.38/1.43  fof(f12,axiom,(
% 8.38/1.43    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 8.38/1.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 8.38/1.43  fof(f245,plain,(
% 8.38/1.43    ( ! [X2] : (k4_xboole_0(X2,k1_xboole_0) = k3_subset_1(X2,k1_xboole_0)) )),
% 8.38/1.43    inference(resolution,[],[f96,f83])).
% 8.38/1.43  fof(f83,plain,(
% 8.38/1.43    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 8.38/1.43    inference(cnf_transformation,[],[f17])).
% 8.38/1.43  fof(f17,axiom,(
% 8.38/1.43    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 8.38/1.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 8.38/1.43  fof(f522,plain,(
% 8.38/1.43    ( ! [X2] : (k2_subset_1(X2) = k4_subset_1(X2,k1_xboole_0,k4_xboole_0(X2,k1_xboole_0))) )),
% 8.38/1.43    inference(forward_demodulation,[],[f281,f245])).
% 8.38/1.43  fof(f281,plain,(
% 8.38/1.43    ( ! [X2] : (k4_subset_1(X2,k1_xboole_0,k3_subset_1(X2,k1_xboole_0)) = k2_subset_1(X2)) )),
% 8.38/1.43    inference(resolution,[],[f98,f83])).
% 8.38/1.43  fof(f98,plain,(
% 8.38/1.43    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = k2_subset_1(X0)) )),
% 8.38/1.43    inference(cnf_transformation,[],[f47])).
% 8.38/1.43  fof(f47,plain,(
% 8.38/1.43    ! [X0,X1] : (k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = k2_subset_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 8.38/1.43    inference(ennf_transformation,[],[f15])).
% 8.38/1.43  fof(f15,axiom,(
% 8.38/1.43    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = k2_subset_1(X0))),
% 8.38/1.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).
% 8.38/1.43  fof(f1622,plain,(
% 8.38/1.43    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = k4_subset_1(X0,k1_xboole_0,X0)) )),
% 8.38/1.43    inference(resolution,[],[f708,f126])).
% 8.38/1.43  fof(f708,plain,(
% 8.38/1.43    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(k1_xboole_0,X0) = k4_subset_1(X1,k1_xboole_0,X0)) )),
% 8.38/1.43    inference(resolution,[],[f312,f110])).
% 8.38/1.43  fof(f312,plain,(
% 8.38/1.43    ( ! [X4,X3] : (~m1_subset_1(X3,k1_zfmisc_1(X4)) | k2_xboole_0(k1_xboole_0,X3) = k4_subset_1(X4,k1_xboole_0,X3)) )),
% 8.38/1.43    inference(resolution,[],[f120,f83])).
% 8.38/1.43  fof(f120,plain,(
% 8.38/1.43    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)) )),
% 8.38/1.43    inference(cnf_transformation,[],[f61])).
% 8.38/1.43  fof(f61,plain,(
% 8.38/1.43    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 8.38/1.43    inference(flattening,[],[f60])).
% 8.38/1.43  fof(f60,plain,(
% 8.38/1.43    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 8.38/1.43    inference(ennf_transformation,[],[f13])).
% 8.38/1.43  fof(f13,axiom,(
% 8.38/1.43    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 8.38/1.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 8.38/1.43  fof(f930,plain,(
% 8.38/1.43    ( ! [X2] : (r1_tarski(k2_xboole_0(k1_xboole_0,X2),X2)) )),
% 8.38/1.43    inference(superposition,[],[f228,f923])).
% 8.38/1.43  fof(f228,plain,(
% 8.38/1.43    ( ! [X2,X3] : (r1_tarski(k4_xboole_0(k2_xboole_0(X2,X3),X2),X3)) )),
% 8.38/1.43    inference(resolution,[],[f114,f126])).
% 8.38/1.43  fof(f1954,plain,(
% 8.38/1.43    ( ! [X5] : (~r1_tarski(k2_subset_1(X5),X5) | k2_subset_1(X5) = X5) )),
% 8.38/1.43    inference(superposition,[],[f193,f1920])).
% 8.38/1.43  fof(f1920,plain,(
% 8.38/1.43    ( ! [X0] : (k2_subset_1(X0) = k2_xboole_0(X0,k1_xboole_0)) )),
% 8.38/1.43    inference(forward_demodulation,[],[f1890,f699])).
% 8.38/1.43  fof(f699,plain,(
% 8.38/1.43    ( ! [X0] : (k2_subset_1(X0) = k4_subset_1(X0,X0,k1_xboole_0)) )),
% 8.38/1.43    inference(forward_demodulation,[],[f681,f560])).
% 8.38/1.43  fof(f681,plain,(
% 8.38/1.43    ( ! [X0] : (k2_subset_1(X0) = k4_subset_1(X0,X0,k3_subset_1(X0,X0))) )),
% 8.38/1.43    inference(resolution,[],[f280,f126])).
% 8.38/1.43  fof(f280,plain,(
% 8.38/1.43    ( ! [X0,X1] : (~r1_tarski(X1,X0) | k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = k2_subset_1(X0)) )),
% 8.38/1.43    inference(resolution,[],[f98,f110])).
% 8.38/1.43  fof(f1890,plain,(
% 8.38/1.43    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = k4_subset_1(X0,X0,k1_xboole_0)) )),
% 8.38/1.43    inference(resolution,[],[f805,f126])).
% 8.38/1.43  fof(f805,plain,(
% 8.38/1.43    ( ! [X4,X3] : (~r1_tarski(X3,X4) | k2_xboole_0(X3,k1_xboole_0) = k4_subset_1(X4,X3,k1_xboole_0)) )),
% 8.38/1.43    inference(resolution,[],[f311,f83])).
% 8.38/1.43  fof(f311,plain,(
% 8.38/1.43    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | k2_xboole_0(X2,X0) = k4_subset_1(X1,X2,X0) | ~r1_tarski(X2,X1)) )),
% 8.38/1.43    inference(resolution,[],[f120,f110])).
% 8.38/1.43  fof(f193,plain,(
% 8.38/1.43    ( ! [X4,X5] : (~r1_tarski(k2_xboole_0(X4,X5),X4) | k2_xboole_0(X4,X5) = X4) )),
% 8.38/1.43    inference(resolution,[],[f104,f86])).
% 8.38/1.43  fof(f1763,plain,(
% 8.38/1.43    ( ! [X6,X5] : (r1_tarski(k2_subset_1(k3_xboole_0(X5,X6)),X6)) ) | ~spl5_88),
% 8.38/1.43    inference(avatar_component_clause,[],[f1762])).
% 8.38/1.43  fof(f1764,plain,(
% 8.38/1.43    spl5_88 | ~spl5_50),
% 8.38/1.43    inference(avatar_split_clause,[],[f1661,f1032,f1762])).
% 8.38/1.43  fof(f1032,plain,(
% 8.38/1.43    spl5_50 <=> ! [X5,X6] : r1_tarski(k2_xboole_0(k1_xboole_0,k3_xboole_0(X5,X6)),X6)),
% 8.38/1.43    introduced(avatar_definition,[new_symbols(naming,[spl5_50])])).
% 8.38/1.43  fof(f1661,plain,(
% 8.38/1.43    ( ! [X6,X5] : (r1_tarski(k2_subset_1(k3_xboole_0(X5,X6)),X6)) ) | ~spl5_50),
% 8.38/1.43    inference(backward_demodulation,[],[f1033,f1653])).
% 8.38/1.43  fof(f1033,plain,(
% 8.38/1.43    ( ! [X6,X5] : (r1_tarski(k2_xboole_0(k1_xboole_0,k3_xboole_0(X5,X6)),X6)) ) | ~spl5_50),
% 8.38/1.43    inference(avatar_component_clause,[],[f1032])).
% 8.38/1.43  fof(f1034,plain,(
% 8.38/1.43    spl5_50 | ~spl5_26),
% 8.38/1.43    inference(avatar_split_clause,[],[f934,f442,f1032])).
% 8.38/1.43  fof(f442,plain,(
% 8.38/1.43    spl5_26 <=> ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 8.38/1.43    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).
% 8.38/1.43  fof(f934,plain,(
% 8.38/1.43    ( ! [X6,X5] : (r1_tarski(k2_xboole_0(k1_xboole_0,k3_xboole_0(X5,X6)),X6)) ) | ~spl5_26),
% 8.38/1.43    inference(forward_demodulation,[],[f933,f443])).
% 8.38/1.43  fof(f443,plain,(
% 8.38/1.43    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) ) | ~spl5_26),
% 8.38/1.43    inference(avatar_component_clause,[],[f442])).
% 8.38/1.43  fof(f933,plain,(
% 8.38/1.43    ( ! [X6,X5] : (r1_tarski(k2_xboole_0(k3_xboole_0(X5,k1_xboole_0),k3_xboole_0(X5,X6)),X6)) )),
% 8.38/1.43    inference(superposition,[],[f254,f923])).
% 8.38/1.43  fof(f254,plain,(
% 8.38/1.43    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),X1),X2)) )),
% 8.38/1.43    inference(resolution,[],[f111,f114])).
% 8.38/1.43  fof(f111,plain,(
% 8.38/1.43    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))) )),
% 8.38/1.43    inference(cnf_transformation,[],[f5])).
% 8.38/1.43  fof(f5,axiom,(
% 8.38/1.43    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))),
% 8.38/1.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_xboole_1)).
% 8.38/1.43  fof(f723,plain,(
% 8.38/1.43    spl5_43 | ~spl5_3 | ~spl5_37),
% 8.38/1.43    inference(avatar_split_clause,[],[f674,f649,f143,f720])).
% 8.38/1.43  fof(f649,plain,(
% 8.38/1.43    spl5_37 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))))),
% 8.38/1.43    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).
% 8.38/1.43  fof(f674,plain,(
% 8.38/1.43    m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl5_3 | ~spl5_37)),
% 8.38/1.43    inference(resolution,[],[f650,f145])).
% 8.38/1.43  fof(f650,plain,(
% 8.38/1.43    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl5_37),
% 8.38/1.43    inference(avatar_component_clause,[],[f649])).
% 8.38/1.43  fof(f651,plain,(
% 8.38/1.43    spl5_37 | ~spl5_1),
% 8.38/1.43    inference(avatar_split_clause,[],[f295,f133,f649])).
% 8.38/1.43  fof(f295,plain,(
% 8.38/1.43    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl5_1),
% 8.38/1.43    inference(resolution,[],[f101,f135])).
% 8.38/1.43  fof(f101,plain,(
% 8.38/1.43    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 8.38/1.43    inference(cnf_transformation,[],[f50])).
% 8.38/1.43  fof(f50,plain,(
% 8.38/1.43    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 8.38/1.43    inference(flattening,[],[f49])).
% 8.38/1.43  fof(f49,plain,(
% 8.38/1.43    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 8.38/1.43    inference(ennf_transformation,[],[f30])).
% 8.38/1.43  fof(f30,axiom,(
% 8.38/1.43    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 8.38/1.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 8.38/1.43  fof(f449,plain,(
% 8.38/1.43    spl5_26 | ~spl5_23),
% 8.38/1.43    inference(avatar_split_clause,[],[f438,f421,f442])).
% 8.38/1.43  fof(f421,plain,(
% 8.38/1.43    spl5_23 <=> ! [X1] : r1_tarski(k3_xboole_0(X1,k1_xboole_0),k1_xboole_0)),
% 8.38/1.43    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).
% 8.38/1.43  fof(f438,plain,(
% 8.38/1.43    ( ! [X1] : (k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0)) ) | ~spl5_23),
% 8.38/1.43    inference(subsumption_resolution,[],[f436,f82])).
% 8.38/1.43  fof(f82,plain,(
% 8.38/1.43    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 8.38/1.43    inference(cnf_transformation,[],[f4])).
% 8.38/1.43  fof(f4,axiom,(
% 8.38/1.43    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 8.38/1.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 8.38/1.43  fof(f436,plain,(
% 8.38/1.43    ( ! [X1] : (~r1_tarski(k1_xboole_0,k3_xboole_0(X1,k1_xboole_0)) | k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0)) ) | ~spl5_23),
% 8.38/1.43    inference(resolution,[],[f422,f104])).
% 8.38/1.43  fof(f422,plain,(
% 8.38/1.43    ( ! [X1] : (r1_tarski(k3_xboole_0(X1,k1_xboole_0),k1_xboole_0)) ) | ~spl5_23),
% 8.38/1.43    inference(avatar_component_clause,[],[f421])).
% 8.38/1.43  fof(f434,plain,(
% 8.38/1.43    ~spl5_25 | ~spl5_3 | spl5_11),
% 8.38/1.43    inference(avatar_split_clause,[],[f424,f318,f143,f431])).
% 8.38/1.43  fof(f318,plain,(
% 8.38/1.43    spl5_11 <=> r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)))),
% 8.38/1.43    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 8.38/1.43  fof(f424,plain,(
% 8.38/1.43    ~r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))) | (~spl5_3 | spl5_11)),
% 8.38/1.43    inference(backward_demodulation,[],[f320,f268])).
% 8.38/1.43  fof(f268,plain,(
% 8.38/1.43    ( ! [X6] : (k3_xboole_0(X6,sK2) = k9_subset_1(u1_struct_0(sK0),X6,sK2)) ) | ~spl5_3),
% 8.38/1.43    inference(resolution,[],[f113,f145])).
% 8.38/1.43  fof(f320,plain,(
% 8.38/1.43    ~r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))) | spl5_11),
% 8.38/1.43    inference(avatar_component_clause,[],[f318])).
% 8.38/1.43  fof(f429,plain,(
% 8.38/1.43    spl5_23 | ~spl5_6 | ~spl5_13),
% 8.38/1.43    inference(avatar_split_clause,[],[f415,f339,f174,f421])).
% 8.38/1.43  fof(f174,plain,(
% 8.38/1.43    spl5_6 <=> v1_relat_1(k1_xboole_0)),
% 8.38/1.43    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 8.38/1.43  fof(f339,plain,(
% 8.38/1.43    spl5_13 <=> ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)),
% 8.38/1.43    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 8.38/1.43  fof(f415,plain,(
% 8.38/1.43    ( ! [X3] : (r1_tarski(k3_xboole_0(X3,k1_xboole_0),k1_xboole_0)) ) | (~spl5_6 | ~spl5_13)),
% 8.38/1.43    inference(forward_demodulation,[],[f414,f340])).
% 8.38/1.43  fof(f340,plain,(
% 8.38/1.43    ( ! [X0] : (k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)) ) | ~spl5_13),
% 8.38/1.43    inference(avatar_component_clause,[],[f339])).
% 8.38/1.43  fof(f414,plain,(
% 8.38/1.43    ( ! [X4,X3] : (r1_tarski(k3_xboole_0(X3,k10_relat_1(k1_xboole_0,X4)),k1_xboole_0)) ) | (~spl5_6 | ~spl5_13)),
% 8.38/1.43    inference(subsumption_resolution,[],[f411,f176])).
% 8.38/1.43  fof(f176,plain,(
% 8.38/1.43    v1_relat_1(k1_xboole_0) | ~spl5_6),
% 8.38/1.43    inference(avatar_component_clause,[],[f174])).
% 8.38/1.43  fof(f411,plain,(
% 8.38/1.43    ( ! [X4,X3] : (r1_tarski(k3_xboole_0(X3,k10_relat_1(k1_xboole_0,X4)),k1_xboole_0) | ~v1_relat_1(k1_xboole_0)) ) | ~spl5_13),
% 8.38/1.43    inference(superposition,[],[f112,f340])).
% 8.38/1.43  fof(f112,plain,(
% 8.38/1.43    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,k10_relat_1(X2,X1)),k10_relat_1(X2,k3_xboole_0(k9_relat_1(X2,X0),X1))) | ~v1_relat_1(X2)) )),
% 8.38/1.43    inference(cnf_transformation,[],[f51])).
% 8.38/1.43  fof(f51,plain,(
% 8.38/1.43    ! [X0,X1,X2] : (r1_tarski(k3_xboole_0(X0,k10_relat_1(X2,X1)),k10_relat_1(X2,k3_xboole_0(k9_relat_1(X2,X0),X1))) | ~v1_relat_1(X2))),
% 8.38/1.43    inference(ennf_transformation,[],[f26])).
% 8.38/1.43  fof(f26,axiom,(
% 8.38/1.43    ! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k3_xboole_0(X0,k10_relat_1(X2,X1)),k10_relat_1(X2,k3_xboole_0(k9_relat_1(X2,X0),X1))))),
% 8.38/1.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_funct_1)).
% 8.38/1.43  fof(f403,plain,(
% 8.38/1.43    spl5_13 | ~spl5_12),
% 8.38/1.43    inference(avatar_split_clause,[],[f335,f328,f339])).
% 8.38/1.43  fof(f328,plain,(
% 8.38/1.43    spl5_12 <=> ! [X0] : r1_tarski(k10_relat_1(k1_xboole_0,X0),k1_xboole_0)),
% 8.38/1.43    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 8.38/1.43  fof(f335,plain,(
% 8.38/1.43    ( ! [X1] : (k1_xboole_0 = k10_relat_1(k1_xboole_0,X1)) ) | ~spl5_12),
% 8.38/1.43    inference(subsumption_resolution,[],[f334,f82])).
% 8.38/1.43  fof(f334,plain,(
% 8.38/1.43    ( ! [X1] : (~r1_tarski(k1_xboole_0,k10_relat_1(k1_xboole_0,X1)) | k1_xboole_0 = k10_relat_1(k1_xboole_0,X1)) ) | ~spl5_12),
% 8.38/1.43    inference(resolution,[],[f329,f104])).
% 8.38/1.43  fof(f329,plain,(
% 8.38/1.43    ( ! [X0] : (r1_tarski(k10_relat_1(k1_xboole_0,X0),k1_xboole_0)) ) | ~spl5_12),
% 8.38/1.43    inference(avatar_component_clause,[],[f328])).
% 8.38/1.43  fof(f330,plain,(
% 8.38/1.43    spl5_12 | ~spl5_6 | ~spl5_10),
% 8.38/1.43    inference(avatar_split_clause,[],[f264,f240,f174,f328])).
% 8.38/1.43  fof(f240,plain,(
% 8.38/1.43    spl5_10 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 8.38/1.43    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 8.38/1.43  fof(f264,plain,(
% 8.38/1.43    ( ! [X0] : (r1_tarski(k10_relat_1(k1_xboole_0,X0),k1_xboole_0)) ) | (~spl5_6 | ~spl5_10)),
% 8.38/1.43    inference(subsumption_resolution,[],[f263,f176])).
% 8.38/1.43  fof(f263,plain,(
% 8.38/1.43    ( ! [X0] : (r1_tarski(k10_relat_1(k1_xboole_0,X0),k1_xboole_0) | ~v1_relat_1(k1_xboole_0)) ) | ~spl5_10),
% 8.38/1.43    inference(superposition,[],[f89,f242])).
% 8.38/1.43  fof(f242,plain,(
% 8.38/1.43    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl5_10),
% 8.38/1.43    inference(avatar_component_clause,[],[f240])).
% 8.38/1.43  fof(f89,plain,(
% 8.38/1.43    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 8.38/1.43    inference(cnf_transformation,[],[f39])).
% 8.38/1.43  fof(f39,plain,(
% 8.38/1.43    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 8.38/1.43    inference(ennf_transformation,[],[f25])).
% 8.38/1.43  fof(f25,axiom,(
% 8.38/1.43    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 8.38/1.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).
% 8.38/1.43  fof(f321,plain,(
% 8.38/1.43    ~spl5_11),
% 8.38/1.43    inference(avatar_split_clause,[],[f81,f318])).
% 8.38/1.43  fof(f81,plain,(
% 8.38/1.43    ~r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)))),
% 8.38/1.43    inference(cnf_transformation,[],[f67])).
% 8.38/1.43  fof(f67,plain,(
% 8.38/1.43    ((~r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 8.38/1.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f34,f66,f65,f64])).
% 8.38/1.43  fof(f64,plain,(
% 8.38/1.43    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X1,X2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 8.38/1.43    introduced(choice_axiom,[])).
% 8.38/1.43  fof(f65,plain,(
% 8.38/1.43    ? [X1] : (? [X2] : (~r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X1,X2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (~r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,X2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 8.38/1.43    introduced(choice_axiom,[])).
% 8.38/1.43  fof(f66,plain,(
% 8.38/1.43    ? [X2] : (~r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,X2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (~r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 8.38/1.43    introduced(choice_axiom,[])).
% 8.38/1.43  fof(f34,plain,(
% 8.38/1.43    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 8.38/1.43    inference(ennf_transformation,[],[f33])).
% 8.38/1.43  fof(f33,negated_conjecture,(
% 8.38/1.43    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))))))),
% 8.38/1.43    inference(negated_conjecture,[],[f32])).
% 8.38/1.43  fof(f32,conjecture,(
% 8.38/1.43    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))))))),
% 8.38/1.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_pre_topc)).
% 8.38/1.43  fof(f260,plain,(
% 8.38/1.43    spl5_10 | ~spl5_8),
% 8.38/1.43    inference(avatar_split_clause,[],[f221,f211,f240])).
% 8.38/1.43  fof(f211,plain,(
% 8.38/1.43    spl5_8 <=> ! [X0] : r1_tarski(k1_relat_1(k1_xboole_0),X0)),
% 8.38/1.43    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 8.38/1.43  fof(f221,plain,(
% 8.38/1.43    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl5_8),
% 8.38/1.43    inference(resolution,[],[f123,f212])).
% 8.38/1.43  fof(f212,plain,(
% 8.38/1.43    ( ! [X0] : (r1_tarski(k1_relat_1(k1_xboole_0),X0)) ) | ~spl5_8),
% 8.38/1.43    inference(avatar_component_clause,[],[f211])).
% 8.38/1.43  fof(f123,plain,(
% 8.38/1.43    ( ! [X2,X0,X1] : (~r1_tarski(X0,k3_zfmisc_1(X2,X0,X1)) | k1_xboole_0 = X0) )),
% 8.38/1.43    inference(cnf_transformation,[],[f62])).
% 8.38/1.43  fof(f62,plain,(
% 8.38/1.43    ! [X0,X1,X2] : (k1_xboole_0 = X0 | (~r1_tarski(X0,k3_zfmisc_1(X2,X0,X1)) & ~r1_tarski(X0,k3_zfmisc_1(X1,X2,X0)) & ~r1_tarski(X0,k3_zfmisc_1(X0,X1,X2))))),
% 8.38/1.43    inference(ennf_transformation,[],[f29])).
% 8.38/1.43  fof(f29,axiom,(
% 8.38/1.43    ! [X0,X1,X2] : (~(~r1_tarski(X0,k3_zfmisc_1(X2,X0,X1)) & ~r1_tarski(X0,k3_zfmisc_1(X1,X2,X0)) & ~r1_tarski(X0,k3_zfmisc_1(X0,X1,X2))) => k1_xboole_0 = X0)),
% 8.38/1.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_mcart_1)).
% 8.38/1.43  fof(f213,plain,(
% 8.38/1.43    spl5_8 | ~spl5_6),
% 8.38/1.43    inference(avatar_split_clause,[],[f206,f174,f211])).
% 8.38/1.43  fof(f206,plain,(
% 8.38/1.43    ( ! [X0] : (r1_tarski(k1_relat_1(k1_xboole_0),X0)) ) | ~spl5_6),
% 8.38/1.43    inference(subsumption_resolution,[],[f205,f176])).
% 8.38/1.43  fof(f205,plain,(
% 8.38/1.43    ( ! [X0] : (r1_tarski(k1_relat_1(k1_xboole_0),X0) | ~v1_relat_1(k1_xboole_0)) )),
% 8.38/1.43    inference(resolution,[],[f204,f92])).
% 8.38/1.43  fof(f92,plain,(
% 8.38/1.43    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 8.38/1.43    inference(cnf_transformation,[],[f69])).
% 8.38/1.43  fof(f69,plain,(
% 8.38/1.43    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 8.38/1.43    inference(nnf_transformation,[],[f41])).
% 8.38/1.43  fof(f41,plain,(
% 8.38/1.43    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 8.38/1.43    inference(ennf_transformation,[],[f22])).
% 8.38/1.43  fof(f22,axiom,(
% 8.38/1.43    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 8.38/1.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 8.38/1.43  fof(f204,plain,(
% 8.38/1.43    ( ! [X3] : (v4_relat_1(k1_xboole_0,X3)) )),
% 8.38/1.43    inference(resolution,[],[f116,f83])).
% 8.38/1.43  fof(f116,plain,(
% 8.38/1.43    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 8.38/1.43    inference(cnf_transformation,[],[f55])).
% 8.38/1.43  fof(f55,plain,(
% 8.38/1.43    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 8.38/1.43    inference(ennf_transformation,[],[f28])).
% 8.38/1.43  fof(f28,axiom,(
% 8.38/1.43    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 8.38/1.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 8.38/1.43  fof(f177,plain,(
% 8.38/1.43    spl5_6),
% 8.38/1.43    inference(avatar_split_clause,[],[f172,f174])).
% 8.38/1.43  fof(f172,plain,(
% 8.38/1.43    v1_relat_1(k1_xboole_0)),
% 8.38/1.43    inference(resolution,[],[f115,f83])).
% 8.38/1.43  fof(f115,plain,(
% 8.38/1.43    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 8.38/1.43    inference(cnf_transformation,[],[f54])).
% 8.38/1.43  fof(f54,plain,(
% 8.38/1.43    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 8.38/1.43    inference(ennf_transformation,[],[f27])).
% 8.38/1.43  fof(f27,axiom,(
% 8.38/1.43    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 8.38/1.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 8.38/1.43  fof(f158,plain,(
% 8.38/1.43    spl5_4 | ~spl5_2),
% 8.38/1.43    inference(avatar_split_clause,[],[f152,f138,f155])).
% 8.38/1.43  fof(f152,plain,(
% 8.38/1.43    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl5_2),
% 8.38/1.43    inference(resolution,[],[f109,f140])).
% 8.38/1.43  fof(f109,plain,(
% 8.38/1.43    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 8.38/1.43    inference(cnf_transformation,[],[f77])).
% 8.38/1.43  fof(f146,plain,(
% 8.38/1.43    spl5_3),
% 8.38/1.43    inference(avatar_split_clause,[],[f80,f143])).
% 8.38/1.43  fof(f80,plain,(
% 8.38/1.43    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 8.38/1.43    inference(cnf_transformation,[],[f67])).
% 8.38/1.43  fof(f141,plain,(
% 8.38/1.43    spl5_2),
% 8.38/1.43    inference(avatar_split_clause,[],[f79,f138])).
% 8.38/1.43  fof(f79,plain,(
% 8.38/1.43    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 8.38/1.43    inference(cnf_transformation,[],[f67])).
% 8.38/1.43  fof(f136,plain,(
% 8.38/1.43    spl5_1),
% 8.38/1.43    inference(avatar_split_clause,[],[f78,f133])).
% 8.38/1.43  fof(f78,plain,(
% 8.38/1.43    l1_pre_topc(sK0)),
% 8.38/1.43    inference(cnf_transformation,[],[f67])).
% 8.38/1.43  % SZS output end Proof for theBenchmark
% 8.38/1.43  % (21188)------------------------------
% 8.38/1.43  % (21188)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.38/1.43  % (21188)Termination reason: Refutation
% 8.38/1.43  
% 8.38/1.43  % (21188)Memory used [KB]: 16630
% 8.38/1.43  % (21188)Time elapsed: 0.981 s
% 8.38/1.43  % (21188)------------------------------
% 8.38/1.43  % (21188)------------------------------
% 8.38/1.44  % (21185)Success in time 1.072 s
%------------------------------------------------------------------------------
