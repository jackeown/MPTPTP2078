%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:23 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 217 expanded)
%              Number of leaves         :   30 (  82 expanded)
%              Depth                    :   13
%              Number of atoms          :  300 ( 518 expanded)
%              Number of equality atoms :   38 (  54 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f618,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f80,f85,f90,f95,f106,f114,f121,f129,f292,f314,f438,f529,f616,f617])).

fof(f617,plain,
    ( u1_struct_0(sK0) != k1_tops_1(sK0,u1_struct_0(sK0))
    | ~ r1_tarski(sK1,u1_struct_0(sK0))
    | r1_tarski(sK1,k1_tops_1(sK0,u1_struct_0(sK0))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f616,plain,
    ( spl4_65
    | ~ spl4_1
    | ~ spl4_43 ),
    inference(avatar_split_clause,[],[f611,f435,f77,f613])).

fof(f613,plain,
    ( spl4_65
  <=> u1_struct_0(sK0) = k1_tops_1(sK0,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_65])])).

fof(f77,plain,
    ( spl4_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f435,plain,
    ( spl4_43
  <=> k1_xboole_0 = k2_pre_topc(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).

fof(f611,plain,
    ( u1_struct_0(sK0) = k1_tops_1(sK0,u1_struct_0(sK0))
    | ~ spl4_1
    | ~ spl4_43 ),
    inference(forward_demodulation,[],[f610,f303])).

fof(f303,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f179,f270])).

fof(f270,plain,(
    ! [X1] : k1_xboole_0 = k3_subset_1(X1,X1) ),
    inference(resolution,[],[f245,f137])).

fof(f137,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,k1_xboole_0)
      | k1_xboole_0 = X1 ) ),
    inference(resolution,[],[f66,f122])).

fof(f122,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[],[f71,f49])).

fof(f49,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f245,plain,(
    ! [X0] : r1_tarski(k3_subset_1(X0,X0),k1_xboole_0) ),
    inference(global_subsumption,[],[f49,f107,f240])).

fof(f240,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X0))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
      | r1_tarski(k3_subset_1(X0,X0),k1_xboole_0) ) ),
    inference(resolution,[],[f63,f165])).

fof(f165,plain,(
    ! [X1] : r1_tarski(k3_subset_1(X1,k1_xboole_0),X1) ),
    inference(resolution,[],[f156,f71])).

fof(f156,plain,(
    ! [X0] : m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) ),
    inference(resolution,[],[f61,f49])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k3_subset_1(X0,X1),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | r1_tarski(k3_subset_1(X0,X2),X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k3_subset_1(X0,X2),X1)
          | ~ r1_tarski(k3_subset_1(X0,X1),X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k3_subset_1(X0,X2),X1)
          | ~ r1_tarski(k3_subset_1(X0,X1),X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(k3_subset_1(X0,X1),X2)
           => r1_tarski(k3_subset_1(X0,X2),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_subset_1)).

fof(f107,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f50,f48])).

fof(f48,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f50,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f179,plain,(
    ! [X0] : k3_subset_1(X0,k3_subset_1(X0,X0)) = X0 ),
    inference(resolution,[],[f62,f107])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f610,plain,
    ( k1_tops_1(sK0,u1_struct_0(sK0)) = k3_subset_1(u1_struct_0(sK0),k1_xboole_0)
    | ~ spl4_1
    | ~ spl4_43 ),
    inference(forward_demodulation,[],[f609,f437])).

fof(f437,plain,
    ( k1_xboole_0 = k2_pre_topc(sK0,k1_xboole_0)
    | ~ spl4_43 ),
    inference(avatar_component_clause,[],[f435])).

fof(f609,plain,
    ( k1_tops_1(sK0,u1_struct_0(sK0)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k1_xboole_0))
    | ~ spl4_1 ),
    inference(resolution,[],[f608,f79])).

fof(f79,plain,
    ( l1_pre_topc(sK0)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f77])).

fof(f608,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | k1_tops_1(X0,u1_struct_0(X0)) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k1_xboole_0)) ) ),
    inference(forward_demodulation,[],[f259,f270])).

fof(f259,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | k1_tops_1(X0,u1_struct_0(X0)) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    inference(resolution,[],[f53,f107])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).

fof(f529,plain,
    ( ~ spl4_50
    | spl4_8
    | ~ spl4_23 ),
    inference(avatar_split_clause,[],[f520,f290,f118,f526])).

fof(f526,plain,
    ( spl4_50
  <=> r1_tarski(sK1,k1_tops_1(sK0,u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_50])])).

fof(f118,plain,
    ( spl4_8
  <=> m2_connsp_2(u1_struct_0(sK0),sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f290,plain,
    ( spl4_23
  <=> ! [X6] :
        ( ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
        | m2_connsp_2(X6,sK0,sK1)
        | ~ r1_tarski(sK1,k1_tops_1(sK0,X6)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f520,plain,
    ( m2_connsp_2(u1_struct_0(sK0),sK0,sK1)
    | ~ r1_tarski(sK1,k1_tops_1(sK0,u1_struct_0(sK0)))
    | ~ spl4_23 ),
    inference(resolution,[],[f291,f107])).

fof(f291,plain,
    ( ! [X6] :
        ( ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
        | m2_connsp_2(X6,sK0,sK1)
        | ~ r1_tarski(sK1,k1_tops_1(sK0,X6)) )
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f290])).

fof(f438,plain,
    ( spl4_43
    | ~ spl4_1
    | ~ spl4_25 ),
    inference(avatar_split_clause,[],[f433,f311,f77,f435])).

fof(f311,plain,
    ( spl4_25
  <=> v4_pre_topc(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f433,plain,
    ( ~ l1_pre_topc(sK0)
    | k1_xboole_0 = k2_pre_topc(sK0,k1_xboole_0)
    | ~ spl4_25 ),
    inference(resolution,[],[f213,f313])).

fof(f313,plain,
    ( v4_pre_topc(k1_xboole_0,sK0)
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f311])).

fof(f213,plain,(
    ! [X1] :
      ( ~ v4_pre_topc(k1_xboole_0,X1)
      | ~ l1_pre_topc(X1)
      | k1_xboole_0 = k2_pre_topc(X1,k1_xboole_0) ) ),
    inference(resolution,[],[f55,f49])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

fof(f314,plain,
    ( spl4_25
    | ~ spl4_2
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f309,f77,f82,f311])).

fof(f82,plain,
    ( spl4_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f309,plain,
    ( ~ v2_pre_topc(sK0)
    | v4_pre_topc(k1_xboole_0,sK0)
    | ~ spl4_1 ),
    inference(resolution,[],[f197,f79])).

fof(f197,plain,(
    ! [X1] :
      ( ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v4_pre_topc(k1_xboole_0,X1) ) ),
    inference(global_subsumption,[],[f47,f193])).

fof(f193,plain,(
    ! [X1] :
      ( ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ v1_xboole_0(k1_xboole_0)
      | v4_pre_topc(k1_xboole_0,X1) ) ),
    inference(resolution,[],[f56,f49])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ v1_xboole_0(X1)
      | v4_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_xboole_0(X1)
           => v4_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_pre_topc)).

fof(f47,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f292,plain,
    ( spl4_23
    | ~ spl4_2
    | ~ spl4_1
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f288,f92,f77,f82,f290])).

fof(f92,plain,
    ( spl4_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f288,plain,
    ( ! [X6] :
        ( ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(sK1,k1_tops_1(sK0,X6))
        | m2_connsp_2(X6,sK0,sK1) )
    | ~ spl4_4 ),
    inference(resolution,[],[f57,f94])).

fof(f94,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f92])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X1,k1_tops_1(X0,X2))
      | m2_connsp_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m2_connsp_2(X2,X0,X1)
              <=> r1_tarski(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m2_connsp_2(X2,X0,X1)
              <=> r1_tarski(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m2_connsp_2(X2,X0,X1)
              <=> r1_tarski(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_connsp_2)).

fof(f129,plain,
    ( spl4_9
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f123,f92,f126])).

fof(f126,plain,
    ( spl4_9
  <=> r1_tarski(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f123,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl4_4 ),
    inference(resolution,[],[f71,f94])).

fof(f121,plain,
    ( ~ spl4_8
    | spl4_3
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f116,f111,f87,f118])).

fof(f87,plain,
    ( spl4_3
  <=> m2_connsp_2(k2_struct_0(sK0),sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f111,plain,
    ( spl4_7
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f116,plain,
    ( ~ m2_connsp_2(u1_struct_0(sK0),sK0,sK1)
    | spl4_3
    | ~ spl4_7 ),
    inference(backward_demodulation,[],[f89,f113])).

fof(f113,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f111])).

fof(f89,plain,
    ( ~ m2_connsp_2(k2_struct_0(sK0),sK0,sK1)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f87])).

fof(f114,plain,
    ( spl4_7
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f109,f103,f111])).

fof(f103,plain,
    ( spl4_6
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f109,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl4_6 ),
    inference(resolution,[],[f51,f105])).

fof(f105,plain,
    ( l1_struct_0(sK0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f103])).

fof(f51,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | u1_struct_0(X0) = k2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f106,plain,
    ( spl4_6
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f101,f77,f103])).

fof(f101,plain,
    ( l1_struct_0(sK0)
    | ~ spl4_1 ),
    inference(resolution,[],[f52,f79])).

fof(f52,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f95,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f43,f92])).

fof(f43,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ m2_connsp_2(k2_struct_0(X0),X0,X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ m2_connsp_2(k2_struct_0(X0),X0,X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => m2_connsp_2(k2_struct_0(X0),X0,X1) ) ) ),
    inference(pure_predicate_removal,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => m2_connsp_2(k2_struct_0(X0),X0,X1) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => m2_connsp_2(k2_struct_0(X0),X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_connsp_2)).

fof(f90,plain,(
    ~ spl4_3 ),
    inference(avatar_split_clause,[],[f44,f87])).

fof(f44,plain,(
    ~ m2_connsp_2(k2_struct_0(sK0),sK0,sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f85,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f45,f82])).

fof(f45,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f80,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f46,f77])).

fof(f46,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:37:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (4241)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (4230)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.51  % (4254)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.51  % (4256)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.51  % (4234)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (4233)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (4246)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.52  % (4242)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.53  % (4240)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (4239)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.53  % (4232)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (4240)Refutation not found, incomplete strategy% (4240)------------------------------
% 0.21/0.53  % (4240)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (4240)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (4240)Memory used [KB]: 10746
% 0.21/0.53  % (4240)Time elapsed: 0.132 s
% 0.21/0.53  % (4240)------------------------------
% 0.21/0.53  % (4240)------------------------------
% 0.21/0.53  % (4237)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.53  % (4250)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.53  % (4252)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (4253)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.53  % (4231)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (4229)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (4251)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.54  % (4255)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  % (4243)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.54  % (4258)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  % (4257)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (4239)Refutation not found, incomplete strategy% (4239)------------------------------
% 0.21/0.54  % (4239)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (4245)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.54  % (4244)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.54  % (4248)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.54  % (4236)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.54  % (4235)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.55  % (4247)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.55  % (4239)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (4239)Memory used [KB]: 10618
% 0.21/0.55  % (4239)Time elapsed: 0.142 s
% 0.21/0.55  % (4239)------------------------------
% 0.21/0.55  % (4239)------------------------------
% 0.21/0.55  % (4238)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.55  % (4249)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.57  % (4245)Refutation found. Thanks to Tanya!
% 0.21/0.57  % SZS status Theorem for theBenchmark
% 0.21/0.58  % SZS output start Proof for theBenchmark
% 0.21/0.58  fof(f618,plain,(
% 0.21/0.58    $false),
% 0.21/0.58    inference(avatar_sat_refutation,[],[f80,f85,f90,f95,f106,f114,f121,f129,f292,f314,f438,f529,f616,f617])).
% 0.21/0.58  fof(f617,plain,(
% 0.21/0.58    u1_struct_0(sK0) != k1_tops_1(sK0,u1_struct_0(sK0)) | ~r1_tarski(sK1,u1_struct_0(sK0)) | r1_tarski(sK1,k1_tops_1(sK0,u1_struct_0(sK0)))),
% 0.21/0.58    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.58  fof(f616,plain,(
% 0.21/0.58    spl4_65 | ~spl4_1 | ~spl4_43),
% 0.21/0.58    inference(avatar_split_clause,[],[f611,f435,f77,f613])).
% 0.21/0.58  fof(f613,plain,(
% 0.21/0.58    spl4_65 <=> u1_struct_0(sK0) = k1_tops_1(sK0,u1_struct_0(sK0))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_65])])).
% 0.21/0.58  fof(f77,plain,(
% 0.21/0.58    spl4_1 <=> l1_pre_topc(sK0)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.58  fof(f435,plain,(
% 0.21/0.58    spl4_43 <=> k1_xboole_0 = k2_pre_topc(sK0,k1_xboole_0)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).
% 0.21/0.58  fof(f611,plain,(
% 0.21/0.58    u1_struct_0(sK0) = k1_tops_1(sK0,u1_struct_0(sK0)) | (~spl4_1 | ~spl4_43)),
% 0.21/0.58    inference(forward_demodulation,[],[f610,f303])).
% 0.21/0.58  fof(f303,plain,(
% 0.21/0.58    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 0.21/0.58    inference(forward_demodulation,[],[f179,f270])).
% 0.21/0.58  fof(f270,plain,(
% 0.21/0.58    ( ! [X1] : (k1_xboole_0 = k3_subset_1(X1,X1)) )),
% 0.21/0.58    inference(resolution,[],[f245,f137])).
% 0.21/0.58  fof(f137,plain,(
% 0.21/0.58    ( ! [X1] : (~r1_tarski(X1,k1_xboole_0) | k1_xboole_0 = X1) )),
% 0.21/0.58    inference(resolution,[],[f66,f122])).
% 0.21/0.58  fof(f122,plain,(
% 0.21/0.58    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.58    inference(resolution,[],[f71,f49])).
% 0.21/0.58  fof(f49,plain,(
% 0.21/0.58    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.21/0.58    inference(cnf_transformation,[],[f11])).
% 0.21/0.58  fof(f11,axiom,(
% 0.21/0.58    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.21/0.58  fof(f71,plain,(
% 0.21/0.58    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f12])).
% 0.21/0.58  fof(f12,axiom,(
% 0.21/0.58    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.58  fof(f66,plain,(
% 0.21/0.58    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.21/0.58    inference(cnf_transformation,[],[f4])).
% 0.21/0.58  fof(f4,axiom,(
% 0.21/0.58    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.58  fof(f245,plain,(
% 0.21/0.58    ( ! [X0] : (r1_tarski(k3_subset_1(X0,X0),k1_xboole_0)) )),
% 0.21/0.58    inference(global_subsumption,[],[f49,f107,f240])).
% 0.21/0.58  fof(f240,plain,(
% 0.21/0.58    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(X0)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) | r1_tarski(k3_subset_1(X0,X0),k1_xboole_0)) )),
% 0.21/0.58    inference(resolution,[],[f63,f165])).
% 0.21/0.58  fof(f165,plain,(
% 0.21/0.58    ( ! [X1] : (r1_tarski(k3_subset_1(X1,k1_xboole_0),X1)) )),
% 0.21/0.58    inference(resolution,[],[f156,f71])).
% 0.21/0.58  fof(f156,plain,(
% 0.21/0.58    ( ! [X0] : (m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0))) )),
% 0.21/0.58    inference(resolution,[],[f61,f49])).
% 0.21/0.58  fof(f61,plain,(
% 0.21/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 0.21/0.58    inference(cnf_transformation,[],[f34])).
% 0.21/0.58  fof(f34,plain,(
% 0.21/0.58    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.58    inference(ennf_transformation,[],[f8])).
% 0.21/0.58  fof(f8,axiom,(
% 0.21/0.58    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 0.21/0.58  fof(f63,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (~r1_tarski(k3_subset_1(X0,X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | r1_tarski(k3_subset_1(X0,X2),X1)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f37])).
% 0.21/0.58  fof(f37,plain,(
% 0.21/0.58    ! [X0,X1] : (! [X2] : (r1_tarski(k3_subset_1(X0,X2),X1) | ~r1_tarski(k3_subset_1(X0,X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.58    inference(flattening,[],[f36])).
% 0.21/0.58  fof(f36,plain,(
% 0.21/0.58    ! [X0,X1] : (! [X2] : ((r1_tarski(k3_subset_1(X0,X2),X1) | ~r1_tarski(k3_subset_1(X0,X1),X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.58    inference(ennf_transformation,[],[f10])).
% 0.21/0.58  fof(f10,axiom,(
% 0.21/0.58    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X2) => r1_tarski(k3_subset_1(X0,X2),X1))))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_subset_1)).
% 0.21/0.58  fof(f107,plain,(
% 0.21/0.58    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.21/0.58    inference(forward_demodulation,[],[f50,f48])).
% 0.21/0.58  fof(f48,plain,(
% 0.21/0.58    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.21/0.58    inference(cnf_transformation,[],[f6])).
% 0.21/0.58  fof(f6,axiom,(
% 0.21/0.58    ! [X0] : k2_subset_1(X0) = X0),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 0.21/0.58  fof(f50,plain,(
% 0.21/0.58    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.21/0.58    inference(cnf_transformation,[],[f7])).
% 0.21/0.58  fof(f7,axiom,(
% 0.21/0.58    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.21/0.58  fof(f179,plain,(
% 0.21/0.58    ( ! [X0] : (k3_subset_1(X0,k3_subset_1(X0,X0)) = X0) )),
% 0.21/0.58    inference(resolution,[],[f62,f107])).
% 0.21/0.58  fof(f62,plain,(
% 0.21/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 0.21/0.58    inference(cnf_transformation,[],[f35])).
% 0.21/0.58  fof(f35,plain,(
% 0.21/0.58    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.58    inference(ennf_transformation,[],[f9])).
% 0.21/0.58  fof(f9,axiom,(
% 0.21/0.58    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 0.21/0.58  fof(f610,plain,(
% 0.21/0.58    k1_tops_1(sK0,u1_struct_0(sK0)) = k3_subset_1(u1_struct_0(sK0),k1_xboole_0) | (~spl4_1 | ~spl4_43)),
% 0.21/0.58    inference(forward_demodulation,[],[f609,f437])).
% 0.21/0.58  fof(f437,plain,(
% 0.21/0.58    k1_xboole_0 = k2_pre_topc(sK0,k1_xboole_0) | ~spl4_43),
% 0.21/0.58    inference(avatar_component_clause,[],[f435])).
% 0.21/0.58  fof(f609,plain,(
% 0.21/0.58    k1_tops_1(sK0,u1_struct_0(sK0)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k1_xboole_0)) | ~spl4_1),
% 0.21/0.58    inference(resolution,[],[f608,f79])).
% 0.21/0.58  fof(f79,plain,(
% 0.21/0.58    l1_pre_topc(sK0) | ~spl4_1),
% 0.21/0.58    inference(avatar_component_clause,[],[f77])).
% 0.21/0.58  fof(f608,plain,(
% 0.21/0.58    ( ! [X0] : (~l1_pre_topc(X0) | k1_tops_1(X0,u1_struct_0(X0)) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k1_xboole_0))) )),
% 0.21/0.58    inference(forward_demodulation,[],[f259,f270])).
% 0.21/0.58  fof(f259,plain,(
% 0.21/0.58    ( ! [X0] : (~l1_pre_topc(X0) | k1_tops_1(X0,u1_struct_0(X0)) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),u1_struct_0(X0))))) )),
% 0.21/0.58    inference(resolution,[],[f53,f107])).
% 0.21/0.58  fof(f53,plain,(
% 0.21/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))) )),
% 0.21/0.58    inference(cnf_transformation,[],[f27])).
% 0.21/0.58  fof(f27,plain,(
% 0.21/0.58    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.58    inference(ennf_transformation,[],[f18])).
% 0.21/0.58  fof(f18,axiom,(
% 0.21/0.58    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).
% 0.21/0.58  fof(f529,plain,(
% 0.21/0.58    ~spl4_50 | spl4_8 | ~spl4_23),
% 0.21/0.58    inference(avatar_split_clause,[],[f520,f290,f118,f526])).
% 0.21/0.58  fof(f526,plain,(
% 0.21/0.58    spl4_50 <=> r1_tarski(sK1,k1_tops_1(sK0,u1_struct_0(sK0)))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_50])])).
% 0.21/0.58  fof(f118,plain,(
% 0.21/0.58    spl4_8 <=> m2_connsp_2(u1_struct_0(sK0),sK0,sK1)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.58  fof(f290,plain,(
% 0.21/0.58    spl4_23 <=> ! [X6] : (~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0))) | m2_connsp_2(X6,sK0,sK1) | ~r1_tarski(sK1,k1_tops_1(sK0,X6)))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 0.21/0.58  fof(f520,plain,(
% 0.21/0.58    m2_connsp_2(u1_struct_0(sK0),sK0,sK1) | ~r1_tarski(sK1,k1_tops_1(sK0,u1_struct_0(sK0))) | ~spl4_23),
% 0.21/0.58    inference(resolution,[],[f291,f107])).
% 0.21/0.58  fof(f291,plain,(
% 0.21/0.58    ( ! [X6] : (~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0))) | m2_connsp_2(X6,sK0,sK1) | ~r1_tarski(sK1,k1_tops_1(sK0,X6))) ) | ~spl4_23),
% 0.21/0.58    inference(avatar_component_clause,[],[f290])).
% 0.21/0.58  fof(f438,plain,(
% 0.21/0.58    spl4_43 | ~spl4_1 | ~spl4_25),
% 0.21/0.58    inference(avatar_split_clause,[],[f433,f311,f77,f435])).
% 0.21/0.58  fof(f311,plain,(
% 0.21/0.58    spl4_25 <=> v4_pre_topc(k1_xboole_0,sK0)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 0.21/0.58  fof(f433,plain,(
% 0.21/0.58    ~l1_pre_topc(sK0) | k1_xboole_0 = k2_pre_topc(sK0,k1_xboole_0) | ~spl4_25),
% 0.21/0.58    inference(resolution,[],[f213,f313])).
% 0.21/0.58  fof(f313,plain,(
% 0.21/0.58    v4_pre_topc(k1_xboole_0,sK0) | ~spl4_25),
% 0.21/0.58    inference(avatar_component_clause,[],[f311])).
% 0.21/0.58  fof(f213,plain,(
% 0.21/0.58    ( ! [X1] : (~v4_pre_topc(k1_xboole_0,X1) | ~l1_pre_topc(X1) | k1_xboole_0 = k2_pre_topc(X1,k1_xboole_0)) )),
% 0.21/0.58    inference(resolution,[],[f55,f49])).
% 0.21/0.58  fof(f55,plain,(
% 0.21/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) = X1) )),
% 0.21/0.58    inference(cnf_transformation,[],[f29])).
% 0.21/0.58  fof(f29,plain,(
% 0.21/0.58    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.58    inference(flattening,[],[f28])).
% 0.21/0.58  fof(f28,plain,(
% 0.21/0.58    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.58    inference(ennf_transformation,[],[f17])).
% 0.21/0.58  fof(f17,axiom,(
% 0.21/0.58    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).
% 0.21/0.58  fof(f314,plain,(
% 0.21/0.58    spl4_25 | ~spl4_2 | ~spl4_1),
% 0.21/0.58    inference(avatar_split_clause,[],[f309,f77,f82,f311])).
% 0.21/0.58  fof(f82,plain,(
% 0.21/0.58    spl4_2 <=> v2_pre_topc(sK0)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.58  fof(f309,plain,(
% 0.21/0.58    ~v2_pre_topc(sK0) | v4_pre_topc(k1_xboole_0,sK0) | ~spl4_1),
% 0.21/0.58    inference(resolution,[],[f197,f79])).
% 0.21/0.58  fof(f197,plain,(
% 0.21/0.58    ( ! [X1] : (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v4_pre_topc(k1_xboole_0,X1)) )),
% 0.21/0.58    inference(global_subsumption,[],[f47,f193])).
% 0.21/0.58  fof(f193,plain,(
% 0.21/0.58    ( ! [X1] : (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~v1_xboole_0(k1_xboole_0) | v4_pre_topc(k1_xboole_0,X1)) )),
% 0.21/0.58    inference(resolution,[],[f56,f49])).
% 0.21/0.58  fof(f56,plain,(
% 0.21/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~v1_xboole_0(X1) | v4_pre_topc(X1,X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f31])).
% 0.21/0.58  fof(f31,plain,(
% 0.21/0.58    ! [X0] : (! [X1] : (v4_pre_topc(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.58    inference(flattening,[],[f30])).
% 0.21/0.58  fof(f30,plain,(
% 0.21/0.58    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) | ~v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.58    inference(ennf_transformation,[],[f14])).
% 0.21/0.58  fof(f14,axiom,(
% 0.21/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_xboole_0(X1) => v4_pre_topc(X1,X0))))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_pre_topc)).
% 0.21/0.58  fof(f47,plain,(
% 0.21/0.58    v1_xboole_0(k1_xboole_0)),
% 0.21/0.58    inference(cnf_transformation,[],[f3])).
% 0.21/0.58  fof(f3,axiom,(
% 0.21/0.58    v1_xboole_0(k1_xboole_0)),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.58  fof(f292,plain,(
% 0.21/0.58    spl4_23 | ~spl4_2 | ~spl4_1 | ~spl4_4),
% 0.21/0.58    inference(avatar_split_clause,[],[f288,f92,f77,f82,f290])).
% 0.21/0.58  fof(f92,plain,(
% 0.21/0.58    spl4_4 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.58  fof(f288,plain,(
% 0.21/0.58    ( ! [X6] : (~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(sK1,k1_tops_1(sK0,X6)) | m2_connsp_2(X6,sK0,sK1)) ) | ~spl4_4),
% 0.21/0.58    inference(resolution,[],[f57,f94])).
% 0.21/0.58  fof(f94,plain,(
% 0.21/0.58    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_4),
% 0.21/0.58    inference(avatar_component_clause,[],[f92])).
% 0.21/0.58  fof(f57,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X1,k1_tops_1(X0,X2)) | m2_connsp_2(X2,X0,X1)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f33])).
% 0.21/0.58  fof(f33,plain,(
% 0.21/0.58    ! [X0] : (! [X1] : (! [X2] : ((m2_connsp_2(X2,X0,X1) <=> r1_tarski(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.58    inference(flattening,[],[f32])).
% 0.21/0.58  fof(f32,plain,(
% 0.21/0.58    ! [X0] : (! [X1] : (! [X2] : ((m2_connsp_2(X2,X0,X1) <=> r1_tarski(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.58    inference(ennf_transformation,[],[f19])).
% 0.21/0.58  fof(f19,axiom,(
% 0.21/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m2_connsp_2(X2,X0,X1) <=> r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_connsp_2)).
% 0.21/0.58  fof(f129,plain,(
% 0.21/0.58    spl4_9 | ~spl4_4),
% 0.21/0.58    inference(avatar_split_clause,[],[f123,f92,f126])).
% 0.21/0.58  fof(f126,plain,(
% 0.21/0.58    spl4_9 <=> r1_tarski(sK1,u1_struct_0(sK0))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.58  fof(f123,plain,(
% 0.21/0.58    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl4_4),
% 0.21/0.58    inference(resolution,[],[f71,f94])).
% 0.21/0.58  fof(f121,plain,(
% 0.21/0.58    ~spl4_8 | spl4_3 | ~spl4_7),
% 0.21/0.58    inference(avatar_split_clause,[],[f116,f111,f87,f118])).
% 0.21/0.58  fof(f87,plain,(
% 0.21/0.58    spl4_3 <=> m2_connsp_2(k2_struct_0(sK0),sK0,sK1)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.58  fof(f111,plain,(
% 0.21/0.58    spl4_7 <=> u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.58  fof(f116,plain,(
% 0.21/0.58    ~m2_connsp_2(u1_struct_0(sK0),sK0,sK1) | (spl4_3 | ~spl4_7)),
% 0.21/0.58    inference(backward_demodulation,[],[f89,f113])).
% 0.21/0.58  fof(f113,plain,(
% 0.21/0.58    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl4_7),
% 0.21/0.58    inference(avatar_component_clause,[],[f111])).
% 0.21/0.58  fof(f89,plain,(
% 0.21/0.58    ~m2_connsp_2(k2_struct_0(sK0),sK0,sK1) | spl4_3),
% 0.21/0.58    inference(avatar_component_clause,[],[f87])).
% 0.21/0.58  fof(f114,plain,(
% 0.21/0.58    spl4_7 | ~spl4_6),
% 0.21/0.58    inference(avatar_split_clause,[],[f109,f103,f111])).
% 0.21/0.58  fof(f103,plain,(
% 0.21/0.58    spl4_6 <=> l1_struct_0(sK0)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.58  fof(f109,plain,(
% 0.21/0.58    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl4_6),
% 0.21/0.58    inference(resolution,[],[f51,f105])).
% 0.21/0.58  fof(f105,plain,(
% 0.21/0.58    l1_struct_0(sK0) | ~spl4_6),
% 0.21/0.58    inference(avatar_component_clause,[],[f103])).
% 0.21/0.58  fof(f51,plain,(
% 0.21/0.58    ( ! [X0] : (~l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f25])).
% 0.21/0.58  fof(f25,plain,(
% 0.21/0.58    ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0))),
% 0.21/0.58    inference(ennf_transformation,[],[f15])).
% 0.21/0.58  fof(f15,axiom,(
% 0.21/0.58    ! [X0] : (l1_struct_0(X0) => u1_struct_0(X0) = k2_struct_0(X0))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.21/0.58  fof(f106,plain,(
% 0.21/0.58    spl4_6 | ~spl4_1),
% 0.21/0.58    inference(avatar_split_clause,[],[f101,f77,f103])).
% 0.21/0.58  fof(f101,plain,(
% 0.21/0.58    l1_struct_0(sK0) | ~spl4_1),
% 0.21/0.58    inference(resolution,[],[f52,f79])).
% 0.21/0.58  fof(f52,plain,(
% 0.21/0.58    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f26])).
% 0.21/0.58  fof(f26,plain,(
% 0.21/0.58    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.58    inference(ennf_transformation,[],[f16])).
% 0.21/0.58  fof(f16,axiom,(
% 0.21/0.58    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.58  fof(f95,plain,(
% 0.21/0.58    spl4_4),
% 0.21/0.58    inference(avatar_split_clause,[],[f43,f92])).
% 0.21/0.58  fof(f43,plain,(
% 0.21/0.58    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.58    inference(cnf_transformation,[],[f24])).
% 0.21/0.58  fof(f24,plain,(
% 0.21/0.58    ? [X0] : (? [X1] : (~m2_connsp_2(k2_struct_0(X0),X0,X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.58    inference(flattening,[],[f23])).
% 0.21/0.58  fof(f23,plain,(
% 0.21/0.58    ? [X0] : (? [X1] : (~m2_connsp_2(k2_struct_0(X0),X0,X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.21/0.58    inference(ennf_transformation,[],[f22])).
% 0.21/0.58  fof(f22,plain,(
% 0.21/0.58    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => m2_connsp_2(k2_struct_0(X0),X0,X1)))),
% 0.21/0.58    inference(pure_predicate_removal,[],[f21])).
% 0.21/0.58  fof(f21,negated_conjecture,(
% 0.21/0.58    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => m2_connsp_2(k2_struct_0(X0),X0,X1)))),
% 0.21/0.58    inference(negated_conjecture,[],[f20])).
% 0.21/0.58  fof(f20,conjecture,(
% 0.21/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => m2_connsp_2(k2_struct_0(X0),X0,X1)))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_connsp_2)).
% 0.21/0.58  fof(f90,plain,(
% 0.21/0.58    ~spl4_3),
% 0.21/0.58    inference(avatar_split_clause,[],[f44,f87])).
% 0.21/0.58  fof(f44,plain,(
% 0.21/0.58    ~m2_connsp_2(k2_struct_0(sK0),sK0,sK1)),
% 0.21/0.58    inference(cnf_transformation,[],[f24])).
% 0.21/0.58  fof(f85,plain,(
% 0.21/0.58    spl4_2),
% 0.21/0.58    inference(avatar_split_clause,[],[f45,f82])).
% 0.21/0.58  fof(f45,plain,(
% 0.21/0.58    v2_pre_topc(sK0)),
% 0.21/0.58    inference(cnf_transformation,[],[f24])).
% 0.21/0.58  fof(f80,plain,(
% 0.21/0.58    spl4_1),
% 0.21/0.58    inference(avatar_split_clause,[],[f46,f77])).
% 0.21/0.58  fof(f46,plain,(
% 0.21/0.58    l1_pre_topc(sK0)),
% 0.21/0.58    inference(cnf_transformation,[],[f24])).
% 0.21/0.58  % SZS output end Proof for theBenchmark
% 0.21/0.58  % (4245)------------------------------
% 0.21/0.58  % (4245)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (4245)Termination reason: Refutation
% 0.21/0.58  
% 0.21/0.58  % (4245)Memory used [KB]: 11129
% 0.21/0.58  % (4245)Time elapsed: 0.174 s
% 0.21/0.58  % (4245)------------------------------
% 0.21/0.58  % (4245)------------------------------
% 0.21/0.59  % (4228)Success in time 0.228 s
%------------------------------------------------------------------------------
