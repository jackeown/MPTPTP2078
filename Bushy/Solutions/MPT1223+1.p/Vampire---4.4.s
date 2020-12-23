%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tops_1__t31_tops_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:27 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  332 (1034 expanded)
%              Number of leaves         :   94 ( 417 expanded)
%              Depth                    :   13
%              Number of atoms          :  960 (2916 expanded)
%              Number of equality atoms :   43 ( 116 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f796,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f90,f97,f104,f111,f118,f125,f132,f139,f146,f157,f164,f196,f209,f222,f232,f234,f246,f256,f269,f274,f284,f295,f305,f315,f330,f334,f357,f370,f377,f394,f395,f409,f425,f435,f452,f454,f461,f473,f474,f488,f501,f528,f544,f551,f566,f594,f595,f639,f664,f672,f677,f684,f706,f711,f726,f745,f755,f756,f758,f781,f789,f795])).

fof(f795,plain,
    ( ~ spl5_0
    | ~ spl5_8
    | ~ spl5_12
    | ~ spl5_14
    | spl5_17
    | ~ spl5_66 ),
    inference(avatar_contradiction_clause,[],[f794])).

fof(f794,plain,
    ( $false
    | ~ spl5_0
    | ~ spl5_8
    | ~ spl5_12
    | ~ spl5_14
    | ~ spl5_17
    | ~ spl5_66 ),
    inference(subsumption_resolution,[],[f793,f145])).

fof(f145,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,sK2),sK1)
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f144])).

fof(f144,plain,
    ( spl5_17
  <=> ~ r1_tarski(k2_pre_topc(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f793,plain,
    ( r1_tarski(k2_pre_topc(sK0,sK2),sK1)
    | ~ spl5_0
    | ~ spl5_8
    | ~ spl5_12
    | ~ spl5_14
    | ~ spl5_66 ),
    inference(forward_demodulation,[],[f792,f376])).

fof(f376,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | ~ spl5_66 ),
    inference(avatar_component_clause,[],[f375])).

fof(f375,plain,
    ( spl5_66
  <=> k2_pre_topc(sK0,sK1) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_66])])).

fof(f792,plain,
    ( r1_tarski(k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,sK1))
    | ~ spl5_0
    | ~ spl5_8
    | ~ spl5_12
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f790,f131])).

fof(f131,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f130])).

fof(f130,plain,
    ( spl5_12
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f790,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,sK1))
    | ~ spl5_0
    | ~ spl5_8
    | ~ spl5_14 ),
    inference(resolution,[],[f763,f117])).

fof(f117,plain,
    ( r1_tarski(sK2,sK1)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl5_8
  <=> r1_tarski(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f763,plain,
    ( ! [X5] :
        ( ~ r1_tarski(sK2,X5)
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,X5)) )
    | ~ spl5_0
    | ~ spl5_14 ),
    inference(resolution,[],[f514,f138])).

fof(f138,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f137])).

fof(f137,plain,
    ( spl5_14
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f514,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X0,X1)
        | r1_tarski(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,X1)) )
    | ~ spl5_0 ),
    inference(resolution,[],[f69,f89])).

fof(f89,plain,
    ( l1_pre_topc(sK0)
    | ~ spl5_0 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl5_0
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_0])])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) ) ),
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
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t31_tops_1.p',t49_pre_topc)).

fof(f789,plain,
    ( ~ spl5_133
    | spl5_131 ),
    inference(avatar_split_clause,[],[f782,f779,f787])).

fof(f787,plain,
    ( spl5_133
  <=> ~ r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_133])])).

fof(f779,plain,
    ( spl5_131
  <=> ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_131])])).

fof(f782,plain,
    ( ~ r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ spl5_131 ),
    inference(resolution,[],[f780,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
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
    file('/export/starexec/sandbox2/benchmark/tops_1__t31_tops_1.p',t3_subset)).

fof(f780,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_131 ),
    inference(avatar_component_clause,[],[f779])).

fof(f781,plain,
    ( spl5_128
    | ~ spl5_131
    | ~ spl5_0
    | ~ spl5_12
    | ~ spl5_18
    | ~ spl5_66 ),
    inference(avatar_split_clause,[],[f768,f375,f155,f130,f88,f779,f773])).

fof(f773,plain,
    ( spl5_128
  <=> r1_tarski(sK1,k2_pre_topc(sK0,u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_128])])).

fof(f155,plain,
    ( spl5_18
  <=> r1_tarski(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f768,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK1,k2_pre_topc(sK0,u1_struct_0(sK0)))
    | ~ spl5_0
    | ~ spl5_12
    | ~ spl5_18
    | ~ spl5_66 ),
    inference(resolution,[],[f767,f156])).

fof(f156,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f155])).

fof(f767,plain,
    ( ! [X4] :
        ( ~ r1_tarski(sK1,X4)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(sK1,k2_pre_topc(sK0,X4)) )
    | ~ spl5_0
    | ~ spl5_12
    | ~ spl5_66 ),
    inference(forward_demodulation,[],[f762,f376])).

fof(f762,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(sK1,X4)
        | r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,X4)) )
    | ~ spl5_0
    | ~ spl5_12 ),
    inference(resolution,[],[f514,f131])).

fof(f758,plain,
    ( ~ spl5_75
    | spl5_81 ),
    inference(avatar_split_clause,[],[f757,f456,f420])).

fof(f420,plain,
    ( spl5_75
  <=> ~ r1_tarski(k1_xboole_0,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_75])])).

fof(f456,plain,
    ( spl5_81
  <=> ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_81])])).

fof(f757,plain,
    ( ~ r1_tarski(k1_xboole_0,u1_struct_0(sK0))
    | ~ spl5_81 ),
    inference(resolution,[],[f457,f77])).

fof(f457,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_81 ),
    inference(avatar_component_clause,[],[f456])).

fof(f756,plain,
    ( ~ spl5_81
    | ~ spl5_0
    | spl5_121 ),
    inference(avatar_split_clause,[],[f748,f731,f88,f456])).

fof(f731,plain,
    ( spl5_121
  <=> ~ m1_subset_1(k2_pre_topc(sK0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_121])])).

fof(f748,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_0
    | ~ spl5_121 ),
    inference(subsumption_resolution,[],[f746,f89])).

fof(f746,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl5_121 ),
    inference(resolution,[],[f732,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t31_tops_1.p',dt_k2_pre_topc)).

fof(f732,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_121 ),
    inference(avatar_component_clause,[],[f731])).

fof(f755,plain,
    ( ~ spl5_127
    | spl5_121 ),
    inference(avatar_split_clause,[],[f747,f731,f753])).

fof(f753,plain,
    ( spl5_127
  <=> ~ r1_tarski(k2_pre_topc(sK0,k1_xboole_0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_127])])).

fof(f747,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k1_xboole_0),u1_struct_0(sK0))
    | ~ spl5_121 ),
    inference(resolution,[],[f732,f77])).

fof(f745,plain,
    ( ~ spl5_121
    | spl5_122
    | spl5_124
    | ~ spl5_0
    | ~ spl5_86 ),
    inference(avatar_split_clause,[],[f682,f499,f88,f743,f737,f731])).

fof(f737,plain,
    ( spl5_122
  <=> m1_subset_1(sK3(k2_pre_topc(sK0,k1_xboole_0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_122])])).

fof(f743,plain,
    ( spl5_124
  <=> v1_xboole_0(k2_pre_topc(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_124])])).

fof(f499,plain,
    ( spl5_86
  <=> k2_pre_topc(sK0,k1_xboole_0) = k2_pre_topc(sK0,k2_pre_topc(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_86])])).

fof(f682,plain,
    ( v1_xboole_0(k2_pre_topc(sK0,k1_xboole_0))
    | m1_subset_1(sK3(k2_pre_topc(sK0,k1_xboole_0)),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_pre_topc(sK0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_0
    | ~ spl5_86 ),
    inference(forward_demodulation,[],[f678,f500])).

fof(f500,plain,
    ( k2_pre_topc(sK0,k1_xboole_0) = k2_pre_topc(sK0,k2_pre_topc(sK0,k1_xboole_0))
    | ~ spl5_86 ),
    inference(avatar_component_clause,[],[f499])).

fof(f678,plain,
    ( m1_subset_1(sK3(k2_pre_topc(sK0,k1_xboole_0)),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_pre_topc(sK0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(k2_pre_topc(sK0,k2_pre_topc(sK0,k1_xboole_0)))
    | ~ spl5_0
    | ~ spl5_86 ),
    inference(superposition,[],[f616,f500])).

fof(f616,plain,
    ( ! [X0] :
        ( m1_subset_1(sK3(k2_pre_topc(sK0,X0)),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(k2_pre_topc(sK0,X0)) )
    | ~ spl5_0 ),
    inference(resolution,[],[f571,f70])).

fof(f70,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f15,f54])).

fof(f54,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f15,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t31_tops_1.p',existence_m1_subset_1)).

fof(f571,plain,
    ( ! [X2,X1] :
        ( ~ m1_subset_1(X2,k2_pre_topc(sK0,X1))
        | v1_xboole_0(k2_pre_topc(sK0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | m1_subset_1(X2,u1_struct_0(sK0)) )
    | ~ spl5_0 ),
    inference(resolution,[],[f568,f260])).

fof(f260,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X1)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X0,X2)
      | m1_subset_1(X0,X1) ) ),
    inference(resolution,[],[f173,f77])).

fof(f173,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | m1_subset_1(X2,X1)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X2,X0) ) ),
    inference(resolution,[],[f80,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t31_tops_1.p',t2_subset)).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t31_tops_1.p',t4_subset)).

fof(f568,plain,
    ( ! [X0] :
        ( r1_tarski(k2_pre_topc(sK0,X0),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_0 ),
    inference(resolution,[],[f247,f89])).

fof(f247,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | r1_tarski(k2_pre_topc(X1,X0),u1_struct_0(X1)) ) ),
    inference(resolution,[],[f74,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f726,plain,
    ( ~ spl5_117
    | spl5_118
    | spl5_49
    | ~ spl5_112 ),
    inference(avatar_split_clause,[],[f713,f698,f287,f724,f718])).

fof(f718,plain,
    ( spl5_117
  <=> ~ m1_subset_1(u1_struct_0(sK0),sK3(k2_pre_topc(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_117])])).

fof(f724,plain,
    ( spl5_118
  <=> v1_xboole_0(sK3(k2_pre_topc(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_118])])).

fof(f287,plain,
    ( spl5_49
  <=> ~ v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_49])])).

fof(f698,plain,
    ( spl5_112
  <=> m1_subset_1(sK3(k2_pre_topc(sK0,sK2)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_112])])).

fof(f713,plain,
    ( v1_xboole_0(sK3(k2_pre_topc(sK0,sK2)))
    | ~ m1_subset_1(u1_struct_0(sK0),sK3(k2_pre_topc(sK0,sK2)))
    | ~ spl5_49
    | ~ spl5_112 ),
    inference(subsumption_resolution,[],[f712,f288])).

fof(f288,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl5_49 ),
    inference(avatar_component_clause,[],[f287])).

fof(f712,plain,
    ( v1_xboole_0(sK3(k2_pre_topc(sK0,sK2)))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ m1_subset_1(u1_struct_0(sK0),sK3(k2_pre_topc(sK0,sK2)))
    | ~ spl5_112 ),
    inference(resolution,[],[f699,f170])).

fof(f170,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(resolution,[],[f168,f73])).

fof(f168,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,X3)
      | ~ m1_subset_1(X3,X2)
      | v1_xboole_0(X2) ) ),
    inference(resolution,[],[f73,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t31_tops_1.p',antisymmetry_r2_hidden)).

fof(f699,plain,
    ( m1_subset_1(sK3(k2_pre_topc(sK0,sK2)),u1_struct_0(sK0))
    | ~ spl5_112 ),
    inference(avatar_component_clause,[],[f698])).

fof(f711,plain,
    ( ~ spl5_0
    | ~ spl5_14
    | spl5_111 ),
    inference(avatar_contradiction_clause,[],[f710])).

fof(f710,plain,
    ( $false
    | ~ spl5_0
    | ~ spl5_14
    | ~ spl5_111 ),
    inference(subsumption_resolution,[],[f709,f89])).

fof(f709,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl5_14
    | ~ spl5_111 ),
    inference(subsumption_resolution,[],[f707,f138])).

fof(f707,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl5_111 ),
    inference(resolution,[],[f693,f74])).

fof(f693,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_111 ),
    inference(avatar_component_clause,[],[f692])).

fof(f692,plain,
    ( spl5_111
  <=> ~ m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_111])])).

fof(f706,plain,
    ( ~ spl5_111
    | spl5_112
    | spl5_114
    | ~ spl5_0
    | ~ spl5_84 ),
    inference(avatar_split_clause,[],[f631,f486,f88,f704,f698,f692])).

fof(f704,plain,
    ( spl5_114
  <=> v1_xboole_0(k2_pre_topc(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_114])])).

fof(f486,plain,
    ( spl5_84
  <=> k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k2_pre_topc(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_84])])).

fof(f631,plain,
    ( v1_xboole_0(k2_pre_topc(sK0,sK2))
    | m1_subset_1(sK3(k2_pre_topc(sK0,sK2)),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_0
    | ~ spl5_84 ),
    inference(forward_demodulation,[],[f625,f487])).

fof(f487,plain,
    ( k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k2_pre_topc(sK0,sK2))
    | ~ spl5_84 ),
    inference(avatar_component_clause,[],[f486])).

fof(f625,plain,
    ( m1_subset_1(sK3(k2_pre_topc(sK0,sK2)),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(k2_pre_topc(sK0,k2_pre_topc(sK0,sK2)))
    | ~ spl5_0
    | ~ spl5_84 ),
    inference(superposition,[],[f616,f487])).

fof(f684,plain,
    ( spl5_42
    | spl5_26
    | ~ spl5_0
    | ~ spl5_12
    | ~ spl5_66 ),
    inference(avatar_split_clause,[],[f641,f375,f130,f88,f194,f267])).

fof(f267,plain,
    ( spl5_42
  <=> ! [X7] :
        ( m1_subset_1(X7,u1_struct_0(sK0))
        | ~ m1_subset_1(X7,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_42])])).

fof(f194,plain,
    ( spl5_26
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f641,plain,
    ( ! [X0] :
        ( v1_xboole_0(sK1)
        | ~ m1_subset_1(X0,sK1)
        | m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl5_0
    | ~ spl5_12
    | ~ spl5_66 ),
    inference(forward_demodulation,[],[f640,f376])).

fof(f640,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | v1_xboole_0(k2_pre_topc(sK0,sK1))
        | m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl5_0
    | ~ spl5_12
    | ~ spl5_66 ),
    inference(subsumption_resolution,[],[f618,f131])).

fof(f618,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | v1_xboole_0(k2_pre_topc(sK0,sK1))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl5_0
    | ~ spl5_66 ),
    inference(superposition,[],[f571,f376])).

fof(f677,plain,
    ( spl5_106
    | spl5_26
    | ~ spl5_0
    | ~ spl5_12
    | ~ spl5_66 ),
    inference(avatar_split_clause,[],[f629,f375,f130,f88,f194,f637])).

fof(f637,plain,
    ( spl5_106
  <=> m1_subset_1(sK3(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_106])])).

fof(f629,plain,
    ( v1_xboole_0(sK1)
    | m1_subset_1(sK3(sK1),u1_struct_0(sK0))
    | ~ spl5_0
    | ~ spl5_12
    | ~ spl5_66 ),
    inference(forward_demodulation,[],[f628,f376])).

fof(f628,plain,
    ( m1_subset_1(sK3(sK1),u1_struct_0(sK0))
    | v1_xboole_0(k2_pre_topc(sK0,sK1))
    | ~ spl5_0
    | ~ spl5_12
    | ~ spl5_66 ),
    inference(subsumption_resolution,[],[f624,f131])).

fof(f624,plain,
    ( m1_subset_1(sK3(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(k2_pre_topc(sK0,sK1))
    | ~ spl5_0
    | ~ spl5_66 ),
    inference(superposition,[],[f616,f376])).

fof(f672,plain,
    ( spl5_108
    | ~ spl5_6
    | ~ spl5_52 ),
    inference(avatar_split_clause,[],[f648,f303,f109,f670])).

fof(f670,plain,
    ( spl5_108
  <=> v4_pre_topc(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_108])])).

fof(f109,plain,
    ( spl5_6
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f303,plain,
    ( spl5_52
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_52])])).

fof(f648,plain,
    ( v4_pre_topc(k1_xboole_0,sK0)
    | ~ spl5_6
    | ~ spl5_52 ),
    inference(superposition,[],[f110,f304])).

fof(f304,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_52 ),
    inference(avatar_component_clause,[],[f303])).

fof(f110,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f109])).

fof(f664,plain,
    ( ~ spl5_52
    | spl5_79 ),
    inference(avatar_contradiction_clause,[],[f663])).

fof(f663,plain,
    ( $false
    | ~ spl5_52
    | ~ spl5_79 ),
    inference(subsumption_resolution,[],[f658,f70])).

fof(f658,plain,
    ( ~ m1_subset_1(sK3(k1_xboole_0),k1_xboole_0)
    | ~ spl5_52
    | ~ spl5_79 ),
    inference(superposition,[],[f448,f304])).

fof(f448,plain,
    ( ~ m1_subset_1(sK3(k1_xboole_0),sK1)
    | ~ spl5_79 ),
    inference(avatar_component_clause,[],[f447])).

fof(f447,plain,
    ( spl5_79
  <=> ~ m1_subset_1(sK3(k1_xboole_0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_79])])).

fof(f639,plain,
    ( spl5_106
    | ~ spl5_0
    | ~ spl5_12
    | spl5_27
    | ~ spl5_66 ),
    inference(avatar_split_clause,[],[f630,f375,f191,f130,f88,f637])).

fof(f191,plain,
    ( spl5_27
  <=> ~ v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f630,plain,
    ( m1_subset_1(sK3(sK1),u1_struct_0(sK0))
    | ~ spl5_0
    | ~ spl5_12
    | ~ spl5_27
    | ~ spl5_66 ),
    inference(subsumption_resolution,[],[f629,f192])).

fof(f192,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl5_27 ),
    inference(avatar_component_clause,[],[f191])).

fof(f595,plain,
    ( spl5_94
    | ~ spl5_97
    | spl5_90
    | ~ spl5_60 ),
    inference(avatar_split_clause,[],[f511,f332,f526,f549,f542])).

fof(f542,plain,
    ( spl5_94
  <=> v1_xboole_0(sK3(sK3(k1_zfmisc_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_94])])).

fof(f549,plain,
    ( spl5_97
  <=> ~ m1_subset_1(u1_struct_0(sK0),sK3(sK3(k1_zfmisc_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_97])])).

fof(f526,plain,
    ( spl5_90
  <=> v1_xboole_0(sK3(k1_zfmisc_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_90])])).

fof(f332,plain,
    ( spl5_60
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,sK2)
        | ~ m1_subset_1(u1_struct_0(sK0),X0)
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_60])])).

fof(f511,plain,
    ( v1_xboole_0(sK3(k1_zfmisc_1(sK2)))
    | ~ m1_subset_1(u1_struct_0(sK0),sK3(sK3(k1_zfmisc_1(sK2))))
    | v1_xboole_0(sK3(sK3(k1_zfmisc_1(sK2))))
    | ~ spl5_60 ),
    inference(resolution,[],[f502,f333])).

fof(f333,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK2)
        | ~ m1_subset_1(u1_struct_0(sK0),X0)
        | v1_xboole_0(X0) )
    | ~ spl5_60 ),
    inference(avatar_component_clause,[],[f332])).

fof(f502,plain,(
    ! [X0] :
      ( m1_subset_1(sK3(sK3(k1_zfmisc_1(X0))),X0)
      | v1_xboole_0(sK3(k1_zfmisc_1(X0))) ) ),
    inference(resolution,[],[f265,f70])).

fof(f265,plain,(
    ! [X10,X9] :
      ( ~ m1_subset_1(X9,sK3(k1_zfmisc_1(X10)))
      | v1_xboole_0(sK3(k1_zfmisc_1(X10)))
      | m1_subset_1(X9,X10) ) ),
    inference(resolution,[],[f173,f70])).

fof(f594,plain,
    ( spl5_100
    | ~ spl5_103
    | spl5_104
    | ~ spl5_50 ),
    inference(avatar_split_clause,[],[f509,f293,f592,f586,f580])).

fof(f580,plain,
    ( spl5_100
  <=> v1_xboole_0(sK3(sK3(k1_zfmisc_1(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_100])])).

fof(f586,plain,
    ( spl5_103
  <=> ~ m1_subset_1(u1_struct_0(sK0),sK3(sK3(k1_zfmisc_1(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_103])])).

fof(f592,plain,
    ( spl5_104
  <=> v1_xboole_0(sK3(k1_zfmisc_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_104])])).

fof(f293,plain,
    ( spl5_50
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | ~ m1_subset_1(u1_struct_0(sK0),X0)
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_50])])).

fof(f509,plain,
    ( v1_xboole_0(sK3(k1_zfmisc_1(sK1)))
    | ~ m1_subset_1(u1_struct_0(sK0),sK3(sK3(k1_zfmisc_1(sK1))))
    | v1_xboole_0(sK3(sK3(k1_zfmisc_1(sK1))))
    | ~ spl5_50 ),
    inference(resolution,[],[f502,f294])).

fof(f294,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | ~ m1_subset_1(u1_struct_0(sK0),X0)
        | v1_xboole_0(X0) )
    | ~ spl5_50 ),
    inference(avatar_component_clause,[],[f293])).

fof(f566,plain,
    ( spl5_98
    | ~ spl5_0 ),
    inference(avatar_split_clause,[],[f479,f88,f564])).

fof(f564,plain,
    ( spl5_98
  <=> k2_pre_topc(sK0,sK3(k1_zfmisc_1(u1_struct_0(sK0)))) = k2_pre_topc(sK0,k2_pre_topc(sK0,sK3(k1_zfmisc_1(u1_struct_0(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_98])])).

fof(f479,plain,
    ( k2_pre_topc(sK0,sK3(k1_zfmisc_1(u1_struct_0(sK0)))) = k2_pre_topc(sK0,k2_pre_topc(sK0,sK3(k1_zfmisc_1(u1_struct_0(sK0)))))
    | ~ spl5_0 ),
    inference(resolution,[],[f429,f70])).

fof(f429,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_pre_topc(sK0,X0) = k2_pre_topc(sK0,k2_pre_topc(sK0,X0)) )
    | ~ spl5_0 ),
    inference(resolution,[],[f75,f89])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t31_tops_1.p',projectivity_k2_pre_topc)).

fof(f551,plain,
    ( spl5_94
    | ~ spl5_97
    | ~ spl5_50
    | ~ spl5_88 ),
    inference(avatar_split_clause,[],[f529,f520,f293,f549,f542])).

fof(f520,plain,
    ( spl5_88
  <=> m1_subset_1(sK3(sK3(k1_zfmisc_1(sK2))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_88])])).

fof(f529,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),sK3(sK3(k1_zfmisc_1(sK2))))
    | v1_xboole_0(sK3(sK3(k1_zfmisc_1(sK2))))
    | ~ spl5_50
    | ~ spl5_88 ),
    inference(resolution,[],[f521,f294])).

fof(f521,plain,
    ( m1_subset_1(sK3(sK3(k1_zfmisc_1(sK2))),sK1)
    | ~ spl5_88 ),
    inference(avatar_component_clause,[],[f520])).

fof(f544,plain,
    ( ~ spl5_93
    | spl5_94
    | spl5_27
    | ~ spl5_88 ),
    inference(avatar_split_clause,[],[f531,f520,f191,f542,f536])).

fof(f536,plain,
    ( spl5_93
  <=> ~ m1_subset_1(sK1,sK3(sK3(k1_zfmisc_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_93])])).

fof(f531,plain,
    ( v1_xboole_0(sK3(sK3(k1_zfmisc_1(sK2))))
    | ~ m1_subset_1(sK1,sK3(sK3(k1_zfmisc_1(sK2))))
    | ~ spl5_27
    | ~ spl5_88 ),
    inference(subsumption_resolution,[],[f530,f192])).

fof(f530,plain,
    ( v1_xboole_0(sK3(sK3(k1_zfmisc_1(sK2))))
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(sK1,sK3(sK3(k1_zfmisc_1(sK2))))
    | ~ spl5_88 ),
    inference(resolution,[],[f521,f170])).

fof(f528,plain,
    ( spl5_88
    | spl5_90
    | ~ spl5_76 ),
    inference(avatar_split_clause,[],[f510,f433,f526,f520])).

fof(f433,plain,
    ( spl5_76
  <=> ! [X2] :
        ( ~ m1_subset_1(X2,sK2)
        | m1_subset_1(X2,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_76])])).

fof(f510,plain,
    ( v1_xboole_0(sK3(k1_zfmisc_1(sK2)))
    | m1_subset_1(sK3(sK3(k1_zfmisc_1(sK2))),sK1)
    | ~ spl5_76 ),
    inference(resolution,[],[f502,f434])).

fof(f434,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,sK2)
        | m1_subset_1(X2,sK1) )
    | ~ spl5_76 ),
    inference(avatar_component_clause,[],[f433])).

fof(f501,plain,
    ( spl5_86
    | ~ spl5_0
    | ~ spl5_74 ),
    inference(avatar_split_clause,[],[f490,f423,f88,f499])).

fof(f423,plain,
    ( spl5_74
  <=> r1_tarski(k1_xboole_0,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_74])])).

fof(f490,plain,
    ( k2_pre_topc(sK0,k1_xboole_0) = k2_pre_topc(sK0,k2_pre_topc(sK0,k1_xboole_0))
    | ~ spl5_0
    | ~ spl5_74 ),
    inference(resolution,[],[f475,f424])).

fof(f424,plain,
    ( r1_tarski(k1_xboole_0,u1_struct_0(sK0))
    | ~ spl5_74 ),
    inference(avatar_component_clause,[],[f423])).

fof(f475,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK0))
        | k2_pre_topc(sK0,X0) = k2_pre_topc(sK0,k2_pre_topc(sK0,X0)) )
    | ~ spl5_0 ),
    inference(resolution,[],[f429,f77])).

fof(f488,plain,
    ( spl5_84
    | ~ spl5_0
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f478,f137,f88,f486])).

fof(f478,plain,
    ( k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k2_pre_topc(sK0,sK2))
    | ~ spl5_0
    | ~ spl5_14 ),
    inference(resolution,[],[f429,f138])).

fof(f474,plain,
    ( spl5_44
    | spl5_30
    | ~ spl5_20 ),
    inference(avatar_split_clause,[],[f399,f162,f207,f272])).

fof(f272,plain,
    ( spl5_44
  <=> ! [X8] :
        ( m1_subset_1(X8,u1_struct_0(sK0))
        | ~ m1_subset_1(X8,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_44])])).

fof(f207,plain,
    ( spl5_30
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f162,plain,
    ( spl5_20
  <=> r1_tarski(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f399,plain,
    ( ! [X3] :
        ( v1_xboole_0(sK2)
        | ~ m1_subset_1(X3,sK2)
        | m1_subset_1(X3,u1_struct_0(sK0)) )
    | ~ spl5_20 ),
    inference(resolution,[],[f260,f163])).

fof(f163,plain,
    ( r1_tarski(sK2,u1_struct_0(sK0))
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f162])).

fof(f473,plain,
    ( ~ spl5_83
    | spl5_68
    | spl5_27
    | ~ spl5_72 ),
    inference(avatar_split_clause,[],[f464,f407,f191,f386,f471])).

fof(f471,plain,
    ( spl5_83
  <=> ~ m1_subset_1(sK1,sK3(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_83])])).

fof(f386,plain,
    ( spl5_68
  <=> v1_xboole_0(sK3(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_68])])).

fof(f407,plain,
    ( spl5_72
  <=> m1_subset_1(sK3(sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_72])])).

fof(f464,plain,
    ( v1_xboole_0(sK3(sK2))
    | ~ m1_subset_1(sK1,sK3(sK2))
    | ~ spl5_27
    | ~ spl5_72 ),
    inference(subsumption_resolution,[],[f463,f192])).

fof(f463,plain,
    ( v1_xboole_0(sK3(sK2))
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(sK1,sK3(sK2))
    | ~ spl5_72 ),
    inference(resolution,[],[f408,f170])).

fof(f408,plain,
    ( m1_subset_1(sK3(sK2),sK1)
    | ~ spl5_72 ),
    inference(avatar_component_clause,[],[f407])).

fof(f461,plain,
    ( spl5_80
    | ~ spl5_14
    | ~ spl5_46 ),
    inference(avatar_split_clause,[],[f438,f282,f137,f459])).

fof(f459,plain,
    ( spl5_80
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_80])])).

fof(f282,plain,
    ( spl5_46
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_46])])).

fof(f438,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_14
    | ~ spl5_46 ),
    inference(superposition,[],[f138,f283])).

fof(f283,plain,
    ( k1_xboole_0 = sK2
    | ~ spl5_46 ),
    inference(avatar_component_clause,[],[f282])).

fof(f454,plain,
    ( ~ spl5_79
    | ~ spl5_46
    | spl5_73 ),
    inference(avatar_split_clause,[],[f453,f404,f282,f447])).

fof(f404,plain,
    ( spl5_73
  <=> ~ m1_subset_1(sK3(sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_73])])).

fof(f453,plain,
    ( ~ m1_subset_1(sK3(k1_xboole_0),sK1)
    | ~ spl5_46
    | ~ spl5_73 ),
    inference(forward_demodulation,[],[f405,f283])).

fof(f405,plain,
    ( ~ m1_subset_1(sK3(sK2),sK1)
    | ~ spl5_73 ),
    inference(avatar_component_clause,[],[f404])).

fof(f452,plain,
    ( spl5_78
    | ~ spl5_46
    | ~ spl5_72 ),
    inference(avatar_split_clause,[],[f444,f407,f282,f450])).

fof(f450,plain,
    ( spl5_78
  <=> m1_subset_1(sK3(k1_xboole_0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_78])])).

fof(f444,plain,
    ( m1_subset_1(sK3(k1_xboole_0),sK1)
    | ~ spl5_46
    | ~ spl5_72 ),
    inference(superposition,[],[f408,f283])).

fof(f435,plain,
    ( spl5_76
    | spl5_30
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f398,f116,f207,f433])).

fof(f398,plain,
    ( ! [X2] :
        ( v1_xboole_0(sK2)
        | ~ m1_subset_1(X2,sK2)
        | m1_subset_1(X2,sK1) )
    | ~ spl5_8 ),
    inference(resolution,[],[f260,f117])).

fof(f425,plain,
    ( spl5_74
    | ~ spl5_20
    | ~ spl5_46 ),
    inference(avatar_split_clause,[],[f414,f282,f162,f423])).

fof(f414,plain,
    ( r1_tarski(k1_xboole_0,u1_struct_0(sK0))
    | ~ spl5_20
    | ~ spl5_46 ),
    inference(superposition,[],[f163,f283])).

fof(f409,plain,
    ( spl5_72
    | ~ spl5_8
    | spl5_31 ),
    inference(avatar_split_clause,[],[f402,f204,f116,f407])).

fof(f204,plain,
    ( spl5_31
  <=> ~ v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).

fof(f402,plain,
    ( m1_subset_1(sK3(sK2),sK1)
    | ~ spl5_8
    | ~ spl5_31 ),
    inference(resolution,[],[f401,f70])).

fof(f401,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,sK2)
        | m1_subset_1(X2,sK1) )
    | ~ spl5_8
    | ~ spl5_31 ),
    inference(subsumption_resolution,[],[f398,f205])).

fof(f205,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ spl5_31 ),
    inference(avatar_component_clause,[],[f204])).

fof(f395,plain,
    ( spl5_48
    | spl5_50
    | ~ spl5_42 ),
    inference(avatar_split_clause,[],[f316,f267,f293,f290])).

fof(f290,plain,
    ( spl5_48
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_48])])).

fof(f316,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | v1_xboole_0(X0)
        | v1_xboole_0(u1_struct_0(sK0))
        | ~ m1_subset_1(u1_struct_0(sK0),X0) )
    | ~ spl5_42 ),
    inference(resolution,[],[f268,f170])).

fof(f268,plain,
    ( ! [X7] :
        ( m1_subset_1(X7,u1_struct_0(sK0))
        | ~ m1_subset_1(X7,sK1) )
    | ~ spl5_42 ),
    inference(avatar_component_clause,[],[f267])).

fof(f394,plain,
    ( spl5_68
    | ~ spl5_71
    | ~ spl5_60 ),
    inference(avatar_split_clause,[],[f381,f332,f392,f386])).

fof(f392,plain,
    ( spl5_71
  <=> ~ m1_subset_1(u1_struct_0(sK0),sK3(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_71])])).

fof(f381,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),sK3(sK2))
    | v1_xboole_0(sK3(sK2))
    | ~ spl5_60 ),
    inference(resolution,[],[f333,f70])).

fof(f377,plain,
    ( spl5_66
    | ~ spl5_0
    | ~ spl5_6
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f350,f130,f109,f88,f375])).

fof(f350,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | ~ spl5_0
    | ~ spl5_6
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f349,f89])).

fof(f349,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | ~ l1_pre_topc(sK0)
    | ~ spl5_6
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f348,f131])).

fof(f348,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl5_6 ),
    inference(resolution,[],[f68,f110])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = X1
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = X1
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => k2_pre_topc(X0,X1) = X1 ) ) ) ),
    inference(pure_predicate_removal,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t31_tops_1.p',t52_pre_topc)).

fof(f370,plain,
    ( spl5_64
    | ~ spl5_8
    | ~ spl5_46 ),
    inference(avatar_split_clause,[],[f363,f282,f116,f368])).

fof(f368,plain,
    ( spl5_64
  <=> r1_tarski(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_64])])).

fof(f363,plain,
    ( r1_tarski(k1_xboole_0,sK1)
    | ~ spl5_8
    | ~ spl5_46 ),
    inference(superposition,[],[f117,f283])).

fof(f357,plain,
    ( spl5_62
    | ~ spl5_18
    | ~ spl5_54 ),
    inference(avatar_split_clause,[],[f338,f313,f155,f355])).

fof(f355,plain,
    ( spl5_62
  <=> r1_tarski(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_62])])).

fof(f313,plain,
    ( spl5_54
  <=> u1_struct_0(sK0) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_54])])).

fof(f338,plain,
    ( r1_tarski(sK1,k1_xboole_0)
    | ~ spl5_18
    | ~ spl5_54 ),
    inference(superposition,[],[f156,f314])).

fof(f314,plain,
    ( u1_struct_0(sK0) = k1_xboole_0
    | ~ spl5_54 ),
    inference(avatar_component_clause,[],[f313])).

fof(f334,plain,
    ( spl5_48
    | spl5_60
    | ~ spl5_44 ),
    inference(avatar_split_clause,[],[f285,f272,f332,f290])).

fof(f285,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK2)
        | v1_xboole_0(X0)
        | v1_xboole_0(u1_struct_0(sK0))
        | ~ m1_subset_1(u1_struct_0(sK0),X0) )
    | ~ spl5_44 ),
    inference(resolution,[],[f273,f170])).

fof(f273,plain,
    ( ! [X8] :
        ( m1_subset_1(X8,u1_struct_0(sK0))
        | ~ m1_subset_1(X8,sK2) )
    | ~ spl5_44 ),
    inference(avatar_component_clause,[],[f272])).

fof(f330,plain,
    ( spl5_56
    | ~ spl5_59
    | ~ spl5_50 ),
    inference(avatar_split_clause,[],[f317,f293,f328,f322])).

fof(f322,plain,
    ( spl5_56
  <=> v1_xboole_0(sK3(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_56])])).

fof(f328,plain,
    ( spl5_59
  <=> ~ m1_subset_1(u1_struct_0(sK0),sK3(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_59])])).

fof(f317,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),sK3(sK1))
    | v1_xboole_0(sK3(sK1))
    | ~ spl5_50 ),
    inference(resolution,[],[f294,f70])).

fof(f315,plain,
    ( spl5_54
    | ~ spl5_48 ),
    inference(avatar_split_clause,[],[f308,f290,f313])).

fof(f308,plain,
    ( u1_struct_0(sK0) = k1_xboole_0
    | ~ spl5_48 ),
    inference(resolution,[],[f291,f67])).

fof(f67,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t31_tops_1.p',t6_boole)).

fof(f291,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl5_48 ),
    inference(avatar_component_clause,[],[f290])).

fof(f305,plain,
    ( spl5_52
    | ~ spl5_26 ),
    inference(avatar_split_clause,[],[f298,f194,f303])).

fof(f298,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_26 ),
    inference(resolution,[],[f195,f67])).

fof(f195,plain,
    ( v1_xboole_0(sK1)
    | ~ spl5_26 ),
    inference(avatar_component_clause,[],[f194])).

fof(f295,plain,
    ( spl5_48
    | spl5_50
    | ~ spl5_42 ),
    inference(avatar_split_clause,[],[f270,f267,f293,f290])).

fof(f270,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | v1_xboole_0(X0)
        | v1_xboole_0(u1_struct_0(sK0))
        | ~ m1_subset_1(u1_struct_0(sK0),X0) )
    | ~ spl5_42 ),
    inference(resolution,[],[f268,f170])).

fof(f284,plain,
    ( spl5_46
    | ~ spl5_30 ),
    inference(avatar_split_clause,[],[f277,f207,f282])).

fof(f277,plain,
    ( k1_xboole_0 = sK2
    | ~ spl5_30 ),
    inference(resolution,[],[f208,f67])).

fof(f208,plain,
    ( v1_xboole_0(sK2)
    | ~ spl5_30 ),
    inference(avatar_component_clause,[],[f207])).

fof(f274,plain,
    ( spl5_30
    | spl5_44
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f264,f137,f272,f207])).

fof(f264,plain,
    ( ! [X8] :
        ( m1_subset_1(X8,u1_struct_0(sK0))
        | v1_xboole_0(sK2)
        | ~ m1_subset_1(X8,sK2) )
    | ~ spl5_14 ),
    inference(resolution,[],[f173,f138])).

fof(f269,plain,
    ( spl5_26
    | spl5_42
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f263,f130,f267,f194])).

fof(f263,plain,
    ( ! [X7] :
        ( m1_subset_1(X7,u1_struct_0(sK0))
        | v1_xboole_0(sK1)
        | ~ m1_subset_1(X7,sK1) )
    | ~ spl5_12 ),
    inference(resolution,[],[f173,f131])).

fof(f256,plain,
    ( spl5_40
    | ~ spl5_36 ),
    inference(avatar_split_clause,[],[f238,f230,f254])).

fof(f254,plain,
    ( spl5_40
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_40])])).

fof(f230,plain,
    ( spl5_36
  <=> k1_xboole_0 = sK3(k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).

fof(f238,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_36 ),
    inference(superposition,[],[f70,f231])).

fof(f231,plain,
    ( k1_xboole_0 = sK3(k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_36 ),
    inference(avatar_component_clause,[],[f230])).

fof(f246,plain,
    ( spl5_38
    | ~ spl5_36 ),
    inference(avatar_split_clause,[],[f236,f230,f244])).

fof(f244,plain,
    ( spl5_38
  <=> r1_tarski(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).

fof(f236,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl5_36 ),
    inference(superposition,[],[f148,f231])).

fof(f148,plain,(
    ! [X0] : r1_tarski(sK3(k1_zfmisc_1(X0)),X0) ),
    inference(resolution,[],[f76,f70])).

fof(f234,plain,(
    ~ spl5_32 ),
    inference(avatar_contradiction_clause,[],[f233])).

fof(f233,plain,
    ( $false
    | ~ spl5_32 ),
    inference(resolution,[],[f215,f70])).

fof(f215,plain,
    ( ! [X2] : ~ m1_subset_1(X2,sK3(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl5_32 ),
    inference(avatar_component_clause,[],[f214])).

fof(f214,plain,
    ( spl5_32
  <=> ! [X2] : ~ m1_subset_1(X2,sK3(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).

fof(f232,plain,
    ( spl5_36
    | ~ spl5_34 ),
    inference(avatar_split_clause,[],[f225,f220,f230])).

fof(f220,plain,
    ( spl5_34
  <=> v1_xboole_0(sK3(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).

fof(f225,plain,
    ( k1_xboole_0 = sK3(k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_34 ),
    inference(resolution,[],[f221,f67])).

fof(f221,plain,
    ( v1_xboole_0(sK3(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl5_34 ),
    inference(avatar_component_clause,[],[f220])).

fof(f222,plain,
    ( spl5_32
    | spl5_34
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f211,f102,f220,f214])).

fof(f102,plain,
    ( spl5_4
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f211,plain,
    ( ! [X2] :
        ( v1_xboole_0(sK3(k1_zfmisc_1(k1_xboole_0)))
        | ~ m1_subset_1(X2,sK3(k1_zfmisc_1(k1_xboole_0))) )
    | ~ spl5_4 ),
    inference(resolution,[],[f172,f70])).

fof(f172,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | v1_xboole_0(X0)
        | ~ m1_subset_1(X1,X0) )
    | ~ spl5_4 ),
    inference(resolution,[],[f171,f73])).

fof(f171,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) )
    | ~ spl5_4 ),
    inference(resolution,[],[f81,f103])).

fof(f103,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f102])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t31_tops_1.p',t5_subset)).

fof(f209,plain,
    ( ~ spl5_29
    | spl5_24
    | spl5_30
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f176,f137,f207,f188,f201])).

fof(f201,plain,
    ( spl5_29
  <=> ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).

fof(f188,plain,
    ( spl5_24
  <=> v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f176,plain,
    ( v1_xboole_0(sK2)
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2)
    | ~ spl5_14 ),
    inference(resolution,[],[f170,f138])).

fof(f196,plain,
    ( ~ spl5_23
    | spl5_24
    | spl5_26
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f175,f130,f194,f188,f182])).

fof(f182,plain,
    ( spl5_23
  <=> ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f175,plain,
    ( v1_xboole_0(sK1)
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1)
    | ~ spl5_12 ),
    inference(resolution,[],[f170,f131])).

fof(f164,plain,
    ( spl5_20
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f150,f137,f162])).

fof(f150,plain,
    ( r1_tarski(sK2,u1_struct_0(sK0))
    | ~ spl5_14 ),
    inference(resolution,[],[f76,f138])).

fof(f157,plain,
    ( spl5_18
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f149,f130,f155])).

fof(f149,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl5_12 ),
    inference(resolution,[],[f76,f131])).

fof(f146,plain,(
    ~ spl5_17 ),
    inference(avatar_split_clause,[],[f64,f144])).

fof(f64,plain,(
    ~ r1_tarski(k2_pre_topc(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,sK2),sK1)
    & r1_tarski(sK2,sK1)
    & v4_pre_topc(sK1,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f31,f52,f51,f50])).

fof(f50,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(k2_pre_topc(X0,X2),X1)
                & r1_tarski(X2,X1)
                & v4_pre_topc(X1,X0)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k2_pre_topc(sK0,X2),X1)
              & r1_tarski(X2,X1)
              & v4_pre_topc(X1,sK0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k2_pre_topc(X0,X2),X1)
              & r1_tarski(X2,X1)
              & v4_pre_topc(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ~ r1_tarski(k2_pre_topc(X0,X2),sK1)
            & r1_tarski(X2,sK1)
            & v4_pre_topc(sK1,X0)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k2_pre_topc(X0,X2),X1)
          & r1_tarski(X2,X1)
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r1_tarski(k2_pre_topc(X0,sK2),X1)
        & r1_tarski(sK2,X1)
        & v4_pre_topc(X1,X0)
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k2_pre_topc(X0,X2),X1)
              & r1_tarski(X2,X1)
              & v4_pre_topc(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k2_pre_topc(X0,X2),X1)
              & r1_tarski(X2,X1)
              & v4_pre_topc(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( r1_tarski(X2,X1)
                    & v4_pre_topc(X1,X0) )
                 => r1_tarski(k2_pre_topc(X0,X2),X1) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_tarski(X2,X1)
                  & v4_pre_topc(X1,X0) )
               => r1_tarski(k2_pre_topc(X0,X2),X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t31_tops_1.p',t31_tops_1)).

fof(f139,plain,(
    spl5_14 ),
    inference(avatar_split_clause,[],[f61,f137])).

fof(f61,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f53])).

fof(f132,plain,(
    spl5_12 ),
    inference(avatar_split_clause,[],[f60,f130])).

fof(f60,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f53])).

fof(f125,plain,(
    spl5_10 ),
    inference(avatar_split_clause,[],[f66,f123])).

fof(f123,plain,
    ( spl5_10
  <=> k1_xboole_0 = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f66,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t31_tops_1.p',d2_xboole_0)).

fof(f118,plain,(
    spl5_8 ),
    inference(avatar_split_clause,[],[f63,f116])).

fof(f63,plain,(
    r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f53])).

fof(f111,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f62,f109])).

fof(f62,plain,(
    v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f53])).

fof(f104,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f83,f102])).

fof(f83,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(forward_demodulation,[],[f65,f66])).

fof(f65,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t31_tops_1.p',dt_o_0_0_xboole_0)).

fof(f97,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f82,f95])).

fof(f95,plain,
    ( spl5_2
  <=> l1_pre_topc(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f82,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    l1_pre_topc(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f13,f57])).

fof(f57,plain,
    ( ? [X0] : l1_pre_topc(X0)
   => l1_pre_topc(sK4) ),
    introduced(choice_axiom,[])).

fof(f13,axiom,(
    ? [X0] : l1_pre_topc(X0) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t31_tops_1.p',existence_l1_pre_topc)).

fof(f90,plain,(
    spl5_0 ),
    inference(avatar_split_clause,[],[f59,f88])).

fof(f59,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f53])).
%------------------------------------------------------------------------------
