%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:48 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  152 ( 288 expanded)
%              Number of leaves         :   38 ( 125 expanded)
%              Depth                    :   11
%              Number of atoms          :  426 ( 840 expanded)
%              Number of equality atoms :   50 ( 124 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1556,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f72,f77,f82,f87,f92,f97,f103,f110,f116,f122,f128,f134,f152,f163,f200,f550,f756,f774,f775,f861,f867,f1421,f1438,f1503,f1553,f1555])).

fof(f1555,plain,
    ( ~ spl8_9
    | spl8_5
    | ~ spl8_3
    | ~ spl8_15
    | ~ spl8_79
    | ~ spl8_261 ),
    inference(avatar_split_clause,[],[f1554,f1550,f548,f149,f79,f89,f113])).

fof(f113,plain,
    ( spl8_9
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f89,plain,
    ( spl8_5
  <=> v4_pre_topc(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f79,plain,
    ( spl8_3
  <=> v4_pre_topc(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f149,plain,
    ( spl8_15
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f548,plain,
    ( spl8_79
  <=> ! [X0] :
        ( v4_pre_topc(k1_setfam_1(k2_tarski(X0,k2_struct_0(sK2))),sK2)
        | ~ v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(k1_setfam_1(k2_tarski(X0,k2_struct_0(sK2))),k1_zfmisc_1(k2_struct_0(sK2)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_79])])).

fof(f1550,plain,
    ( spl8_261
  <=> sK3 = k1_setfam_1(k2_tarski(sK3,k2_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_261])])).

fof(f1554,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK2)))
    | ~ v4_pre_topc(sK3,sK0)
    | v4_pre_topc(sK3,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl8_79
    | ~ spl8_261 ),
    inference(superposition,[],[f549,f1552])).

fof(f1552,plain,
    ( sK3 = k1_setfam_1(k2_tarski(sK3,k2_struct_0(sK2)))
    | ~ spl8_261 ),
    inference(avatar_component_clause,[],[f1550])).

fof(f549,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k1_setfam_1(k2_tarski(X0,k2_struct_0(sK2))),k1_zfmisc_1(k2_struct_0(sK2)))
        | ~ v4_pre_topc(X0,sK0)
        | v4_pre_topc(k1_setfam_1(k2_tarski(X0,k2_struct_0(sK2))),sK2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) )
    | ~ spl8_79 ),
    inference(avatar_component_clause,[],[f548])).

fof(f1553,plain,
    ( spl8_261
    | ~ spl8_251 ),
    inference(avatar_split_clause,[],[f1548,f1500,f1550])).

fof(f1500,plain,
    ( spl8_251
  <=> r1_tarski(sK3,k2_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_251])])).

fof(f1548,plain,
    ( sK3 = k1_setfam_1(k2_tarski(sK3,k2_struct_0(sK2)))
    | ~ spl8_251 ),
    inference(resolution,[],[f1502,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_setfam_1(k2_tarski(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f59,f58])).

fof(f58,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f1502,plain,
    ( r1_tarski(sK3,k2_struct_0(sK2))
    | ~ spl8_251 ),
    inference(avatar_component_clause,[],[f1500])).

fof(f1503,plain,
    ( spl8_251
    | ~ spl8_114
    | ~ spl8_238 ),
    inference(avatar_split_clause,[],[f1489,f1435,f767,f1500])).

fof(f767,plain,
    ( spl8_114
  <=> r1_tarski(k2_struct_0(k1_pre_topc(sK2,sK3)),k2_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_114])])).

fof(f1435,plain,
    ( spl8_238
  <=> sK3 = k2_struct_0(k1_pre_topc(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_238])])).

fof(f1489,plain,
    ( r1_tarski(sK3,k2_struct_0(sK2))
    | ~ spl8_114
    | ~ spl8_238 ),
    inference(backward_demodulation,[],[f769,f1437])).

fof(f1437,plain,
    ( sK3 = k2_struct_0(k1_pre_topc(sK2,sK3))
    | ~ spl8_238 ),
    inference(avatar_component_clause,[],[f1435])).

fof(f769,plain,
    ( r1_tarski(k2_struct_0(k1_pre_topc(sK2,sK3)),k2_struct_0(sK2))
    | ~ spl8_114 ),
    inference(avatar_component_clause,[],[f767])).

fof(f1438,plain,
    ( spl8_238
    | ~ spl8_134
    | ~ spl8_237 ),
    inference(avatar_split_clause,[],[f1422,f1418,f864,f1435])).

fof(f864,plain,
    ( spl8_134
  <=> k2_struct_0(k1_pre_topc(sK2,sK3)) = u1_struct_0(k1_pre_topc(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_134])])).

fof(f1418,plain,
    ( spl8_237
  <=> sK3 = u1_struct_0(k1_pre_topc(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_237])])).

fof(f1422,plain,
    ( sK3 = k2_struct_0(k1_pre_topc(sK2,sK3))
    | ~ spl8_134
    | ~ spl8_237 ),
    inference(backward_demodulation,[],[f866,f1420])).

fof(f1420,plain,
    ( sK3 = u1_struct_0(k1_pre_topc(sK2,sK3))
    | ~ spl8_237 ),
    inference(avatar_component_clause,[],[f1418])).

fof(f866,plain,
    ( k2_struct_0(k1_pre_topc(sK2,sK3)) = u1_struct_0(k1_pre_topc(sK2,sK3))
    | ~ spl8_134 ),
    inference(avatar_component_clause,[],[f864])).

fof(f1421,plain,
    ( spl8_237
    | ~ spl8_15
    | ~ spl8_23 ),
    inference(avatar_split_clause,[],[f1415,f198,f149,f1418])).

fof(f198,plain,
    ( spl8_23
  <=> ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK2)))
        | u1_struct_0(k1_pre_topc(sK2,X1)) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).

fof(f1415,plain,
    ( sK3 = u1_struct_0(k1_pre_topc(sK2,sK3))
    | ~ spl8_15
    | ~ spl8_23 ),
    inference(resolution,[],[f199,f151])).

fof(f151,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK2)))
    | ~ spl8_15 ),
    inference(avatar_component_clause,[],[f149])).

fof(f199,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK2)))
        | u1_struct_0(k1_pre_topc(sK2,X1)) = X1 )
    | ~ spl8_23 ),
    inference(avatar_component_clause,[],[f198])).

fof(f867,plain,
    ( spl8_134
    | ~ spl8_133 ),
    inference(avatar_split_clause,[],[f862,f858,f864])).

fof(f858,plain,
    ( spl8_133
  <=> l1_struct_0(k1_pre_topc(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_133])])).

fof(f862,plain,
    ( k2_struct_0(k1_pre_topc(sK2,sK3)) = u1_struct_0(k1_pre_topc(sK2,sK3))
    | ~ spl8_133 ),
    inference(resolution,[],[f860,f39])).

fof(f39,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f860,plain,
    ( l1_struct_0(k1_pre_topc(sK2,sK3))
    | ~ spl8_133 ),
    inference(avatar_component_clause,[],[f858])).

fof(f861,plain,
    ( spl8_133
    | ~ spl8_115 ),
    inference(avatar_split_clause,[],[f846,f771,f858])).

fof(f771,plain,
    ( spl8_115
  <=> l1_pre_topc(k1_pre_topc(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_115])])).

fof(f846,plain,
    ( l1_struct_0(k1_pre_topc(sK2,sK3))
    | ~ spl8_115 ),
    inference(resolution,[],[f772,f40])).

fof(f40,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f772,plain,
    ( l1_pre_topc(k1_pre_topc(sK2,sK3))
    | ~ spl8_115 ),
    inference(avatar_component_clause,[],[f771])).

fof(f775,plain,
    ( spl8_115
    | ~ spl8_10
    | ~ spl8_113 ),
    inference(avatar_split_clause,[],[f760,f753,f119,f771])).

fof(f119,plain,
    ( spl8_10
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f753,plain,
    ( spl8_113
  <=> m1_pre_topc(k1_pre_topc(sK2,sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_113])])).

fof(f760,plain,
    ( ~ l1_pre_topc(sK2)
    | l1_pre_topc(k1_pre_topc(sK2,sK3))
    | ~ spl8_113 ),
    inference(resolution,[],[f755,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f755,plain,
    ( m1_pre_topc(k1_pre_topc(sK2,sK3),sK2)
    | ~ spl8_113 ),
    inference(avatar_component_clause,[],[f753])).

fof(f774,plain,
    ( ~ spl8_10
    | spl8_114
    | ~ spl8_115
    | ~ spl8_113 ),
    inference(avatar_split_clause,[],[f759,f753,f771,f767,f119])).

fof(f759,plain,
    ( ~ l1_pre_topc(k1_pre_topc(sK2,sK3))
    | r1_tarski(k2_struct_0(k1_pre_topc(sK2,sK3)),k2_struct_0(sK2))
    | ~ l1_pre_topc(sK2)
    | ~ spl8_113 ),
    inference(resolution,[],[f755,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X1)
      | r1_tarski(k2_struct_0(X1),k2_struct_0(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X1,X0)
          <=> ( ! [X2] :
                  ( ( r2_hidden(X2,u1_pre_topc(X1))
                  <=> ? [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                        & r2_hidden(X3,u1_pre_topc(X0))
                        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
              & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X1,X0)
          <=> ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( r2_hidden(X2,u1_pre_topc(X1))
                  <=> ? [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                        & r2_hidden(X3,u1_pre_topc(X0))
                        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) )
              & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_pre_topc)).

fof(f756,plain,
    ( spl8_113
    | ~ spl8_15
    | ~ spl8_17 ),
    inference(avatar_split_clause,[],[f750,f161,f149,f753])).

fof(f161,plain,
    ( spl8_17
  <=> ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK2)))
        | m1_pre_topc(k1_pre_topc(sK2,X1),sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

fof(f750,plain,
    ( m1_pre_topc(k1_pre_topc(sK2,sK3),sK2)
    | ~ spl8_15
    | ~ spl8_17 ),
    inference(resolution,[],[f162,f151])).

fof(f162,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK2)))
        | m1_pre_topc(k1_pre_topc(sK2,X1),sK2) )
    | ~ spl8_17 ),
    inference(avatar_component_clause,[],[f161])).

fof(f550,plain,
    ( ~ spl8_1
    | spl8_79
    | ~ spl8_4
    | ~ spl8_8
    | ~ spl8_12 ),
    inference(avatar_split_clause,[],[f546,f131,f107,f84,f548,f69])).

fof(f69,plain,
    ( spl8_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f84,plain,
    ( spl8_4
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f107,plain,
    ( spl8_8
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f131,plain,
    ( spl8_12
  <=> u1_struct_0(sK2) = k2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f546,plain,
    ( ! [X0] :
        ( v4_pre_topc(k1_setfam_1(k2_tarski(X0,k2_struct_0(sK2))),sK2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(k1_setfam_1(k2_tarski(X0,k2_struct_0(sK2))),k1_zfmisc_1(k2_struct_0(sK2)))
        | ~ l1_pre_topc(sK0)
        | ~ v4_pre_topc(X0,sK0) )
    | ~ spl8_4
    | ~ spl8_8
    | ~ spl8_12 ),
    inference(forward_demodulation,[],[f545,f215])).

fof(f215,plain,(
    ! [X2,X3] : k9_subset_1(X2,X3,X2) = k1_setfam_1(k2_tarski(X3,X2)) ),
    inference(resolution,[],[f65,f104])).

fof(f104,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f38,f37])).

fof(f37,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f38,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) ) ),
    inference(definition_unfolding,[],[f61,f58])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f545,plain,
    ( ! [X0] :
        ( v4_pre_topc(k9_subset_1(k2_struct_0(sK2),X0,k2_struct_0(sK2)),sK2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(k1_setfam_1(k2_tarski(X0,k2_struct_0(sK2))),k1_zfmisc_1(k2_struct_0(sK2)))
        | ~ l1_pre_topc(sK0)
        | ~ v4_pre_topc(X0,sK0) )
    | ~ spl8_4
    | ~ spl8_8
    | ~ spl8_12 ),
    inference(forward_demodulation,[],[f544,f133])).

fof(f133,plain,
    ( u1_struct_0(sK2) = k2_struct_0(sK2)
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f131])).

fof(f544,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(k1_setfam_1(k2_tarski(X0,k2_struct_0(sK2))),k1_zfmisc_1(k2_struct_0(sK2)))
        | ~ l1_pre_topc(sK0)
        | ~ v4_pre_topc(X0,sK0)
        | v4_pre_topc(k9_subset_1(u1_struct_0(sK2),X0,k2_struct_0(sK2)),sK2) )
    | ~ spl8_4
    | ~ spl8_8
    | ~ spl8_12 ),
    inference(forward_demodulation,[],[f543,f109])).

fof(f109,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f107])).

fof(f543,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k1_setfam_1(k2_tarski(X0,k2_struct_0(sK2))),k1_zfmisc_1(k2_struct_0(sK2)))
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v4_pre_topc(X0,sK0)
        | v4_pre_topc(k9_subset_1(u1_struct_0(sK2),X0,k2_struct_0(sK2)),sK2) )
    | ~ spl8_4
    | ~ spl8_12 ),
    inference(forward_demodulation,[],[f542,f215])).

fof(f542,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k9_subset_1(k2_struct_0(sK2),X0,k2_struct_0(sK2)),k1_zfmisc_1(k2_struct_0(sK2)))
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v4_pre_topc(X0,sK0)
        | v4_pre_topc(k9_subset_1(u1_struct_0(sK2),X0,k2_struct_0(sK2)),sK2) )
    | ~ spl8_4
    | ~ spl8_12 ),
    inference(forward_demodulation,[],[f538,f133])).

fof(f538,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK2),X0,k2_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v4_pre_topc(X0,sK0)
        | v4_pre_topc(k9_subset_1(u1_struct_0(sK2),X0,k2_struct_0(sK2)),sK2) )
    | ~ spl8_4 ),
    inference(resolution,[],[f67,f86])).

fof(f86,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f84])).

fof(f67,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X3,X0)
      | v4_pre_topc(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),X1) ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X3,X0)
      | k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
      | v4_pre_topc(X2,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v4_pre_topc(X2,X1)
              <=> ? [X3] :
                    ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                    & v4_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => ( v4_pre_topc(X2,X1)
              <=> ? [X3] :
                    ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                    & v4_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_pre_topc)).

fof(f200,plain,
    ( ~ spl8_10
    | spl8_23
    | ~ spl8_12 ),
    inference(avatar_split_clause,[],[f192,f131,f198,f119])).

fof(f192,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK2)))
        | ~ l1_pre_topc(sK2)
        | u1_struct_0(k1_pre_topc(sK2,X1)) = X1 )
    | ~ spl8_12 ),
    inference(superposition,[],[f57,f133])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | u1_struct_0(k1_pre_topc(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => u1_struct_0(k1_pre_topc(X0,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_pre_topc)).

fof(f163,plain,
    ( ~ spl8_10
    | spl8_17
    | ~ spl8_12 ),
    inference(avatar_split_clause,[],[f155,f131,f161,f119])).

fof(f155,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK2)))
        | ~ l1_pre_topc(sK2)
        | m1_pre_topc(k1_pre_topc(sK2,X1),sK2) )
    | ~ spl8_12 ),
    inference(superposition,[],[f60,f133])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | m1_pre_topc(k1_pre_topc(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_pre_topc(k1_pre_topc(X0,X1),X0) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_pre_topc)).

fof(f152,plain,
    ( spl8_15
    | ~ spl8_6
    | ~ spl8_12 ),
    inference(avatar_split_clause,[],[f147,f131,f94,f149])).

fof(f94,plain,
    ( spl8_6
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f147,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK2)))
    | ~ spl8_6
    | ~ spl8_12 ),
    inference(backward_demodulation,[],[f96,f133])).

fof(f96,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f94])).

fof(f134,plain,
    ( spl8_12
    | ~ spl8_11 ),
    inference(avatar_split_clause,[],[f129,f125,f131])).

fof(f125,plain,
    ( spl8_11
  <=> l1_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f129,plain,
    ( u1_struct_0(sK2) = k2_struct_0(sK2)
    | ~ spl8_11 ),
    inference(resolution,[],[f127,f39])).

fof(f127,plain,
    ( l1_struct_0(sK2)
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f125])).

fof(f128,plain,
    ( spl8_11
    | ~ spl8_10 ),
    inference(avatar_split_clause,[],[f123,f119,f125])).

fof(f123,plain,
    ( l1_struct_0(sK2)
    | ~ spl8_10 ),
    inference(resolution,[],[f121,f40])).

fof(f121,plain,
    ( l1_pre_topc(sK2)
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f119])).

fof(f122,plain,
    ( spl8_10
    | ~ spl8_1
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f117,f84,f69,f119])).

fof(f117,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK2)
    | ~ spl8_4 ),
    inference(resolution,[],[f51,f86])).

fof(f116,plain,
    ( spl8_9
    | ~ spl8_2
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f111,f107,f74,f113])).

fof(f74,plain,
    ( spl8_2
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f111,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl8_2
    | ~ spl8_8 ),
    inference(backward_demodulation,[],[f76,f109])).

fof(f76,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f74])).

fof(f110,plain,
    ( spl8_8
    | ~ spl8_7 ),
    inference(avatar_split_clause,[],[f105,f100,f107])).

fof(f100,plain,
    ( spl8_7
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f105,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl8_7 ),
    inference(resolution,[],[f39,f102])).

fof(f102,plain,
    ( l1_struct_0(sK0)
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f100])).

fof(f103,plain,
    ( spl8_7
    | ~ spl8_1 ),
    inference(avatar_split_clause,[],[f98,f69,f100])).

fof(f98,plain,
    ( l1_struct_0(sK0)
    | ~ spl8_1 ),
    inference(resolution,[],[f40,f71])).

fof(f71,plain,
    ( l1_pre_topc(sK0)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f69])).

fof(f97,plain,(
    spl8_6 ),
    inference(avatar_split_clause,[],[f30,f94])).

fof(f30,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v4_pre_topc(X3,X2)
                  & X1 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              & v4_pre_topc(X1,X0)
              & m1_pre_topc(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v4_pre_topc(X3,X2)
                  & X1 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              & v4_pre_topc(X1,X0)
              & m1_pre_topc(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_pre_topc(X2,X0)
               => ( v4_pre_topc(X1,X0)
                 => ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
                     => ( X1 = X3
                       => v4_pre_topc(X3,X2) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( v4_pre_topc(X1,X0)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
                   => ( X1 = X3
                     => v4_pre_topc(X3,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_tops_2)).

fof(f92,plain,(
    ~ spl8_5 ),
    inference(avatar_split_clause,[],[f32,f89])).

fof(f32,plain,(
    ~ v4_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f87,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f33,f84])).

fof(f33,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f82,plain,(
    spl8_3 ),
    inference(avatar_split_clause,[],[f63,f79])).

fof(f63,plain,(
    v4_pre_topc(sK3,sK0) ),
    inference(definition_unfolding,[],[f34,f31])).

fof(f31,plain,(
    sK1 = sK3 ),
    inference(cnf_transformation,[],[f18])).

fof(f34,plain,(
    v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f77,plain,(
    spl8_2 ),
    inference(avatar_split_clause,[],[f62,f74])).

fof(f62,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(definition_unfolding,[],[f35,f31])).

fof(f35,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f72,plain,(
    spl8_1 ),
    inference(avatar_split_clause,[],[f36,f69])).

fof(f36,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:09:02 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (8354)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (8382)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.51  % (8361)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.52  % (8365)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.52  % (8358)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (8359)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (8362)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.53  % (8364)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.53  % (8364)Refutation not found, incomplete strategy% (8364)------------------------------
% 0.21/0.53  % (8364)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (8364)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (8364)Memory used [KB]: 10746
% 0.21/0.53  % (8364)Time elapsed: 0.118 s
% 0.21/0.53  % (8364)------------------------------
% 0.21/0.53  % (8364)------------------------------
% 0.21/0.53  % (8383)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.53  % (8375)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.53  % (8355)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (8360)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.54  % (8356)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (8357)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (8378)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.54  % (8381)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (8380)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  % (8376)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.54  % (8370)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.54  % (8376)Refutation not found, incomplete strategy% (8376)------------------------------
% 0.21/0.54  % (8376)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (8376)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (8376)Memory used [KB]: 10874
% 0.21/0.54  % (8376)Time elapsed: 0.099 s
% 0.21/0.54  % (8376)------------------------------
% 0.21/0.54  % (8376)------------------------------
% 0.21/0.54  % (8358)Refutation not found, incomplete strategy% (8358)------------------------------
% 0.21/0.54  % (8358)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (8358)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (8358)Memory used [KB]: 6268
% 0.21/0.54  % (8358)Time elapsed: 0.135 s
% 0.21/0.54  % (8358)------------------------------
% 0.21/0.54  % (8358)------------------------------
% 0.21/0.54  % (8359)Refutation not found, incomplete strategy% (8359)------------------------------
% 0.21/0.54  % (8359)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (8359)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (8359)Memory used [KB]: 6396
% 0.21/0.54  % (8359)Time elapsed: 0.137 s
% 0.21/0.54  % (8359)------------------------------
% 0.21/0.54  % (8359)------------------------------
% 0.21/0.54  % (8369)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.54  % (8368)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.54  % (8372)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.55  % (8373)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.55  % (8379)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.55  % (8363)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.55  % (8366)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.55  % (8377)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.55  % (8374)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.55  % (8371)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.55  % (8367)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.56  % (8371)Refutation not found, incomplete strategy% (8371)------------------------------
% 0.21/0.56  % (8371)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (8371)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (8371)Memory used [KB]: 10618
% 0.21/0.56  % (8371)Time elapsed: 0.161 s
% 0.21/0.56  % (8371)------------------------------
% 0.21/0.56  % (8371)------------------------------
% 0.21/0.57  % (8363)Refutation not found, incomplete strategy% (8363)------------------------------
% 0.21/0.57  % (8363)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (8363)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.58  
% 0.21/0.58  % (8363)Memory used [KB]: 10746
% 0.21/0.58  % (8363)Time elapsed: 0.172 s
% 0.21/0.58  % (8363)------------------------------
% 0.21/0.58  % (8363)------------------------------
% 0.21/0.58  % (8370)Refutation found. Thanks to Tanya!
% 0.21/0.58  % SZS status Theorem for theBenchmark
% 0.21/0.58  % SZS output start Proof for theBenchmark
% 0.21/0.58  fof(f1556,plain,(
% 0.21/0.58    $false),
% 0.21/0.58    inference(avatar_sat_refutation,[],[f72,f77,f82,f87,f92,f97,f103,f110,f116,f122,f128,f134,f152,f163,f200,f550,f756,f774,f775,f861,f867,f1421,f1438,f1503,f1553,f1555])).
% 0.21/0.58  fof(f1555,plain,(
% 0.21/0.58    ~spl8_9 | spl8_5 | ~spl8_3 | ~spl8_15 | ~spl8_79 | ~spl8_261),
% 0.21/0.58    inference(avatar_split_clause,[],[f1554,f1550,f548,f149,f79,f89,f113])).
% 0.21/0.58  fof(f113,plain,(
% 0.21/0.58    spl8_9 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 0.21/0.58  fof(f89,plain,(
% 0.21/0.58    spl8_5 <=> v4_pre_topc(sK3,sK2)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.21/0.58  fof(f79,plain,(
% 0.21/0.58    spl8_3 <=> v4_pre_topc(sK3,sK0)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.21/0.58  fof(f149,plain,(
% 0.21/0.58    spl8_15 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK2)))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).
% 0.21/0.58  fof(f548,plain,(
% 0.21/0.58    spl8_79 <=> ! [X0] : (v4_pre_topc(k1_setfam_1(k2_tarski(X0,k2_struct_0(sK2))),sK2) | ~v4_pre_topc(X0,sK0) | ~m1_subset_1(k1_setfam_1(k2_tarski(X0,k2_struct_0(sK2))),k1_zfmisc_1(k2_struct_0(sK2))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl8_79])])).
% 0.21/0.58  fof(f1550,plain,(
% 0.21/0.58    spl8_261 <=> sK3 = k1_setfam_1(k2_tarski(sK3,k2_struct_0(sK2)))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl8_261])])).
% 0.21/0.58  fof(f1554,plain,(
% 0.21/0.58    ~m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK2))) | ~v4_pre_topc(sK3,sK0) | v4_pre_topc(sK3,sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK0))) | (~spl8_79 | ~spl8_261)),
% 0.21/0.58    inference(superposition,[],[f549,f1552])).
% 0.21/0.58  fof(f1552,plain,(
% 0.21/0.58    sK3 = k1_setfam_1(k2_tarski(sK3,k2_struct_0(sK2))) | ~spl8_261),
% 0.21/0.58    inference(avatar_component_clause,[],[f1550])).
% 0.21/0.58  fof(f549,plain,(
% 0.21/0.58    ( ! [X0] : (~m1_subset_1(k1_setfam_1(k2_tarski(X0,k2_struct_0(sK2))),k1_zfmisc_1(k2_struct_0(sK2))) | ~v4_pre_topc(X0,sK0) | v4_pre_topc(k1_setfam_1(k2_tarski(X0,k2_struct_0(sK2))),sK2) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))) ) | ~spl8_79),
% 0.21/0.58    inference(avatar_component_clause,[],[f548])).
% 0.21/0.58  fof(f1553,plain,(
% 0.21/0.58    spl8_261 | ~spl8_251),
% 0.21/0.58    inference(avatar_split_clause,[],[f1548,f1500,f1550])).
% 0.21/0.58  fof(f1500,plain,(
% 0.21/0.58    spl8_251 <=> r1_tarski(sK3,k2_struct_0(sK2))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl8_251])])).
% 0.21/0.58  fof(f1548,plain,(
% 0.21/0.58    sK3 = k1_setfam_1(k2_tarski(sK3,k2_struct_0(sK2))) | ~spl8_251),
% 0.21/0.58    inference(resolution,[],[f1502,f64])).
% 0.21/0.58  fof(f64,plain,(
% 0.21/0.58    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_setfam_1(k2_tarski(X0,X1)) = X0) )),
% 0.21/0.58    inference(definition_unfolding,[],[f59,f58])).
% 0.21/0.58  fof(f58,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.21/0.58    inference(cnf_transformation,[],[f5])).
% 0.21/0.58  fof(f5,axiom,(
% 0.21/0.58    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.21/0.58  fof(f59,plain,(
% 0.21/0.58    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.21/0.58    inference(cnf_transformation,[],[f26])).
% 0.21/0.58  fof(f26,plain,(
% 0.21/0.58    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.58    inference(ennf_transformation,[],[f1])).
% 0.21/0.58  fof(f1,axiom,(
% 0.21/0.58    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.58  fof(f1502,plain,(
% 0.21/0.58    r1_tarski(sK3,k2_struct_0(sK2)) | ~spl8_251),
% 0.21/0.58    inference(avatar_component_clause,[],[f1500])).
% 0.21/0.58  fof(f1503,plain,(
% 0.21/0.58    spl8_251 | ~spl8_114 | ~spl8_238),
% 0.21/0.58    inference(avatar_split_clause,[],[f1489,f1435,f767,f1500])).
% 0.21/0.58  fof(f767,plain,(
% 0.21/0.58    spl8_114 <=> r1_tarski(k2_struct_0(k1_pre_topc(sK2,sK3)),k2_struct_0(sK2))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl8_114])])).
% 0.21/0.58  fof(f1435,plain,(
% 0.21/0.58    spl8_238 <=> sK3 = k2_struct_0(k1_pre_topc(sK2,sK3))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl8_238])])).
% 0.21/0.58  fof(f1489,plain,(
% 0.21/0.58    r1_tarski(sK3,k2_struct_0(sK2)) | (~spl8_114 | ~spl8_238)),
% 0.21/0.58    inference(backward_demodulation,[],[f769,f1437])).
% 0.21/0.58  fof(f1437,plain,(
% 0.21/0.58    sK3 = k2_struct_0(k1_pre_topc(sK2,sK3)) | ~spl8_238),
% 0.21/0.58    inference(avatar_component_clause,[],[f1435])).
% 0.21/0.58  fof(f769,plain,(
% 0.21/0.58    r1_tarski(k2_struct_0(k1_pre_topc(sK2,sK3)),k2_struct_0(sK2)) | ~spl8_114),
% 0.21/0.58    inference(avatar_component_clause,[],[f767])).
% 0.21/0.58  fof(f1438,plain,(
% 0.21/0.58    spl8_238 | ~spl8_134 | ~spl8_237),
% 0.21/0.58    inference(avatar_split_clause,[],[f1422,f1418,f864,f1435])).
% 0.21/0.58  fof(f864,plain,(
% 0.21/0.58    spl8_134 <=> k2_struct_0(k1_pre_topc(sK2,sK3)) = u1_struct_0(k1_pre_topc(sK2,sK3))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl8_134])])).
% 0.21/0.58  fof(f1418,plain,(
% 0.21/0.58    spl8_237 <=> sK3 = u1_struct_0(k1_pre_topc(sK2,sK3))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl8_237])])).
% 0.21/0.58  fof(f1422,plain,(
% 0.21/0.58    sK3 = k2_struct_0(k1_pre_topc(sK2,sK3)) | (~spl8_134 | ~spl8_237)),
% 0.21/0.58    inference(backward_demodulation,[],[f866,f1420])).
% 0.21/0.58  fof(f1420,plain,(
% 0.21/0.58    sK3 = u1_struct_0(k1_pre_topc(sK2,sK3)) | ~spl8_237),
% 0.21/0.58    inference(avatar_component_clause,[],[f1418])).
% 0.21/0.58  fof(f866,plain,(
% 0.21/0.58    k2_struct_0(k1_pre_topc(sK2,sK3)) = u1_struct_0(k1_pre_topc(sK2,sK3)) | ~spl8_134),
% 0.21/0.58    inference(avatar_component_clause,[],[f864])).
% 0.21/0.58  fof(f1421,plain,(
% 0.21/0.58    spl8_237 | ~spl8_15 | ~spl8_23),
% 0.21/0.58    inference(avatar_split_clause,[],[f1415,f198,f149,f1418])).
% 0.21/0.58  fof(f198,plain,(
% 0.21/0.58    spl8_23 <=> ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK2))) | u1_struct_0(k1_pre_topc(sK2,X1)) = X1)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).
% 0.21/0.58  fof(f1415,plain,(
% 0.21/0.58    sK3 = u1_struct_0(k1_pre_topc(sK2,sK3)) | (~spl8_15 | ~spl8_23)),
% 0.21/0.58    inference(resolution,[],[f199,f151])).
% 0.21/0.58  fof(f151,plain,(
% 0.21/0.58    m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK2))) | ~spl8_15),
% 0.21/0.58    inference(avatar_component_clause,[],[f149])).
% 0.21/0.58  fof(f199,plain,(
% 0.21/0.58    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK2))) | u1_struct_0(k1_pre_topc(sK2,X1)) = X1) ) | ~spl8_23),
% 0.21/0.58    inference(avatar_component_clause,[],[f198])).
% 0.21/0.58  fof(f867,plain,(
% 0.21/0.58    spl8_134 | ~spl8_133),
% 0.21/0.58    inference(avatar_split_clause,[],[f862,f858,f864])).
% 0.21/0.58  fof(f858,plain,(
% 0.21/0.58    spl8_133 <=> l1_struct_0(k1_pre_topc(sK2,sK3))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl8_133])])).
% 0.21/0.58  fof(f862,plain,(
% 0.21/0.58    k2_struct_0(k1_pre_topc(sK2,sK3)) = u1_struct_0(k1_pre_topc(sK2,sK3)) | ~spl8_133),
% 0.21/0.58    inference(resolution,[],[f860,f39])).
% 0.21/0.58  fof(f39,plain,(
% 0.21/0.58    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f19])).
% 0.21/0.58  fof(f19,plain,(
% 0.21/0.58    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.21/0.58    inference(ennf_transformation,[],[f6])).
% 0.21/0.58  fof(f6,axiom,(
% 0.21/0.58    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.21/0.58  fof(f860,plain,(
% 0.21/0.58    l1_struct_0(k1_pre_topc(sK2,sK3)) | ~spl8_133),
% 0.21/0.58    inference(avatar_component_clause,[],[f858])).
% 0.21/0.58  fof(f861,plain,(
% 0.21/0.58    spl8_133 | ~spl8_115),
% 0.21/0.58    inference(avatar_split_clause,[],[f846,f771,f858])).
% 0.21/0.58  fof(f771,plain,(
% 0.21/0.58    spl8_115 <=> l1_pre_topc(k1_pre_topc(sK2,sK3))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl8_115])])).
% 0.21/0.58  fof(f846,plain,(
% 0.21/0.58    l1_struct_0(k1_pre_topc(sK2,sK3)) | ~spl8_115),
% 0.21/0.58    inference(resolution,[],[f772,f40])).
% 0.21/0.58  fof(f40,plain,(
% 0.21/0.58    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f20])).
% 0.21/0.58  fof(f20,plain,(
% 0.21/0.58    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.58    inference(ennf_transformation,[],[f9])).
% 0.21/0.58  fof(f9,axiom,(
% 0.21/0.58    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.58  fof(f772,plain,(
% 0.21/0.58    l1_pre_topc(k1_pre_topc(sK2,sK3)) | ~spl8_115),
% 0.21/0.58    inference(avatar_component_clause,[],[f771])).
% 0.21/0.58  fof(f775,plain,(
% 0.21/0.58    spl8_115 | ~spl8_10 | ~spl8_113),
% 0.21/0.58    inference(avatar_split_clause,[],[f760,f753,f119,f771])).
% 0.21/0.58  fof(f119,plain,(
% 0.21/0.58    spl8_10 <=> l1_pre_topc(sK2)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 0.21/0.58  fof(f753,plain,(
% 0.21/0.58    spl8_113 <=> m1_pre_topc(k1_pre_topc(sK2,sK3),sK2)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl8_113])])).
% 0.21/0.58  fof(f760,plain,(
% 0.21/0.58    ~l1_pre_topc(sK2) | l1_pre_topc(k1_pre_topc(sK2,sK3)) | ~spl8_113),
% 0.21/0.58    inference(resolution,[],[f755,f51])).
% 0.21/0.58  fof(f51,plain,(
% 0.21/0.58    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | l1_pre_topc(X1)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f22])).
% 0.21/0.58  fof(f22,plain,(
% 0.21/0.58    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.58    inference(ennf_transformation,[],[f10])).
% 0.21/0.58  fof(f10,axiom,(
% 0.21/0.58    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.21/0.58  fof(f755,plain,(
% 0.21/0.58    m1_pre_topc(k1_pre_topc(sK2,sK3),sK2) | ~spl8_113),
% 0.21/0.58    inference(avatar_component_clause,[],[f753])).
% 0.21/0.58  fof(f774,plain,(
% 0.21/0.58    ~spl8_10 | spl8_114 | ~spl8_115 | ~spl8_113),
% 0.21/0.58    inference(avatar_split_clause,[],[f759,f753,f771,f767,f119])).
% 0.21/0.58  fof(f759,plain,(
% 0.21/0.58    ~l1_pre_topc(k1_pre_topc(sK2,sK3)) | r1_tarski(k2_struct_0(k1_pre_topc(sK2,sK3)),k2_struct_0(sK2)) | ~l1_pre_topc(sK2) | ~spl8_113),
% 0.21/0.58    inference(resolution,[],[f755,f50])).
% 0.21/0.58  fof(f50,plain,(
% 0.21/0.58    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X1) | r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) | ~l1_pre_topc(X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f21])).
% 0.21/0.58  fof(f21,plain,(
% 0.21/0.58    ! [X0] : (! [X1] : ((m1_pre_topc(X1,X0) <=> (! [X2] : ((r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.21/0.58    inference(ennf_transformation,[],[f7])).
% 0.21/0.58  fof(f7,axiom,(
% 0.21/0.58    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => (r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))))))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_pre_topc)).
% 0.21/0.58  fof(f756,plain,(
% 0.21/0.58    spl8_113 | ~spl8_15 | ~spl8_17),
% 0.21/0.58    inference(avatar_split_clause,[],[f750,f161,f149,f753])).
% 0.21/0.58  fof(f161,plain,(
% 0.21/0.58    spl8_17 <=> ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK2))) | m1_pre_topc(k1_pre_topc(sK2,X1),sK2))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).
% 0.21/0.58  fof(f750,plain,(
% 0.21/0.58    m1_pre_topc(k1_pre_topc(sK2,sK3),sK2) | (~spl8_15 | ~spl8_17)),
% 0.21/0.58    inference(resolution,[],[f162,f151])).
% 0.21/0.58  fof(f162,plain,(
% 0.21/0.58    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK2))) | m1_pre_topc(k1_pre_topc(sK2,X1),sK2)) ) | ~spl8_17),
% 0.21/0.58    inference(avatar_component_clause,[],[f161])).
% 0.21/0.58  fof(f550,plain,(
% 0.21/0.58    ~spl8_1 | spl8_79 | ~spl8_4 | ~spl8_8 | ~spl8_12),
% 0.21/0.58    inference(avatar_split_clause,[],[f546,f131,f107,f84,f548,f69])).
% 0.21/0.58  fof(f69,plain,(
% 0.21/0.58    spl8_1 <=> l1_pre_topc(sK0)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.21/0.58  fof(f84,plain,(
% 0.21/0.58    spl8_4 <=> m1_pre_topc(sK2,sK0)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.21/0.58  fof(f107,plain,(
% 0.21/0.58    spl8_8 <=> u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 0.21/0.58  fof(f131,plain,(
% 0.21/0.58    spl8_12 <=> u1_struct_0(sK2) = k2_struct_0(sK2)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).
% 0.21/0.58  fof(f546,plain,(
% 0.21/0.58    ( ! [X0] : (v4_pre_topc(k1_setfam_1(k2_tarski(X0,k2_struct_0(sK2))),sK2) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(k1_setfam_1(k2_tarski(X0,k2_struct_0(sK2))),k1_zfmisc_1(k2_struct_0(sK2))) | ~l1_pre_topc(sK0) | ~v4_pre_topc(X0,sK0)) ) | (~spl8_4 | ~spl8_8 | ~spl8_12)),
% 0.21/0.58    inference(forward_demodulation,[],[f545,f215])).
% 0.21/0.58  fof(f215,plain,(
% 0.21/0.58    ( ! [X2,X3] : (k9_subset_1(X2,X3,X2) = k1_setfam_1(k2_tarski(X3,X2))) )),
% 0.21/0.58    inference(resolution,[],[f65,f104])).
% 0.21/0.58  fof(f104,plain,(
% 0.21/0.58    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.21/0.58    inference(forward_demodulation,[],[f38,f37])).
% 0.21/0.58  fof(f37,plain,(
% 0.21/0.58    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.21/0.58    inference(cnf_transformation,[],[f2])).
% 0.21/0.58  fof(f2,axiom,(
% 0.21/0.58    ! [X0] : k2_subset_1(X0) = X0),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 0.21/0.58  fof(f38,plain,(
% 0.21/0.58    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.21/0.58    inference(cnf_transformation,[],[f3])).
% 0.21/0.58  fof(f3,axiom,(
% 0.21/0.58    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.21/0.58  fof(f65,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))) )),
% 0.21/0.58    inference(definition_unfolding,[],[f61,f58])).
% 0.21/0.58  fof(f61,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f29])).
% 0.21/0.58  fof(f29,plain,(
% 0.21/0.58    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.21/0.58    inference(ennf_transformation,[],[f4])).
% 0.21/0.58  fof(f4,axiom,(
% 0.21/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.21/0.58  fof(f545,plain,(
% 0.21/0.58    ( ! [X0] : (v4_pre_topc(k9_subset_1(k2_struct_0(sK2),X0,k2_struct_0(sK2)),sK2) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(k1_setfam_1(k2_tarski(X0,k2_struct_0(sK2))),k1_zfmisc_1(k2_struct_0(sK2))) | ~l1_pre_topc(sK0) | ~v4_pre_topc(X0,sK0)) ) | (~spl8_4 | ~spl8_8 | ~spl8_12)),
% 0.21/0.58    inference(forward_demodulation,[],[f544,f133])).
% 0.21/0.58  fof(f133,plain,(
% 0.21/0.58    u1_struct_0(sK2) = k2_struct_0(sK2) | ~spl8_12),
% 0.21/0.58    inference(avatar_component_clause,[],[f131])).
% 0.21/0.58  fof(f544,plain,(
% 0.21/0.58    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(k1_setfam_1(k2_tarski(X0,k2_struct_0(sK2))),k1_zfmisc_1(k2_struct_0(sK2))) | ~l1_pre_topc(sK0) | ~v4_pre_topc(X0,sK0) | v4_pre_topc(k9_subset_1(u1_struct_0(sK2),X0,k2_struct_0(sK2)),sK2)) ) | (~spl8_4 | ~spl8_8 | ~spl8_12)),
% 0.21/0.58    inference(forward_demodulation,[],[f543,f109])).
% 0.21/0.58  fof(f109,plain,(
% 0.21/0.58    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl8_8),
% 0.21/0.58    inference(avatar_component_clause,[],[f107])).
% 0.21/0.58  fof(f543,plain,(
% 0.21/0.58    ( ! [X0] : (~m1_subset_1(k1_setfam_1(k2_tarski(X0,k2_struct_0(sK2))),k1_zfmisc_1(k2_struct_0(sK2))) | ~l1_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(X0,sK0) | v4_pre_topc(k9_subset_1(u1_struct_0(sK2),X0,k2_struct_0(sK2)),sK2)) ) | (~spl8_4 | ~spl8_12)),
% 0.21/0.58    inference(forward_demodulation,[],[f542,f215])).
% 0.21/0.58  fof(f542,plain,(
% 0.21/0.58    ( ! [X0] : (~m1_subset_1(k9_subset_1(k2_struct_0(sK2),X0,k2_struct_0(sK2)),k1_zfmisc_1(k2_struct_0(sK2))) | ~l1_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(X0,sK0) | v4_pre_topc(k9_subset_1(u1_struct_0(sK2),X0,k2_struct_0(sK2)),sK2)) ) | (~spl8_4 | ~spl8_12)),
% 0.21/0.58    inference(forward_demodulation,[],[f538,f133])).
% 0.21/0.58  fof(f538,plain,(
% 0.21/0.58    ( ! [X0] : (~l1_pre_topc(sK0) | ~m1_subset_1(k9_subset_1(u1_struct_0(sK2),X0,k2_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK2))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(X0,sK0) | v4_pre_topc(k9_subset_1(u1_struct_0(sK2),X0,k2_struct_0(sK2)),sK2)) ) | ~spl8_4),
% 0.21/0.58    inference(resolution,[],[f67,f86])).
% 0.21/0.58  fof(f86,plain,(
% 0.21/0.58    m1_pre_topc(sK2,sK0) | ~spl8_4),
% 0.21/0.58    inference(avatar_component_clause,[],[f84])).
% 0.21/0.58  fof(f67,plain,(
% 0.21/0.58    ( ! [X0,X3,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~m1_subset_1(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X3,X0) | v4_pre_topc(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),X1)) )),
% 0.21/0.58    inference(equality_resolution,[],[f56])).
% 0.21/0.58  fof(f56,plain,(
% 0.21/0.58    ( ! [X2,X0,X3,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X3,X0) | k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | v4_pre_topc(X2,X1)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f24])).
% 0.21/0.58  fof(f24,plain,(
% 0.21/0.58    ! [X0] : (! [X1] : (! [X2] : ((v4_pre_topc(X2,X1) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.58    inference(ennf_transformation,[],[f13])).
% 0.21/0.58  fof(f13,axiom,(
% 0.21/0.58    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => (v4_pre_topc(X2,X1) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))))))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_pre_topc)).
% 0.21/0.58  fof(f200,plain,(
% 0.21/0.58    ~spl8_10 | spl8_23 | ~spl8_12),
% 0.21/0.58    inference(avatar_split_clause,[],[f192,f131,f198,f119])).
% 0.21/0.58  fof(f192,plain,(
% 0.21/0.58    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK2))) | ~l1_pre_topc(sK2) | u1_struct_0(k1_pre_topc(sK2,X1)) = X1) ) | ~spl8_12),
% 0.21/0.58    inference(superposition,[],[f57,f133])).
% 0.21/0.58  fof(f57,plain,(
% 0.21/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | u1_struct_0(k1_pre_topc(X0,X1)) = X1) )),
% 0.21/0.58    inference(cnf_transformation,[],[f25])).
% 0.21/0.58  fof(f25,plain,(
% 0.21/0.58    ! [X0] : (! [X1] : (u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.58    inference(ennf_transformation,[],[f11])).
% 0.21/0.58  fof(f11,axiom,(
% 0.21/0.58    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => u1_struct_0(k1_pre_topc(X0,X1)) = X1))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_pre_topc)).
% 0.21/0.58  fof(f163,plain,(
% 0.21/0.58    ~spl8_10 | spl8_17 | ~spl8_12),
% 0.21/0.58    inference(avatar_split_clause,[],[f155,f131,f161,f119])).
% 0.21/0.58  fof(f155,plain,(
% 0.21/0.58    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK2))) | ~l1_pre_topc(sK2) | m1_pre_topc(k1_pre_topc(sK2,X1),sK2)) ) | ~spl8_12),
% 0.21/0.58    inference(superposition,[],[f60,f133])).
% 0.21/0.58  fof(f60,plain,(
% 0.21/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | m1_pre_topc(k1_pre_topc(X0,X1),X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f28])).
% 0.21/0.58  fof(f28,plain,(
% 0.21/0.58    ! [X0,X1] : (m1_pre_topc(k1_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.58    inference(flattening,[],[f27])).
% 0.21/0.58  fof(f27,plain,(
% 0.21/0.58    ! [X0,X1] : (m1_pre_topc(k1_pre_topc(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.21/0.58    inference(ennf_transformation,[],[f16])).
% 0.21/0.58  fof(f16,plain,(
% 0.21/0.58    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_pre_topc(k1_pre_topc(X0,X1),X0))),
% 0.21/0.58    inference(pure_predicate_removal,[],[f8])).
% 0.21/0.58  fof(f8,axiom,(
% 0.21/0.58    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => (m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_pre_topc)).
% 0.21/0.58  fof(f152,plain,(
% 0.21/0.58    spl8_15 | ~spl8_6 | ~spl8_12),
% 0.21/0.58    inference(avatar_split_clause,[],[f147,f131,f94,f149])).
% 0.21/0.58  fof(f94,plain,(
% 0.21/0.58    spl8_6 <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.21/0.58  fof(f147,plain,(
% 0.21/0.58    m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK2))) | (~spl8_6 | ~spl8_12)),
% 0.21/0.58    inference(backward_demodulation,[],[f96,f133])).
% 0.21/0.58  fof(f96,plain,(
% 0.21/0.58    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) | ~spl8_6),
% 0.21/0.58    inference(avatar_component_clause,[],[f94])).
% 0.21/0.58  fof(f134,plain,(
% 0.21/0.58    spl8_12 | ~spl8_11),
% 0.21/0.58    inference(avatar_split_clause,[],[f129,f125,f131])).
% 0.21/0.58  fof(f125,plain,(
% 0.21/0.58    spl8_11 <=> l1_struct_0(sK2)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 0.21/0.58  fof(f129,plain,(
% 0.21/0.58    u1_struct_0(sK2) = k2_struct_0(sK2) | ~spl8_11),
% 0.21/0.58    inference(resolution,[],[f127,f39])).
% 0.21/0.58  fof(f127,plain,(
% 0.21/0.58    l1_struct_0(sK2) | ~spl8_11),
% 0.21/0.58    inference(avatar_component_clause,[],[f125])).
% 0.21/0.58  fof(f128,plain,(
% 0.21/0.58    spl8_11 | ~spl8_10),
% 0.21/0.58    inference(avatar_split_clause,[],[f123,f119,f125])).
% 0.21/0.58  fof(f123,plain,(
% 0.21/0.58    l1_struct_0(sK2) | ~spl8_10),
% 0.21/0.58    inference(resolution,[],[f121,f40])).
% 0.21/0.58  fof(f121,plain,(
% 0.21/0.58    l1_pre_topc(sK2) | ~spl8_10),
% 0.21/0.58    inference(avatar_component_clause,[],[f119])).
% 0.21/0.58  fof(f122,plain,(
% 0.21/0.58    spl8_10 | ~spl8_1 | ~spl8_4),
% 0.21/0.58    inference(avatar_split_clause,[],[f117,f84,f69,f119])).
% 0.21/0.58  fof(f117,plain,(
% 0.21/0.58    ~l1_pre_topc(sK0) | l1_pre_topc(sK2) | ~spl8_4),
% 0.21/0.58    inference(resolution,[],[f51,f86])).
% 0.21/0.58  fof(f116,plain,(
% 0.21/0.58    spl8_9 | ~spl8_2 | ~spl8_8),
% 0.21/0.58    inference(avatar_split_clause,[],[f111,f107,f74,f113])).
% 0.21/0.58  fof(f74,plain,(
% 0.21/0.58    spl8_2 <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.21/0.58  fof(f111,plain,(
% 0.21/0.58    m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK0))) | (~spl8_2 | ~spl8_8)),
% 0.21/0.58    inference(backward_demodulation,[],[f76,f109])).
% 0.21/0.58  fof(f76,plain,(
% 0.21/0.58    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl8_2),
% 0.21/0.58    inference(avatar_component_clause,[],[f74])).
% 0.21/0.58  fof(f110,plain,(
% 0.21/0.58    spl8_8 | ~spl8_7),
% 0.21/0.58    inference(avatar_split_clause,[],[f105,f100,f107])).
% 0.21/0.58  fof(f100,plain,(
% 0.21/0.58    spl8_7 <=> l1_struct_0(sK0)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 0.21/0.58  fof(f105,plain,(
% 0.21/0.58    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl8_7),
% 0.21/0.58    inference(resolution,[],[f39,f102])).
% 0.21/0.58  fof(f102,plain,(
% 0.21/0.58    l1_struct_0(sK0) | ~spl8_7),
% 0.21/0.58    inference(avatar_component_clause,[],[f100])).
% 0.21/0.58  fof(f103,plain,(
% 0.21/0.58    spl8_7 | ~spl8_1),
% 0.21/0.58    inference(avatar_split_clause,[],[f98,f69,f100])).
% 0.21/0.58  fof(f98,plain,(
% 0.21/0.58    l1_struct_0(sK0) | ~spl8_1),
% 0.21/0.58    inference(resolution,[],[f40,f71])).
% 0.21/0.58  fof(f71,plain,(
% 0.21/0.58    l1_pre_topc(sK0) | ~spl8_1),
% 0.21/0.58    inference(avatar_component_clause,[],[f69])).
% 0.21/0.58  fof(f97,plain,(
% 0.21/0.58    spl8_6),
% 0.21/0.58    inference(avatar_split_clause,[],[f30,f94])).
% 0.21/0.58  fof(f30,plain,(
% 0.21/0.58    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.21/0.58    inference(cnf_transformation,[],[f18])).
% 0.21/0.58  fof(f18,plain,(
% 0.21/0.58    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~v4_pre_topc(X3,X2) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v4_pre_topc(X1,X0) & m1_pre_topc(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.21/0.58    inference(flattening,[],[f17])).
% 0.21/0.58  fof(f17,plain,(
% 0.21/0.58    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : ((~v4_pre_topc(X3,X2) & X1 = X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v4_pre_topc(X1,X0)) & m1_pre_topc(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.21/0.58    inference(ennf_transformation,[],[f15])).
% 0.21/0.58  fof(f15,negated_conjecture,(
% 0.21/0.58    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_pre_topc(X2,X0) => (v4_pre_topc(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) => (X1 = X3 => v4_pre_topc(X3,X2)))))))),
% 0.21/0.58    inference(negated_conjecture,[],[f14])).
% 0.21/0.58  fof(f14,conjecture,(
% 0.21/0.58    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_pre_topc(X2,X0) => (v4_pre_topc(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) => (X1 = X3 => v4_pre_topc(X3,X2)))))))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_tops_2)).
% 0.21/0.58  fof(f92,plain,(
% 0.21/0.58    ~spl8_5),
% 0.21/0.58    inference(avatar_split_clause,[],[f32,f89])).
% 0.21/0.58  fof(f32,plain,(
% 0.21/0.58    ~v4_pre_topc(sK3,sK2)),
% 0.21/0.58    inference(cnf_transformation,[],[f18])).
% 0.21/0.58  fof(f87,plain,(
% 0.21/0.58    spl8_4),
% 0.21/0.58    inference(avatar_split_clause,[],[f33,f84])).
% 0.21/0.58  fof(f33,plain,(
% 0.21/0.58    m1_pre_topc(sK2,sK0)),
% 0.21/0.58    inference(cnf_transformation,[],[f18])).
% 0.21/0.58  fof(f82,plain,(
% 0.21/0.58    spl8_3),
% 0.21/0.58    inference(avatar_split_clause,[],[f63,f79])).
% 0.21/0.58  fof(f63,plain,(
% 0.21/0.58    v4_pre_topc(sK3,sK0)),
% 0.21/0.58    inference(definition_unfolding,[],[f34,f31])).
% 0.21/0.58  fof(f31,plain,(
% 0.21/0.58    sK1 = sK3),
% 0.21/0.58    inference(cnf_transformation,[],[f18])).
% 0.21/0.58  fof(f34,plain,(
% 0.21/0.58    v4_pre_topc(sK1,sK0)),
% 0.21/0.58    inference(cnf_transformation,[],[f18])).
% 0.21/0.58  fof(f77,plain,(
% 0.21/0.58    spl8_2),
% 0.21/0.58    inference(avatar_split_clause,[],[f62,f74])).
% 0.21/0.58  fof(f62,plain,(
% 0.21/0.58    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.58    inference(definition_unfolding,[],[f35,f31])).
% 0.21/0.58  fof(f35,plain,(
% 0.21/0.58    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.58    inference(cnf_transformation,[],[f18])).
% 0.21/0.58  fof(f72,plain,(
% 0.21/0.58    spl8_1),
% 0.21/0.58    inference(avatar_split_clause,[],[f36,f69])).
% 0.21/0.58  fof(f36,plain,(
% 0.21/0.58    l1_pre_topc(sK0)),
% 0.21/0.58    inference(cnf_transformation,[],[f18])).
% 0.21/0.58  % SZS output end Proof for theBenchmark
% 0.21/0.58  % (8370)------------------------------
% 0.21/0.58  % (8370)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (8370)Termination reason: Refutation
% 0.21/0.58  
% 0.21/0.58  % (8370)Memory used [KB]: 11897
% 0.21/0.58  % (8370)Time elapsed: 0.153 s
% 0.21/0.58  % (8370)------------------------------
% 0.21/0.58  % (8370)------------------------------
% 0.21/0.58  % (8353)Success in time 0.222 s
%------------------------------------------------------------------------------
