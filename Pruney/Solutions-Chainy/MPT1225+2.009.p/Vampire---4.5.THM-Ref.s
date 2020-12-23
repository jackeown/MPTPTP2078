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
% DateTime   : Thu Dec  3 13:10:54 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 272 expanded)
%              Number of leaves         :   34 ( 125 expanded)
%              Depth                    :    8
%              Number of atoms          :  415 ( 951 expanded)
%              Number of equality atoms :   56 ( 150 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f427,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f51,f56,f61,f66,f71,f78,f111,f142,f147,f151,f174,f188,f195,f200,f206,f217,f222,f280,f284,f307,f353,f422,f426])).

fof(f426,plain,
    ( ~ spl3_27
    | ~ spl3_35
    | spl3_45 ),
    inference(avatar_contradiction_clause,[],[f424])).

fof(f424,plain,
    ( $false
    | ~ spl3_27
    | ~ spl3_35
    | spl3_45 ),
    inference(unit_resulting_resolution,[],[f306,f421,f221])).

fof(f221,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK0))
        | r1_tarski(X0,k2_pre_topc(sK0,X0)) )
    | ~ spl3_27 ),
    inference(avatar_component_clause,[],[f220])).

fof(f220,plain,
    ( spl3_27
  <=> ! [X0] :
        ( r1_tarski(X0,k2_pre_topc(sK0,X0))
        | ~ r1_tarski(X0,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f421,plain,
    ( ~ r1_tarski(k3_xboole_0(sK1,sK2),k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)))
    | spl3_45 ),
    inference(avatar_component_clause,[],[f419])).

fof(f419,plain,
    ( spl3_45
  <=> r1_tarski(k3_xboole_0(sK1,sK2),k2_pre_topc(sK0,k3_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).

fof(f306,plain,
    ( ! [X0] : r1_tarski(k3_xboole_0(sK1,X0),u1_struct_0(sK0))
    | ~ spl3_35 ),
    inference(avatar_component_clause,[],[f305])).

fof(f305,plain,
    ( spl3_35
  <=> ! [X0] : r1_tarski(k3_xboole_0(sK1,X0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).

fof(f422,plain,
    ( ~ spl3_45
    | spl3_26
    | ~ spl3_39 ),
    inference(avatar_split_clause,[],[f400,f350,f214,f419])).

fof(f214,plain,
    ( spl3_26
  <=> k3_xboole_0(sK1,sK2) = k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f350,plain,
    ( spl3_39
  <=> r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).

fof(f400,plain,
    ( ~ r1_tarski(k3_xboole_0(sK1,sK2),k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)))
    | spl3_26
    | ~ spl3_39 ),
    inference(subsumption_resolution,[],[f398,f216])).

fof(f216,plain,
    ( k3_xboole_0(sK1,sK2) != k2_pre_topc(sK0,k3_xboole_0(sK1,sK2))
    | spl3_26 ),
    inference(avatar_component_clause,[],[f214])).

fof(f398,plain,
    ( ~ r1_tarski(k3_xboole_0(sK1,sK2),k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)))
    | k3_xboole_0(sK1,sK2) = k2_pre_topc(sK0,k3_xboole_0(sK1,sK2))
    | ~ spl3_39 ),
    inference(resolution,[],[f352,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f352,plain,
    ( r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(sK1,sK2))
    | ~ spl3_39 ),
    inference(avatar_component_clause,[],[f350])).

fof(f353,plain,
    ( spl3_39
    | ~ spl3_5
    | ~ spl3_16
    | ~ spl3_25
    | ~ spl3_31 ),
    inference(avatar_split_clause,[],[f291,f278,f203,f140,f68,f350])).

fof(f68,plain,
    ( spl3_5
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f140,plain,
    ( spl3_16
  <=> ! [X1] : k9_subset_1(u1_struct_0(sK0),X1,sK2) = k3_xboole_0(X1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f203,plain,
    ( spl3_25
  <=> sK2 = k2_pre_topc(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f278,plain,
    ( spl3_31
  <=> ! [X0] :
        ( r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,X0)),k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f291,plain,
    ( r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(sK1,sK2))
    | ~ spl3_5
    | ~ spl3_16
    | ~ spl3_25
    | ~ spl3_31 ),
    inference(forward_demodulation,[],[f290,f141])).

fof(f141,plain,
    ( ! [X1] : k9_subset_1(u1_struct_0(sK0),X1,sK2) = k3_xboole_0(X1,sK2)
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f140])).

fof(f290,plain,
    ( r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ spl3_5
    | ~ spl3_25
    | ~ spl3_31 ),
    inference(forward_demodulation,[],[f286,f205])).

fof(f205,plain,
    ( sK2 = k2_pre_topc(sK0,sK2)
    | ~ spl3_25 ),
    inference(avatar_component_clause,[],[f203])).

fof(f286,plain,
    ( r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,sK2)))
    | ~ spl3_5
    | ~ spl3_31 ),
    inference(resolution,[],[f279,f70])).

fof(f70,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f68])).

fof(f279,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,X0)),k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X0))) )
    | ~ spl3_31 ),
    inference(avatar_component_clause,[],[f278])).

fof(f307,plain,
    ( spl3_35
    | ~ spl3_32 ),
    inference(avatar_split_clause,[],[f297,f282,f305])).

fof(f282,plain,
    ( spl3_32
  <=> ! [X13,X12] :
        ( ~ r1_tarski(X12,sK1)
        | r1_tarski(k3_xboole_0(X12,X13),u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f297,plain,
    ( ! [X0] : r1_tarski(k3_xboole_0(sK1,X0),u1_struct_0(sK0))
    | ~ spl3_32 ),
    inference(resolution,[],[f283,f45])).

fof(f45,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f283,plain,
    ( ! [X12,X13] :
        ( ~ r1_tarski(X12,sK1)
        | r1_tarski(k3_xboole_0(X12,X13),u1_struct_0(sK0)) )
    | ~ spl3_32 ),
    inference(avatar_component_clause,[],[f282])).

fof(f284,plain,
    ( spl3_32
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f239,f75,f282])).

fof(f75,plain,
    ( spl3_6
  <=> r1_tarski(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f239,plain,
    ( ! [X12,X13] :
        ( ~ r1_tarski(X12,sK1)
        | r1_tarski(k3_xboole_0(X12,X13),u1_struct_0(sK0)) )
    | ~ spl3_6 ),
    inference(resolution,[],[f113,f77])).

fof(f77,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f75])).

fof(f113,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1)
      | r1_tarski(k3_xboole_0(X0,X3),X2) ) ),
    inference(resolution,[],[f89,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f89,plain,(
    ! [X4,X2,X3] :
      ( r1_tarski(k3_xboole_0(X2,X4),X3)
      | ~ r1_tarski(X2,X3) ) ),
    inference(resolution,[],[f44,f37])).

fof(f37,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f280,plain,
    ( spl3_31
    | ~ spl3_4
    | ~ spl3_22
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f210,f192,f186,f63,f278])).

fof(f63,plain,
    ( spl3_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f186,plain,
    ( spl3_22
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X1,X0)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f192,plain,
    ( spl3_23
  <=> sK1 = k2_pre_topc(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f210,plain,
    ( ! [X0] :
        ( r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,X0)),k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl3_4
    | ~ spl3_22
    | ~ spl3_23 ),
    inference(forward_demodulation,[],[f207,f194])).

fof(f194,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f192])).

fof(f207,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,X0)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,X0))) )
    | ~ spl3_4
    | ~ spl3_22 ),
    inference(resolution,[],[f187,f65])).

fof(f65,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f63])).

fof(f187,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X1,X0)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X0))) )
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f186])).

fof(f222,plain,
    ( spl3_27
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f154,f149,f220])).

fof(f149,plain,
    ( spl3_18
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(X0,k2_pre_topc(sK0,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f154,plain,
    ( ! [X0] :
        ( r1_tarski(X0,k2_pre_topc(sK0,X0))
        | ~ r1_tarski(X0,u1_struct_0(sK0)) )
    | ~ spl3_18 ),
    inference(resolution,[],[f150,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f150,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(X0,k2_pre_topc(sK0,X0)) )
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f149])).

fof(f217,plain,
    ( ~ spl3_26
    | ~ spl3_16
    | spl3_24
    | ~ spl3_25 ),
    inference(avatar_split_clause,[],[f212,f203,f197,f140,f214])).

fof(f197,plain,
    ( spl3_24
  <=> k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f212,plain,
    ( k3_xboole_0(sK1,sK2) != k2_pre_topc(sK0,k3_xboole_0(sK1,sK2))
    | ~ spl3_16
    | spl3_24
    | ~ spl3_25 ),
    inference(forward_demodulation,[],[f211,f141])).

fof(f211,plain,
    ( k9_subset_1(u1_struct_0(sK0),sK1,sK2) != k2_pre_topc(sK0,k3_xboole_0(sK1,sK2))
    | spl3_24
    | ~ spl3_25 ),
    inference(backward_demodulation,[],[f199,f205])).

fof(f199,plain,
    ( k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,sK2))
    | spl3_24 ),
    inference(avatar_component_clause,[],[f197])).

fof(f206,plain,
    ( spl3_25
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f181,f172,f68,f58,f203])).

fof(f58,plain,
    ( spl3_3
  <=> v4_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f172,plain,
    ( spl3_21
  <=> ! [X0] :
        ( ~ v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_pre_topc(sK0,X0) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f181,plain,
    ( sK2 = k2_pre_topc(sK0,sK2)
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_21 ),
    inference(subsumption_resolution,[],[f179,f70])).

fof(f179,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | sK2 = k2_pre_topc(sK0,sK2)
    | ~ spl3_3
    | ~ spl3_21 ),
    inference(resolution,[],[f173,f60])).

fof(f60,plain,
    ( v4_pre_topc(sK2,sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f58])).

fof(f173,plain,
    ( ! [X0] :
        ( ~ v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_pre_topc(sK0,X0) = X0 )
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f172])).

fof(f200,plain,
    ( ~ spl3_24
    | ~ spl3_2
    | ~ spl3_4
    | spl3_17
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f190,f172,f144,f63,f53,f197])).

fof(f53,plain,
    ( spl3_2
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f144,plain,
    ( spl3_17
  <=> k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)) = k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f190,plain,
    ( k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,sK2))
    | ~ spl3_2
    | ~ spl3_4
    | spl3_17
    | ~ spl3_21 ),
    inference(backward_demodulation,[],[f146,f180])).

fof(f180,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_21 ),
    inference(subsumption_resolution,[],[f178,f65])).

fof(f178,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl3_2
    | ~ spl3_21 ),
    inference(resolution,[],[f173,f55])).

fof(f55,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f53])).

fof(f146,plain,
    ( k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)) != k2_pre_topc(sK0,k3_xboole_0(sK1,sK2))
    | spl3_17 ),
    inference(avatar_component_clause,[],[f144])).

fof(f195,plain,
    ( spl3_23
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f180,f172,f63,f53,f192])).

fof(f188,plain,
    ( spl3_22
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f124,f48,f186])).

fof(f48,plain,
    ( spl3_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f124,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X1,X0)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X0))) )
    | ~ spl3_1 ),
    inference(resolution,[],[f36,f50])).

fof(f50,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f48])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_pre_topc)).

fof(f174,plain,
    ( spl3_21
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f105,f48,f172])).

fof(f105,plain,
    ( ! [X0] :
        ( ~ v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_pre_topc(sK0,X0) = X0 )
    | ~ spl3_1 ),
    inference(resolution,[],[f34,f50])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

fof(f151,plain,
    ( spl3_18
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f93,f48,f149])).

fof(f93,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(X0,k2_pre_topc(sK0,X0)) )
    | ~ spl3_1 ),
    inference(resolution,[],[f33,f50])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(X1,k2_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).

fof(f147,plain,
    ( ~ spl3_17
    | ~ spl3_5
    | spl3_10 ),
    inference(avatar_split_clause,[],[f138,f108,f68,f144])).

fof(f108,plain,
    ( spl3_10
  <=> k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f138,plain,
    ( k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)) != k2_pre_topc(sK0,k3_xboole_0(sK1,sK2))
    | ~ spl3_5
    | spl3_10 ),
    inference(backward_demodulation,[],[f110,f99])).

fof(f99,plain,
    ( ! [X1] : k9_subset_1(u1_struct_0(sK0),X1,sK2) = k3_xboole_0(X1,sK2)
    | ~ spl3_5 ),
    inference(resolution,[],[f43,f70])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f110,plain,
    ( k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)) != k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))
    | spl3_10 ),
    inference(avatar_component_clause,[],[f108])).

fof(f142,plain,
    ( spl3_16
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f99,f68,f140])).

fof(f111,plain,(
    ~ spl3_10 ),
    inference(avatar_split_clause,[],[f32,f108])).

fof(f32,plain,(
    k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)) != k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)) != k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))
    & v4_pre_topc(sK2,sK0)
    & v4_pre_topc(sK1,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f22,f21,f20])).

fof(f20,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) != k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
                & v4_pre_topc(X2,X0)
                & v4_pre_topc(X1,X0)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X1,X2)) != k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X2))
              & v4_pre_topc(X2,sK0)
              & v4_pre_topc(X1,sK0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X1,X2)) != k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X2))
            & v4_pre_topc(X2,sK0)
            & v4_pre_topc(X1,sK0)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,X2)) != k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,X2))
          & v4_pre_topc(X2,sK0)
          & v4_pre_topc(sK1,sK0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X2] :
        ( k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,X2)) != k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,X2))
        & v4_pre_topc(X2,sK0)
        & v4_pre_topc(sK1,sK0)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)) != k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))
      & v4_pre_topc(sK2,sK0)
      & v4_pre_topc(sK1,sK0)
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) != k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              & v4_pre_topc(X2,X0)
              & v4_pre_topc(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) != k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              & v4_pre_topc(X2,X0)
              & v4_pre_topc(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v4_pre_topc(X2,X0)
                    & v4_pre_topc(X1,X0) )
                 => k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v4_pre_topc(X2,X0)
                  & v4_pre_topc(X1,X0) )
               => k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_tops_1)).

fof(f78,plain,
    ( spl3_6
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f72,f63,f75])).

fof(f72,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl3_4 ),
    inference(resolution,[],[f41,f65])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f71,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f29,f68])).

fof(f29,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f23])).

fof(f66,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f28,f63])).

fof(f28,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f23])).

fof(f61,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f31,f58])).

fof(f31,plain,(
    v4_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f56,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f30,f53])).

fof(f30,plain,(
    v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f51,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f27,f48])).

fof(f27,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:04:53 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.48  % (3702)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.48  % (3710)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.49  % (3702)Refutation found. Thanks to Tanya!
% 0.20/0.49  % SZS status Theorem for theBenchmark
% 0.20/0.50  % (3701)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.50  % (3705)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.50  % SZS output start Proof for theBenchmark
% 0.20/0.50  fof(f427,plain,(
% 0.20/0.50    $false),
% 0.20/0.50    inference(avatar_sat_refutation,[],[f51,f56,f61,f66,f71,f78,f111,f142,f147,f151,f174,f188,f195,f200,f206,f217,f222,f280,f284,f307,f353,f422,f426])).
% 0.20/0.50  fof(f426,plain,(
% 0.20/0.50    ~spl3_27 | ~spl3_35 | spl3_45),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f424])).
% 0.20/0.50  fof(f424,plain,(
% 0.20/0.50    $false | (~spl3_27 | ~spl3_35 | spl3_45)),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f306,f421,f221])).
% 0.20/0.50  fof(f221,plain,(
% 0.20/0.50    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK0)) | r1_tarski(X0,k2_pre_topc(sK0,X0))) ) | ~spl3_27),
% 0.20/0.50    inference(avatar_component_clause,[],[f220])).
% 0.20/0.50  fof(f220,plain,(
% 0.20/0.50    spl3_27 <=> ! [X0] : (r1_tarski(X0,k2_pre_topc(sK0,X0)) | ~r1_tarski(X0,u1_struct_0(sK0)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 0.20/0.50  fof(f421,plain,(
% 0.20/0.50    ~r1_tarski(k3_xboole_0(sK1,sK2),k2_pre_topc(sK0,k3_xboole_0(sK1,sK2))) | spl3_45),
% 0.20/0.50    inference(avatar_component_clause,[],[f419])).
% 0.20/0.50  fof(f419,plain,(
% 0.20/0.50    spl3_45 <=> r1_tarski(k3_xboole_0(sK1,sK2),k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).
% 0.20/0.50  fof(f306,plain,(
% 0.20/0.50    ( ! [X0] : (r1_tarski(k3_xboole_0(sK1,X0),u1_struct_0(sK0))) ) | ~spl3_35),
% 0.20/0.50    inference(avatar_component_clause,[],[f305])).
% 0.20/0.50  fof(f305,plain,(
% 0.20/0.50    spl3_35 <=> ! [X0] : r1_tarski(k3_xboole_0(sK1,X0),u1_struct_0(sK0))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).
% 0.20/0.50  fof(f422,plain,(
% 0.20/0.50    ~spl3_45 | spl3_26 | ~spl3_39),
% 0.20/0.50    inference(avatar_split_clause,[],[f400,f350,f214,f419])).
% 0.20/0.50  fof(f214,plain,(
% 0.20/0.50    spl3_26 <=> k3_xboole_0(sK1,sK2) = k2_pre_topc(sK0,k3_xboole_0(sK1,sK2))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 0.20/0.50  fof(f350,plain,(
% 0.20/0.50    spl3_39 <=> r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(sK1,sK2))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).
% 0.20/0.50  fof(f400,plain,(
% 0.20/0.50    ~r1_tarski(k3_xboole_0(sK1,sK2),k2_pre_topc(sK0,k3_xboole_0(sK1,sK2))) | (spl3_26 | ~spl3_39)),
% 0.20/0.50    inference(subsumption_resolution,[],[f398,f216])).
% 0.20/0.50  fof(f216,plain,(
% 0.20/0.50    k3_xboole_0(sK1,sK2) != k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)) | spl3_26),
% 0.20/0.50    inference(avatar_component_clause,[],[f214])).
% 0.20/0.50  fof(f398,plain,(
% 0.20/0.50    ~r1_tarski(k3_xboole_0(sK1,sK2),k2_pre_topc(sK0,k3_xboole_0(sK1,sK2))) | k3_xboole_0(sK1,sK2) = k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)) | ~spl3_39),
% 0.20/0.50    inference(resolution,[],[f352,f40])).
% 0.20/0.50  fof(f40,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.20/0.50    inference(cnf_transformation,[],[f25])).
% 0.20/0.50  fof(f25,plain,(
% 0.20/0.50    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.50    inference(flattening,[],[f24])).
% 0.20/0.50  fof(f24,plain,(
% 0.20/0.50    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.50    inference(nnf_transformation,[],[f1])).
% 0.20/0.50  fof(f1,axiom,(
% 0.20/0.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.50  fof(f352,plain,(
% 0.20/0.50    r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(sK1,sK2)) | ~spl3_39),
% 0.20/0.50    inference(avatar_component_clause,[],[f350])).
% 0.20/0.50  fof(f353,plain,(
% 0.20/0.50    spl3_39 | ~spl3_5 | ~spl3_16 | ~spl3_25 | ~spl3_31),
% 0.20/0.50    inference(avatar_split_clause,[],[f291,f278,f203,f140,f68,f350])).
% 0.20/0.50  fof(f68,plain,(
% 0.20/0.50    spl3_5 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.50  fof(f140,plain,(
% 0.20/0.50    spl3_16 <=> ! [X1] : k9_subset_1(u1_struct_0(sK0),X1,sK2) = k3_xboole_0(X1,sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.20/0.50  fof(f203,plain,(
% 0.20/0.50    spl3_25 <=> sK2 = k2_pre_topc(sK0,sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 0.20/0.50  fof(f278,plain,(
% 0.20/0.50    spl3_31 <=> ! [X0] : (r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,X0)),k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 0.20/0.50  fof(f291,plain,(
% 0.20/0.50    r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(sK1,sK2)) | (~spl3_5 | ~spl3_16 | ~spl3_25 | ~spl3_31)),
% 0.20/0.50    inference(forward_demodulation,[],[f290,f141])).
% 0.20/0.50  fof(f141,plain,(
% 0.20/0.50    ( ! [X1] : (k9_subset_1(u1_struct_0(sK0),X1,sK2) = k3_xboole_0(X1,sK2)) ) | ~spl3_16),
% 0.20/0.50    inference(avatar_component_clause,[],[f140])).
% 0.20/0.50  fof(f290,plain,(
% 0.20/0.50    r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),sK1,sK2)) | (~spl3_5 | ~spl3_25 | ~spl3_31)),
% 0.20/0.50    inference(forward_demodulation,[],[f286,f205])).
% 0.20/0.50  fof(f205,plain,(
% 0.20/0.50    sK2 = k2_pre_topc(sK0,sK2) | ~spl3_25),
% 0.20/0.50    inference(avatar_component_clause,[],[f203])).
% 0.20/0.50  fof(f286,plain,(
% 0.20/0.50    r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,sK2))) | (~spl3_5 | ~spl3_31)),
% 0.20/0.50    inference(resolution,[],[f279,f70])).
% 0.20/0.50  fof(f70,plain,(
% 0.20/0.50    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_5),
% 0.20/0.50    inference(avatar_component_clause,[],[f68])).
% 0.20/0.50  fof(f279,plain,(
% 0.20/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,X0)),k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X0)))) ) | ~spl3_31),
% 0.20/0.50    inference(avatar_component_clause,[],[f278])).
% 0.20/0.50  fof(f307,plain,(
% 0.20/0.50    spl3_35 | ~spl3_32),
% 0.20/0.50    inference(avatar_split_clause,[],[f297,f282,f305])).
% 0.20/0.50  fof(f282,plain,(
% 0.20/0.50    spl3_32 <=> ! [X13,X12] : (~r1_tarski(X12,sK1) | r1_tarski(k3_xboole_0(X12,X13),u1_struct_0(sK0)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 0.20/0.50  fof(f297,plain,(
% 0.20/0.50    ( ! [X0] : (r1_tarski(k3_xboole_0(sK1,X0),u1_struct_0(sK0))) ) | ~spl3_32),
% 0.20/0.50    inference(resolution,[],[f283,f45])).
% 0.20/0.50  fof(f45,plain,(
% 0.20/0.50    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.20/0.50    inference(equality_resolution,[],[f39])).
% 0.20/0.50  fof(f39,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.20/0.50    inference(cnf_transformation,[],[f25])).
% 0.20/0.50  fof(f283,plain,(
% 0.20/0.50    ( ! [X12,X13] : (~r1_tarski(X12,sK1) | r1_tarski(k3_xboole_0(X12,X13),u1_struct_0(sK0))) ) | ~spl3_32),
% 0.20/0.50    inference(avatar_component_clause,[],[f282])).
% 0.20/0.50  fof(f284,plain,(
% 0.20/0.50    spl3_32 | ~spl3_6),
% 0.20/0.50    inference(avatar_split_clause,[],[f239,f75,f282])).
% 0.20/0.50  fof(f75,plain,(
% 0.20/0.50    spl3_6 <=> r1_tarski(sK1,u1_struct_0(sK0))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.50  fof(f239,plain,(
% 0.20/0.50    ( ! [X12,X13] : (~r1_tarski(X12,sK1) | r1_tarski(k3_xboole_0(X12,X13),u1_struct_0(sK0))) ) | ~spl3_6),
% 0.20/0.50    inference(resolution,[],[f113,f77])).
% 0.20/0.50  fof(f77,plain,(
% 0.20/0.50    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl3_6),
% 0.20/0.50    inference(avatar_component_clause,[],[f75])).
% 0.20/0.50  fof(f113,plain,(
% 0.20/0.50    ( ! [X2,X0,X3,X1] : (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1) | r1_tarski(k3_xboole_0(X0,X3),X2)) )),
% 0.20/0.50    inference(resolution,[],[f89,f44])).
% 0.20/0.50  fof(f44,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X2) | r1_tarski(X0,X2)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f19])).
% 0.20/0.50  fof(f19,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.20/0.50    inference(flattening,[],[f18])).
% 0.20/0.50  fof(f18,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.20/0.50    inference(ennf_transformation,[],[f3])).
% 0.20/0.50  fof(f3,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.20/0.50  fof(f89,plain,(
% 0.20/0.50    ( ! [X4,X2,X3] : (r1_tarski(k3_xboole_0(X2,X4),X3) | ~r1_tarski(X2,X3)) )),
% 0.20/0.50    inference(resolution,[],[f44,f37])).
% 0.20/0.50  fof(f37,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f2])).
% 0.20/0.50  fof(f2,axiom,(
% 0.20/0.50    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.20/0.50  fof(f280,plain,(
% 0.20/0.50    spl3_31 | ~spl3_4 | ~spl3_22 | ~spl3_23),
% 0.20/0.50    inference(avatar_split_clause,[],[f210,f192,f186,f63,f278])).
% 0.20/0.50  fof(f63,plain,(
% 0.20/0.50    spl3_4 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.50  fof(f186,plain,(
% 0.20/0.50    spl3_22 <=> ! [X1,X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X1,X0)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X0))))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.20/0.50  fof(f192,plain,(
% 0.20/0.50    spl3_23 <=> sK1 = k2_pre_topc(sK0,sK1)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.20/0.50  fof(f210,plain,(
% 0.20/0.50    ( ! [X0] : (r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,X0)),k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl3_4 | ~spl3_22 | ~spl3_23)),
% 0.20/0.50    inference(forward_demodulation,[],[f207,f194])).
% 0.20/0.50  fof(f194,plain,(
% 0.20/0.50    sK1 = k2_pre_topc(sK0,sK1) | ~spl3_23),
% 0.20/0.50    inference(avatar_component_clause,[],[f192])).
% 0.20/0.50  fof(f207,plain,(
% 0.20/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,X0)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,X0)))) ) | (~spl3_4 | ~spl3_22)),
% 0.20/0.50    inference(resolution,[],[f187,f65])).
% 0.20/0.50  fof(f65,plain,(
% 0.20/0.50    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_4),
% 0.20/0.50    inference(avatar_component_clause,[],[f63])).
% 0.20/0.50  fof(f187,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X1,X0)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X0)))) ) | ~spl3_22),
% 0.20/0.50    inference(avatar_component_clause,[],[f186])).
% 0.20/0.50  fof(f222,plain,(
% 0.20/0.50    spl3_27 | ~spl3_18),
% 0.20/0.50    inference(avatar_split_clause,[],[f154,f149,f220])).
% 0.20/0.50  fof(f149,plain,(
% 0.20/0.50    spl3_18 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(X0,k2_pre_topc(sK0,X0)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.20/0.50  fof(f154,plain,(
% 0.20/0.50    ( ! [X0] : (r1_tarski(X0,k2_pre_topc(sK0,X0)) | ~r1_tarski(X0,u1_struct_0(sK0))) ) | ~spl3_18),
% 0.20/0.50    inference(resolution,[],[f150,f42])).
% 0.20/0.50  fof(f42,plain,(
% 0.20/0.50    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f26])).
% 0.20/0.50  fof(f26,plain,(
% 0.20/0.50    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.20/0.50    inference(nnf_transformation,[],[f5])).
% 0.20/0.50  fof(f5,axiom,(
% 0.20/0.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.50  fof(f150,plain,(
% 0.20/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(X0,k2_pre_topc(sK0,X0))) ) | ~spl3_18),
% 0.20/0.50    inference(avatar_component_clause,[],[f149])).
% 0.20/0.50  fof(f217,plain,(
% 0.20/0.50    ~spl3_26 | ~spl3_16 | spl3_24 | ~spl3_25),
% 0.20/0.50    inference(avatar_split_clause,[],[f212,f203,f197,f140,f214])).
% 0.20/0.50  fof(f197,plain,(
% 0.20/0.50    spl3_24 <=> k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,sK2))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.20/0.50  fof(f212,plain,(
% 0.20/0.50    k3_xboole_0(sK1,sK2) != k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)) | (~spl3_16 | spl3_24 | ~spl3_25)),
% 0.20/0.50    inference(forward_demodulation,[],[f211,f141])).
% 0.20/0.50  fof(f211,plain,(
% 0.20/0.50    k9_subset_1(u1_struct_0(sK0),sK1,sK2) != k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)) | (spl3_24 | ~spl3_25)),
% 0.20/0.50    inference(backward_demodulation,[],[f199,f205])).
% 0.20/0.50  fof(f199,plain,(
% 0.20/0.50    k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,sK2)) | spl3_24),
% 0.20/0.50    inference(avatar_component_clause,[],[f197])).
% 0.20/0.50  fof(f206,plain,(
% 0.20/0.50    spl3_25 | ~spl3_3 | ~spl3_5 | ~spl3_21),
% 0.20/0.50    inference(avatar_split_clause,[],[f181,f172,f68,f58,f203])).
% 0.20/0.50  fof(f58,plain,(
% 0.20/0.50    spl3_3 <=> v4_pre_topc(sK2,sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.50  fof(f172,plain,(
% 0.20/0.50    spl3_21 <=> ! [X0] : (~v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = X0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.20/0.50  fof(f181,plain,(
% 0.20/0.50    sK2 = k2_pre_topc(sK0,sK2) | (~spl3_3 | ~spl3_5 | ~spl3_21)),
% 0.20/0.50    inference(subsumption_resolution,[],[f179,f70])).
% 0.20/0.50  fof(f179,plain,(
% 0.20/0.50    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | sK2 = k2_pre_topc(sK0,sK2) | (~spl3_3 | ~spl3_21)),
% 0.20/0.50    inference(resolution,[],[f173,f60])).
% 0.20/0.50  fof(f60,plain,(
% 0.20/0.50    v4_pre_topc(sK2,sK0) | ~spl3_3),
% 0.20/0.50    inference(avatar_component_clause,[],[f58])).
% 0.20/0.50  fof(f173,plain,(
% 0.20/0.50    ( ! [X0] : (~v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = X0) ) | ~spl3_21),
% 0.20/0.50    inference(avatar_component_clause,[],[f172])).
% 0.20/0.50  fof(f200,plain,(
% 0.20/0.50    ~spl3_24 | ~spl3_2 | ~spl3_4 | spl3_17 | ~spl3_21),
% 0.20/0.50    inference(avatar_split_clause,[],[f190,f172,f144,f63,f53,f197])).
% 0.20/0.50  fof(f53,plain,(
% 0.20/0.50    spl3_2 <=> v4_pre_topc(sK1,sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.50  fof(f144,plain,(
% 0.20/0.50    spl3_17 <=> k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)) = k2_pre_topc(sK0,k3_xboole_0(sK1,sK2))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.20/0.50  fof(f190,plain,(
% 0.20/0.50    k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,sK2)) | (~spl3_2 | ~spl3_4 | spl3_17 | ~spl3_21)),
% 0.20/0.50    inference(backward_demodulation,[],[f146,f180])).
% 0.20/0.50  fof(f180,plain,(
% 0.20/0.50    sK1 = k2_pre_topc(sK0,sK1) | (~spl3_2 | ~spl3_4 | ~spl3_21)),
% 0.20/0.50    inference(subsumption_resolution,[],[f178,f65])).
% 0.20/0.50  fof(f178,plain,(
% 0.20/0.50    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | sK1 = k2_pre_topc(sK0,sK1) | (~spl3_2 | ~spl3_21)),
% 0.20/0.50    inference(resolution,[],[f173,f55])).
% 0.20/0.50  fof(f55,plain,(
% 0.20/0.50    v4_pre_topc(sK1,sK0) | ~spl3_2),
% 0.20/0.50    inference(avatar_component_clause,[],[f53])).
% 0.20/0.50  fof(f146,plain,(
% 0.20/0.50    k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)) != k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)) | spl3_17),
% 0.20/0.50    inference(avatar_component_clause,[],[f144])).
% 0.20/0.50  fof(f195,plain,(
% 0.20/0.50    spl3_23 | ~spl3_2 | ~spl3_4 | ~spl3_21),
% 0.20/0.50    inference(avatar_split_clause,[],[f180,f172,f63,f53,f192])).
% 0.20/0.50  fof(f188,plain,(
% 0.20/0.50    spl3_22 | ~spl3_1),
% 0.20/0.50    inference(avatar_split_clause,[],[f124,f48,f186])).
% 0.20/0.50  fof(f48,plain,(
% 0.20/0.50    spl3_1 <=> l1_pre_topc(sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.50  fof(f124,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X1,X0)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X0)))) ) | ~spl3_1),
% 0.20/0.50    inference(resolution,[],[f36,f50])).
% 0.20/0.50  fof(f50,plain,(
% 0.20/0.50    l1_pre_topc(sK0) | ~spl3_1),
% 0.20/0.50    inference(avatar_component_clause,[],[f48])).
% 0.20/0.50  fof(f36,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f16])).
% 0.20/0.50  fof(f16,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f7])).
% 0.20/0.50  fof(f7,axiom,(
% 0.20/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_pre_topc)).
% 0.20/0.50  fof(f174,plain,(
% 0.20/0.50    spl3_21 | ~spl3_1),
% 0.20/0.50    inference(avatar_split_clause,[],[f105,f48,f172])).
% 0.20/0.50  fof(f105,plain,(
% 0.20/0.50    ( ! [X0] : (~v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = X0) ) | ~spl3_1),
% 0.20/0.50    inference(resolution,[],[f34,f50])).
% 0.20/0.50  fof(f34,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = X1) )),
% 0.20/0.50    inference(cnf_transformation,[],[f15])).
% 0.20/0.50  fof(f15,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.50    inference(flattening,[],[f14])).
% 0.20/0.50  fof(f14,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f8])).
% 0.20/0.50  fof(f8,axiom,(
% 0.20/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).
% 0.20/0.50  fof(f151,plain,(
% 0.20/0.50    spl3_18 | ~spl3_1),
% 0.20/0.50    inference(avatar_split_clause,[],[f93,f48,f149])).
% 0.20/0.50  fof(f93,plain,(
% 0.20/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(X0,k2_pre_topc(sK0,X0))) ) | ~spl3_1),
% 0.20/0.50    inference(resolution,[],[f33,f50])).
% 0.20/0.50  fof(f33,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(X1,k2_pre_topc(X0,X1))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f13])).
% 0.20/0.50  fof(f13,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f6])).
% 0.20/0.50  fof(f6,axiom,(
% 0.20/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(X1,k2_pre_topc(X0,X1))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).
% 0.20/0.50  fof(f147,plain,(
% 0.20/0.50    ~spl3_17 | ~spl3_5 | spl3_10),
% 0.20/0.50    inference(avatar_split_clause,[],[f138,f108,f68,f144])).
% 0.20/0.50  fof(f108,plain,(
% 0.20/0.50    spl3_10 <=> k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.20/0.50  fof(f138,plain,(
% 0.20/0.50    k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)) != k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)) | (~spl3_5 | spl3_10)),
% 0.20/0.50    inference(backward_demodulation,[],[f110,f99])).
% 0.20/0.50  fof(f99,plain,(
% 0.20/0.50    ( ! [X1] : (k9_subset_1(u1_struct_0(sK0),X1,sK2) = k3_xboole_0(X1,sK2)) ) | ~spl3_5),
% 0.20/0.50    inference(resolution,[],[f43,f70])).
% 0.20/0.50  fof(f43,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f17])).
% 0.20/0.50  fof(f17,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f4])).
% 0.20/0.50  fof(f4,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.20/0.50  fof(f110,plain,(
% 0.20/0.50    k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)) != k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)) | spl3_10),
% 0.20/0.50    inference(avatar_component_clause,[],[f108])).
% 0.20/0.50  fof(f142,plain,(
% 0.20/0.50    spl3_16 | ~spl3_5),
% 0.20/0.50    inference(avatar_split_clause,[],[f99,f68,f140])).
% 0.20/0.50  fof(f111,plain,(
% 0.20/0.50    ~spl3_10),
% 0.20/0.50    inference(avatar_split_clause,[],[f32,f108])).
% 0.20/0.50  fof(f32,plain,(
% 0.20/0.50    k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)) != k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))),
% 0.20/0.50    inference(cnf_transformation,[],[f23])).
% 0.20/0.50  fof(f23,plain,(
% 0.20/0.50    ((k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)) != k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)) & v4_pre_topc(sK2,sK0) & v4_pre_topc(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f22,f21,f20])).
% 0.20/0.50  fof(f20,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : (? [X2] : (k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) != k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) & v4_pre_topc(X2,X0) & v4_pre_topc(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X1,X2)) != k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X2)) & v4_pre_topc(X2,sK0) & v4_pre_topc(X1,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f21,plain,(
% 0.20/0.50    ? [X1] : (? [X2] : (k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X1,X2)) != k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X2)) & v4_pre_topc(X2,sK0) & v4_pre_topc(X1,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,X2)) != k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,X2)) & v4_pre_topc(X2,sK0) & v4_pre_topc(sK1,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f22,plain,(
% 0.20/0.50    ? [X2] : (k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,X2)) != k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,X2)) & v4_pre_topc(X2,sK0) & v4_pre_topc(sK1,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)) != k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)) & v4_pre_topc(sK2,sK0) & v4_pre_topc(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f12,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : (? [X2] : (k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) != k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) & v4_pre_topc(X2,X0) & v4_pre_topc(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.20/0.50    inference(flattening,[],[f11])).
% 0.20/0.50  fof(f11,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : (? [X2] : ((k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) != k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) & (v4_pre_topc(X2,X0) & v4_pre_topc(X1,X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f10])).
% 0.20/0.50  fof(f10,negated_conjecture,(
% 0.20/0.50    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X2,X0) & v4_pre_topc(X1,X0)) => k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))))))),
% 0.20/0.50    inference(negated_conjecture,[],[f9])).
% 0.20/0.50  fof(f9,conjecture,(
% 0.20/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X2,X0) & v4_pre_topc(X1,X0)) => k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_tops_1)).
% 0.20/0.50  fof(f78,plain,(
% 0.20/0.50    spl3_6 | ~spl3_4),
% 0.20/0.50    inference(avatar_split_clause,[],[f72,f63,f75])).
% 0.20/0.50  fof(f72,plain,(
% 0.20/0.50    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl3_4),
% 0.20/0.50    inference(resolution,[],[f41,f65])).
% 0.20/0.50  fof(f41,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f26])).
% 0.20/0.50  fof(f71,plain,(
% 0.20/0.50    spl3_5),
% 0.20/0.50    inference(avatar_split_clause,[],[f29,f68])).
% 0.20/0.50  fof(f29,plain,(
% 0.20/0.50    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.50    inference(cnf_transformation,[],[f23])).
% 0.20/0.50  fof(f66,plain,(
% 0.20/0.50    spl3_4),
% 0.20/0.50    inference(avatar_split_clause,[],[f28,f63])).
% 0.20/0.50  fof(f28,plain,(
% 0.20/0.50    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.50    inference(cnf_transformation,[],[f23])).
% 0.20/0.50  fof(f61,plain,(
% 0.20/0.50    spl3_3),
% 0.20/0.50    inference(avatar_split_clause,[],[f31,f58])).
% 0.20/0.50  fof(f31,plain,(
% 0.20/0.50    v4_pre_topc(sK2,sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f23])).
% 0.20/0.50  fof(f56,plain,(
% 0.20/0.50    spl3_2),
% 0.20/0.50    inference(avatar_split_clause,[],[f30,f53])).
% 0.20/0.50  fof(f30,plain,(
% 0.20/0.50    v4_pre_topc(sK1,sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f23])).
% 0.20/0.50  fof(f51,plain,(
% 0.20/0.50    spl3_1),
% 0.20/0.50    inference(avatar_split_clause,[],[f27,f48])).
% 0.20/0.50  fof(f27,plain,(
% 0.20/0.50    l1_pre_topc(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f23])).
% 0.20/0.50  % SZS output end Proof for theBenchmark
% 0.20/0.50  % (3702)------------------------------
% 0.20/0.50  % (3702)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (3702)Termination reason: Refutation
% 0.20/0.50  
% 0.20/0.50  % (3702)Memory used [KB]: 6524
% 0.20/0.50  % (3702)Time elapsed: 0.087 s
% 0.20/0.50  % (3702)------------------------------
% 0.20/0.50  % (3702)------------------------------
% 0.20/0.50  % (3703)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.50  % (3725)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.20/0.50  % (3697)Success in time 0.143 s
%------------------------------------------------------------------------------
