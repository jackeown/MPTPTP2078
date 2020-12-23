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
% DateTime   : Thu Dec  3 13:13:43 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 187 expanded)
%              Number of leaves         :   34 (  94 expanded)
%              Depth                    :    6
%              Number of atoms          :  325 ( 577 expanded)
%              Number of equality atoms :    4 (   6 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f166,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f36,f41,f46,f51,f55,f59,f63,f67,f71,f75,f79,f83,f88,f102,f109,f115,f120,f129,f135,f141,f146,f153,f160,f165])).

fof(f165,plain,
    ( spl3_1
    | ~ spl3_15
    | ~ spl3_24 ),
    inference(avatar_contradiction_clause,[],[f164])).

fof(f164,plain,
    ( $false
    | spl3_1
    | ~ spl3_15
    | ~ spl3_24 ),
    inference(subsumption_resolution,[],[f161,f101])).

fof(f101,plain,
    ( r1_tarski(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl3_15
  <=> r1_tarski(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f161,plain,
    ( ~ r1_tarski(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | spl3_1
    | ~ spl3_24 ),
    inference(resolution,[],[f159,f35])).

fof(f35,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f33])).

fof(f33,plain,
    ( spl3_1
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f159,plain,
    ( ! [X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ r1_tarski(X1,k1_zfmisc_1(u1_struct_0(sK1))) )
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f158])).

fof(f158,plain,
    ( spl3_24
  <=> ! [X1] :
        ( ~ r1_tarski(X1,k1_zfmisc_1(u1_struct_0(sK1)))
        | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f160,plain,
    ( spl3_24
    | ~ spl3_20
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f156,f151,f132,f158])).

fof(f132,plain,
    ( spl3_20
  <=> r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f151,plain,
    ( spl3_23
  <=> ! [X1,X0] :
        ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ r1_tarski(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f156,plain,
    ( ! [X1] :
        ( ~ r1_tarski(X1,k1_zfmisc_1(u1_struct_0(sK1)))
        | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
    | ~ spl3_20
    | ~ spl3_23 ),
    inference(resolution,[],[f152,f134])).

fof(f134,plain,
    ( r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f132])).

fof(f152,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X1,u1_struct_0(sK0))
        | ~ r1_tarski(X0,k1_zfmisc_1(X1))
        | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f151])).

fof(f153,plain,
    ( spl3_23
    | ~ spl3_16
    | ~ spl3_22 ),
    inference(avatar_split_clause,[],[f147,f144,f107,f151])).

fof(f107,plain,
    ( spl3_16
  <=> ! [X1,X0] :
        ( ~ r1_tarski(X0,X1)
        | m1_subset_1(k1_zfmisc_1(X0),k1_zfmisc_1(k1_zfmisc_1(X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f144,plain,
    ( spl3_22
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ r1_tarski(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f147,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ r1_tarski(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X1,u1_struct_0(sK0)) )
    | ~ spl3_16
    | ~ spl3_22 ),
    inference(resolution,[],[f145,f108])).

fof(f108,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k1_zfmisc_1(X0),k1_zfmisc_1(k1_zfmisc_1(X1)))
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f107])).

fof(f145,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ r1_tarski(X1,X0) )
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f144])).

fof(f146,plain,
    ( spl3_22
    | ~ spl3_4
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f142,f139,f48,f144])).

fof(f48,plain,
    ( spl3_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f139,plain,
    ( spl3_21
  <=> ! [X1,X0,X2] :
        ( ~ r1_tarski(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
        | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
        | ~ l1_pre_topc(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f142,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ r1_tarski(X1,X0) )
    | ~ spl3_4
    | ~ spl3_21 ),
    inference(resolution,[],[f140,f50])).

fof(f50,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f48])).

fof(f140,plain,
    ( ! [X2,X0,X1] :
        ( ~ l1_pre_topc(X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
        | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f139])).

fof(f141,plain,
    ( spl3_21
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f137,f65,f61,f139])).

fof(f61,plain,
    ( spl3_7
  <=> ! [X1,X0,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ r1_tarski(X2,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ l1_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f65,plain,
    ( spl3_8
  <=> ! [X0] :
        ( l1_struct_0(X0)
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f137,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
        | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
        | ~ l1_pre_topc(X2) )
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(resolution,[],[f62,f66])).

fof(f66,plain,
    ( ! [X0] :
        ( l1_struct_0(X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f65])).

fof(f62,plain,
    ( ! [X2,X0,X1] :
        ( ~ l1_struct_0(X0)
        | ~ r1_tarski(X2,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f61])).

fof(f135,plain,
    ( spl3_20
    | ~ spl3_12
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f130,f125,f81,f132])).

fof(f81,plain,
    ( spl3_12
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f125,plain,
    ( spl3_19
  <=> m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f130,plain,
    ( r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ spl3_12
    | ~ spl3_19 ),
    inference(resolution,[],[f127,f82])).

fof(f82,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | r1_tarski(X0,X1) )
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f81])).

fof(f127,plain,
    ( m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f125])).

fof(f129,plain,
    ( spl3_19
    | ~ spl3_13
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f122,f118,f86,f125])).

fof(f86,plain,
    ( spl3_13
  <=> ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f118,plain,
    ( spl3_18
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f122,plain,
    ( m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_13
    | ~ spl3_18 ),
    inference(resolution,[],[f119,f87])).

fof(f87,plain,
    ( ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0))
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f86])).

fof(f119,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f118])).

fof(f120,plain,
    ( spl3_18
    | ~ spl3_3
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f116,f113,f43,f118])).

fof(f43,plain,
    ( spl3_3
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f113,plain,
    ( spl3_17
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ m1_pre_topc(X1,sK0)
        | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f116,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl3_3
    | ~ spl3_17 ),
    inference(resolution,[],[f114,f45])).

fof(f45,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f43])).

fof(f114,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(X1,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
        | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f113])).

fof(f115,plain,
    ( spl3_17
    | ~ spl3_4
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f111,f69,f48,f113])).

fof(f69,plain,
    ( spl3_9
  <=> ! [X1,X0,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ m1_pre_topc(X1,X0)
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f111,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ m1_pre_topc(X1,sK0)
        | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl3_4
    | ~ spl3_9 ),
    inference(resolution,[],[f70,f50])).

fof(f70,plain,
    ( ! [X2,X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ m1_pre_topc(X1,X0)
        | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f69])).

fof(f109,plain,
    ( spl3_16
    | ~ spl3_10
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f105,f77,f73,f107])).

fof(f73,plain,
    ( spl3_10
  <=> ! [X1,X0] :
        ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f77,plain,
    ( spl3_11
  <=> ! [X1,X0] :
        ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f105,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | m1_subset_1(k1_zfmisc_1(X0),k1_zfmisc_1(k1_zfmisc_1(X1))) )
    | ~ spl3_10
    | ~ spl3_11 ),
    inference(resolution,[],[f74,f78])).

fof(f78,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | m1_subset_1(X0,k1_zfmisc_1(X1)) )
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f77])).

fof(f74,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f73])).

fof(f102,plain,
    ( spl3_15
    | ~ spl3_2
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f91,f81,f38,f99])).

fof(f38,plain,
    ( spl3_2
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f91,plain,
    ( r1_tarski(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl3_2
    | ~ spl3_12 ),
    inference(resolution,[],[f82,f40])).

fof(f40,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f38])).

fof(f88,plain,
    ( spl3_13
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f84,f57,f53,f86])).

fof(f53,plain,
    ( spl3_5
  <=> ! [X0] : k2_subset_1(X0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f57,plain,
    ( spl3_6
  <=> ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f84,plain,
    ( ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0))
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(superposition,[],[f58,f54])).

fof(f54,plain,
    ( ! [X0] : k2_subset_1(X0) = X0
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f53])).

fof(f58,plain,
    ( ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f57])).

fof(f83,plain,(
    spl3_12 ),
    inference(avatar_split_clause,[],[f30,f81])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f79,plain,(
    spl3_11 ),
    inference(avatar_split_clause,[],[f31,f77])).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f75,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f29,f73])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_zfmisc_1)).

fof(f71,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f28,f69])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_pre_topc)).

fof(f67,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f27,f65])).

fof(f27,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f63,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f26,f61])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ r1_tarski(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
              | ~ r1_tarski(X2,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( r1_tarski(X2,X1)
             => m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_tops_2)).

fof(f59,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f25,f57])).

fof(f25,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f55,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f24,f53])).

fof(f24,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f51,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f20,f48])).

fof(f20,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    & m1_pre_topc(sK1,sK0)
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f17,f16,f15])).

fof(f15,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
                & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
            & m1_pre_topc(X1,X0) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
          & m1_pre_topc(X1,sK0) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
        & m1_pre_topc(X1,sK0) )
   => ( ? [X2] :
          ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) )
      & m1_pre_topc(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) )
   => ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_pre_topc(X1,X0)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
               => m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
             => m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_tops_2)).

fof(f46,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f21,f43])).

fof(f21,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f41,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f22,f38])).

fof(f22,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f18])).

fof(f36,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f23,f33])).

fof(f23,plain,(
    ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:51:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.43  % (21390)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.21/0.43  % (21388)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.21/0.43  % (21389)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.21/0.43  % (21387)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.21/0.43  % (21388)Refutation found. Thanks to Tanya!
% 0.21/0.43  % SZS status Theorem for theBenchmark
% 0.21/0.43  % SZS output start Proof for theBenchmark
% 0.21/0.43  fof(f166,plain,(
% 0.21/0.43    $false),
% 0.21/0.43    inference(avatar_sat_refutation,[],[f36,f41,f46,f51,f55,f59,f63,f67,f71,f75,f79,f83,f88,f102,f109,f115,f120,f129,f135,f141,f146,f153,f160,f165])).
% 0.21/0.44  fof(f165,plain,(
% 0.21/0.44    spl3_1 | ~spl3_15 | ~spl3_24),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f164])).
% 0.21/0.44  fof(f164,plain,(
% 0.21/0.44    $false | (spl3_1 | ~spl3_15 | ~spl3_24)),
% 0.21/0.44    inference(subsumption_resolution,[],[f161,f101])).
% 0.21/0.44  fof(f101,plain,(
% 0.21/0.44    r1_tarski(sK2,k1_zfmisc_1(u1_struct_0(sK1))) | ~spl3_15),
% 0.21/0.44    inference(avatar_component_clause,[],[f99])).
% 0.21/0.44  fof(f99,plain,(
% 0.21/0.44    spl3_15 <=> r1_tarski(sK2,k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.21/0.44  fof(f161,plain,(
% 0.21/0.44    ~r1_tarski(sK2,k1_zfmisc_1(u1_struct_0(sK1))) | (spl3_1 | ~spl3_24)),
% 0.21/0.44    inference(resolution,[],[f159,f35])).
% 0.21/0.44  fof(f35,plain,(
% 0.21/0.44    ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | spl3_1),
% 0.21/0.44    inference(avatar_component_clause,[],[f33])).
% 0.21/0.44  fof(f33,plain,(
% 0.21/0.44    spl3_1 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.44  fof(f159,plain,(
% 0.21/0.44    ( ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~r1_tarski(X1,k1_zfmisc_1(u1_struct_0(sK1)))) ) | ~spl3_24),
% 0.21/0.44    inference(avatar_component_clause,[],[f158])).
% 0.21/0.44  fof(f158,plain,(
% 0.21/0.44    spl3_24 <=> ! [X1] : (~r1_tarski(X1,k1_zfmisc_1(u1_struct_0(sK1))) | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.21/0.44  fof(f160,plain,(
% 0.21/0.44    spl3_24 | ~spl3_20 | ~spl3_23),
% 0.21/0.44    inference(avatar_split_clause,[],[f156,f151,f132,f158])).
% 0.21/0.44  fof(f132,plain,(
% 0.21/0.44    spl3_20 <=> r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.21/0.44  fof(f151,plain,(
% 0.21/0.44    spl3_23 <=> ! [X1,X0] : (m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~r1_tarski(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X1,u1_struct_0(sK0)))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.21/0.44  fof(f156,plain,(
% 0.21/0.44    ( ! [X1] : (~r1_tarski(X1,k1_zfmisc_1(u1_struct_0(sK1))) | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) ) | (~spl3_20 | ~spl3_23)),
% 0.21/0.44    inference(resolution,[],[f152,f134])).
% 0.21/0.44  fof(f134,plain,(
% 0.21/0.44    r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0)) | ~spl3_20),
% 0.21/0.44    inference(avatar_component_clause,[],[f132])).
% 0.21/0.44  fof(f152,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~r1_tarski(X1,u1_struct_0(sK0)) | ~r1_tarski(X0,k1_zfmisc_1(X1)) | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) ) | ~spl3_23),
% 0.21/0.44    inference(avatar_component_clause,[],[f151])).
% 0.21/0.44  fof(f153,plain,(
% 0.21/0.44    spl3_23 | ~spl3_16 | ~spl3_22),
% 0.21/0.44    inference(avatar_split_clause,[],[f147,f144,f107,f151])).
% 0.21/0.44  fof(f107,plain,(
% 0.21/0.44    spl3_16 <=> ! [X1,X0] : (~r1_tarski(X0,X1) | m1_subset_1(k1_zfmisc_1(X0),k1_zfmisc_1(k1_zfmisc_1(X1))))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.21/0.44  fof(f144,plain,(
% 0.21/0.44    spl3_22 <=> ! [X1,X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~r1_tarski(X1,X0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.21/0.44  fof(f147,plain,(
% 0.21/0.44    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~r1_tarski(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X1,u1_struct_0(sK0))) ) | (~spl3_16 | ~spl3_22)),
% 0.21/0.44    inference(resolution,[],[f145,f108])).
% 0.21/0.44  fof(f108,plain,(
% 0.21/0.44    ( ! [X0,X1] : (m1_subset_1(k1_zfmisc_1(X0),k1_zfmisc_1(k1_zfmisc_1(X1))) | ~r1_tarski(X0,X1)) ) | ~spl3_16),
% 0.21/0.44    inference(avatar_component_clause,[],[f107])).
% 0.21/0.44  fof(f145,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~r1_tarski(X1,X0)) ) | ~spl3_22),
% 0.21/0.44    inference(avatar_component_clause,[],[f144])).
% 0.21/0.44  fof(f146,plain,(
% 0.21/0.44    spl3_22 | ~spl3_4 | ~spl3_21),
% 0.21/0.44    inference(avatar_split_clause,[],[f142,f139,f48,f144])).
% 0.21/0.44  fof(f48,plain,(
% 0.21/0.44    spl3_4 <=> l1_pre_topc(sK0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.44  fof(f139,plain,(
% 0.21/0.44    spl3_21 <=> ! [X1,X0,X2] : (~r1_tarski(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) | ~l1_pre_topc(X2))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.21/0.44  fof(f142,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~r1_tarski(X1,X0)) ) | (~spl3_4 | ~spl3_21)),
% 0.21/0.44    inference(resolution,[],[f140,f50])).
% 0.21/0.44  fof(f50,plain,(
% 0.21/0.44    l1_pre_topc(sK0) | ~spl3_4),
% 0.21/0.44    inference(avatar_component_clause,[],[f48])).
% 0.21/0.44  fof(f140,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~l1_pre_topc(X2) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) | ~r1_tarski(X0,X1)) ) | ~spl3_21),
% 0.21/0.44    inference(avatar_component_clause,[],[f139])).
% 0.21/0.44  fof(f141,plain,(
% 0.21/0.44    spl3_21 | ~spl3_7 | ~spl3_8),
% 0.21/0.44    inference(avatar_split_clause,[],[f137,f65,f61,f139])).
% 0.21/0.44  fof(f61,plain,(
% 0.21/0.44    spl3_7 <=> ! [X1,X0,X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_struct_0(X0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.44  fof(f65,plain,(
% 0.21/0.44    spl3_8 <=> ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.44  fof(f137,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) | ~l1_pre_topc(X2)) ) | (~spl3_7 | ~spl3_8)),
% 0.21/0.44    inference(resolution,[],[f62,f66])).
% 0.21/0.44  fof(f66,plain,(
% 0.21/0.44    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) ) | ~spl3_8),
% 0.21/0.44    inference(avatar_component_clause,[],[f65])).
% 0.21/0.44  fof(f62,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~l1_struct_0(X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) ) | ~spl3_7),
% 0.21/0.44    inference(avatar_component_clause,[],[f61])).
% 0.21/0.44  fof(f135,plain,(
% 0.21/0.44    spl3_20 | ~spl3_12 | ~spl3_19),
% 0.21/0.44    inference(avatar_split_clause,[],[f130,f125,f81,f132])).
% 0.21/0.44  fof(f81,plain,(
% 0.21/0.44    spl3_12 <=> ! [X1,X0] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.44  fof(f125,plain,(
% 0.21/0.44    spl3_19 <=> m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.21/0.44  fof(f130,plain,(
% 0.21/0.44    r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0)) | (~spl3_12 | ~spl3_19)),
% 0.21/0.44    inference(resolution,[],[f127,f82])).
% 0.21/0.44  fof(f82,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) ) | ~spl3_12),
% 0.21/0.44    inference(avatar_component_clause,[],[f81])).
% 0.21/0.44  fof(f127,plain,(
% 0.21/0.44    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_19),
% 0.21/0.44    inference(avatar_component_clause,[],[f125])).
% 0.21/0.44  fof(f129,plain,(
% 0.21/0.44    spl3_19 | ~spl3_13 | ~spl3_18),
% 0.21/0.44    inference(avatar_split_clause,[],[f122,f118,f86,f125])).
% 0.21/0.44  fof(f86,plain,(
% 0.21/0.44    spl3_13 <=> ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.21/0.44  fof(f118,plain,(
% 0.21/0.44    spl3_18 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.21/0.44  fof(f122,plain,(
% 0.21/0.44    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_13 | ~spl3_18)),
% 0.21/0.44    inference(resolution,[],[f119,f87])).
% 0.21/0.44  fof(f87,plain,(
% 0.21/0.44    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) ) | ~spl3_13),
% 0.21/0.44    inference(avatar_component_clause,[],[f86])).
% 0.21/0.44  fof(f119,plain,(
% 0.21/0.44    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl3_18),
% 0.21/0.44    inference(avatar_component_clause,[],[f118])).
% 0.21/0.44  fof(f120,plain,(
% 0.21/0.44    spl3_18 | ~spl3_3 | ~spl3_17),
% 0.21/0.44    inference(avatar_split_clause,[],[f116,f113,f43,f118])).
% 0.21/0.44  fof(f43,plain,(
% 0.21/0.44    spl3_3 <=> m1_pre_topc(sK1,sK0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.44  fof(f113,plain,(
% 0.21/0.44    spl3_17 <=> ! [X1,X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X1,sK0) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.21/0.44  fof(f116,plain,(
% 0.21/0.44    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl3_3 | ~spl3_17)),
% 0.21/0.44    inference(resolution,[],[f114,f45])).
% 0.21/0.44  fof(f45,plain,(
% 0.21/0.44    m1_pre_topc(sK1,sK0) | ~spl3_3),
% 0.21/0.44    inference(avatar_component_clause,[],[f43])).
% 0.21/0.44  fof(f114,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~m1_pre_topc(X1,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl3_17),
% 0.21/0.44    inference(avatar_component_clause,[],[f113])).
% 0.21/0.44  fof(f115,plain,(
% 0.21/0.44    spl3_17 | ~spl3_4 | ~spl3_9),
% 0.21/0.44    inference(avatar_split_clause,[],[f111,f69,f48,f113])).
% 0.21/0.44  fof(f69,plain,(
% 0.21/0.44    spl3_9 <=> ! [X1,X0,X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.44  fof(f111,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X1,sK0) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl3_4 | ~spl3_9)),
% 0.21/0.44    inference(resolution,[],[f70,f50])).
% 0.21/0.44  fof(f70,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) ) | ~spl3_9),
% 0.21/0.44    inference(avatar_component_clause,[],[f69])).
% 0.21/0.44  fof(f109,plain,(
% 0.21/0.44    spl3_16 | ~spl3_10 | ~spl3_11),
% 0.21/0.44    inference(avatar_split_clause,[],[f105,f77,f73,f107])).
% 0.21/0.44  fof(f73,plain,(
% 0.21/0.44    spl3_10 <=> ! [X1,X0] : (r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.44  fof(f77,plain,(
% 0.21/0.44    spl3_11 <=> ! [X1,X0] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.44  fof(f105,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(k1_zfmisc_1(X0),k1_zfmisc_1(k1_zfmisc_1(X1)))) ) | (~spl3_10 | ~spl3_11)),
% 0.21/0.44    inference(resolution,[],[f74,f78])).
% 0.21/0.44  fof(f78,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) ) | ~spl3_11),
% 0.21/0.44    inference(avatar_component_clause,[],[f77])).
% 0.21/0.44  fof(f74,plain,(
% 0.21/0.44    ( ! [X0,X1] : (r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) ) | ~spl3_10),
% 0.21/0.44    inference(avatar_component_clause,[],[f73])).
% 0.21/0.44  fof(f102,plain,(
% 0.21/0.44    spl3_15 | ~spl3_2 | ~spl3_12),
% 0.21/0.44    inference(avatar_split_clause,[],[f91,f81,f38,f99])).
% 0.21/0.44  fof(f38,plain,(
% 0.21/0.44    spl3_2 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.44  fof(f91,plain,(
% 0.21/0.44    r1_tarski(sK2,k1_zfmisc_1(u1_struct_0(sK1))) | (~spl3_2 | ~spl3_12)),
% 0.21/0.44    inference(resolution,[],[f82,f40])).
% 0.21/0.44  fof(f40,plain,(
% 0.21/0.44    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) | ~spl3_2),
% 0.21/0.44    inference(avatar_component_clause,[],[f38])).
% 0.21/0.44  fof(f88,plain,(
% 0.21/0.44    spl3_13 | ~spl3_5 | ~spl3_6),
% 0.21/0.44    inference(avatar_split_clause,[],[f84,f57,f53,f86])).
% 0.21/0.44  fof(f53,plain,(
% 0.21/0.44    spl3_5 <=> ! [X0] : k2_subset_1(X0) = X0),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.44  fof(f57,plain,(
% 0.21/0.44    spl3_6 <=> ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.44  fof(f84,plain,(
% 0.21/0.44    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) ) | (~spl3_5 | ~spl3_6)),
% 0.21/0.44    inference(superposition,[],[f58,f54])).
% 0.21/0.44  fof(f54,plain,(
% 0.21/0.44    ( ! [X0] : (k2_subset_1(X0) = X0) ) | ~spl3_5),
% 0.21/0.44    inference(avatar_component_clause,[],[f53])).
% 0.21/0.44  fof(f58,plain,(
% 0.21/0.44    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) ) | ~spl3_6),
% 0.21/0.44    inference(avatar_component_clause,[],[f57])).
% 0.21/0.44  fof(f83,plain,(
% 0.21/0.44    spl3_12),
% 0.21/0.44    inference(avatar_split_clause,[],[f30,f81])).
% 0.21/0.44  fof(f30,plain,(
% 0.21/0.44    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f19])).
% 0.21/0.44  fof(f19,plain,(
% 0.21/0.44    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.44    inference(nnf_transformation,[],[f4])).
% 0.21/0.44  fof(f4,axiom,(
% 0.21/0.44    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.44  fof(f79,plain,(
% 0.21/0.44    spl3_11),
% 0.21/0.44    inference(avatar_split_clause,[],[f31,f77])).
% 0.21/0.44  fof(f31,plain,(
% 0.21/0.44    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f19])).
% 0.21/0.44  fof(f75,plain,(
% 0.21/0.44    spl3_10),
% 0.21/0.44    inference(avatar_split_clause,[],[f29,f73])).
% 0.21/0.44  fof(f29,plain,(
% 0.21/0.44    ( ! [X0,X1] : (r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f14])).
% 0.21/0.44  fof(f14,plain,(
% 0.21/0.44    ! [X0,X1] : (r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 0.21/0.44    inference(ennf_transformation,[],[f1])).
% 0.21/0.44  fof(f1,axiom,(
% 0.21/0.44    ! [X0,X1] : (r1_tarski(X0,X1) => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_zfmisc_1)).
% 0.21/0.44  fof(f71,plain,(
% 0.21/0.44    spl3_9),
% 0.21/0.44    inference(avatar_split_clause,[],[f28,f69])).
% 0.21/0.44  fof(f28,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f13])).
% 0.21/0.44  fof(f13,plain,(
% 0.21/0.44    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.44    inference(ennf_transformation,[],[f6])).
% 0.21/0.44  fof(f6,axiom,(
% 0.21/0.44    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_pre_topc)).
% 0.21/0.44  fof(f67,plain,(
% 0.21/0.44    spl3_8),
% 0.21/0.44    inference(avatar_split_clause,[],[f27,f65])).
% 0.21/0.44  fof(f27,plain,(
% 0.21/0.44    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f12])).
% 0.21/0.44  fof(f12,plain,(
% 0.21/0.44    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.44    inference(ennf_transformation,[],[f5])).
% 0.21/0.44  fof(f5,axiom,(
% 0.21/0.44    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.44  fof(f63,plain,(
% 0.21/0.44    spl3_7),
% 0.21/0.44    inference(avatar_split_clause,[],[f26,f61])).
% 0.21/0.44  fof(f26,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_struct_0(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f11])).
% 0.21/0.44  fof(f11,plain,(
% 0.21/0.44    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_struct_0(X0))),
% 0.21/0.44    inference(ennf_transformation,[],[f7])).
% 0.21/0.44  fof(f7,axiom,(
% 0.21/0.44    ! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (r1_tarski(X2,X1) => m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_tops_2)).
% 0.21/0.44  fof(f59,plain,(
% 0.21/0.44    spl3_6),
% 0.21/0.44    inference(avatar_split_clause,[],[f25,f57])).
% 0.21/0.44  fof(f25,plain,(
% 0.21/0.44    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f3])).
% 0.21/0.44  fof(f3,axiom,(
% 0.21/0.44    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.21/0.44  fof(f55,plain,(
% 0.21/0.44    spl3_5),
% 0.21/0.44    inference(avatar_split_clause,[],[f24,f53])).
% 0.21/0.44  fof(f24,plain,(
% 0.21/0.44    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.21/0.44    inference(cnf_transformation,[],[f2])).
% 0.21/0.44  fof(f2,axiom,(
% 0.21/0.44    ! [X0] : k2_subset_1(X0) = X0),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 0.21/0.44  fof(f51,plain,(
% 0.21/0.44    spl3_4),
% 0.21/0.44    inference(avatar_split_clause,[],[f20,f48])).
% 0.21/0.44  fof(f20,plain,(
% 0.21/0.44    l1_pre_topc(sK0)),
% 0.21/0.44    inference(cnf_transformation,[],[f18])).
% 0.21/0.44  fof(f18,plain,(
% 0.21/0.44    ((~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))) & m1_pre_topc(sK1,sK0)) & l1_pre_topc(sK0)),
% 0.21/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f17,f16,f15])).
% 0.21/0.44  fof(f15,plain,(
% 0.21/0.44    ? [X0] : (? [X1] : (? [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))) & m1_pre_topc(X1,sK0)) & l1_pre_topc(sK0))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f16,plain,(
% 0.21/0.44    ? [X1] : (? [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))) & m1_pre_topc(X1,sK0)) => (? [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))) & m1_pre_topc(sK1,sK0))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f17,plain,(
% 0.21/0.44    ? [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))) => (~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f10,plain,(
% 0.21/0.44    ? [X0] : (? [X1] : (? [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0))),
% 0.21/0.44    inference(ennf_transformation,[],[f9])).
% 0.21/0.44  fof(f9,negated_conjecture,(
% 0.21/0.44    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) => m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))))),
% 0.21/0.44    inference(negated_conjecture,[],[f8])).
% 0.21/0.44  fof(f8,conjecture,(
% 0.21/0.44    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) => m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_tops_2)).
% 0.21/0.44  fof(f46,plain,(
% 0.21/0.44    spl3_3),
% 0.21/0.44    inference(avatar_split_clause,[],[f21,f43])).
% 0.21/0.44  fof(f21,plain,(
% 0.21/0.44    m1_pre_topc(sK1,sK0)),
% 0.21/0.44    inference(cnf_transformation,[],[f18])).
% 0.21/0.44  fof(f41,plain,(
% 0.21/0.44    spl3_2),
% 0.21/0.44    inference(avatar_split_clause,[],[f22,f38])).
% 0.21/0.44  fof(f22,plain,(
% 0.21/0.44    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))),
% 0.21/0.44    inference(cnf_transformation,[],[f18])).
% 0.21/0.44  fof(f36,plain,(
% 0.21/0.44    ~spl3_1),
% 0.21/0.44    inference(avatar_split_clause,[],[f23,f33])).
% 0.21/0.44  fof(f23,plain,(
% 0.21/0.44    ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.44    inference(cnf_transformation,[],[f18])).
% 0.21/0.44  % SZS output end Proof for theBenchmark
% 0.21/0.44  % (21388)------------------------------
% 0.21/0.44  % (21388)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.44  % (21388)Termination reason: Refutation
% 0.21/0.44  
% 0.21/0.44  % (21388)Memory used [KB]: 10618
% 0.21/0.44  % (21388)Time elapsed: 0.008 s
% 0.21/0.44  % (21388)------------------------------
% 0.21/0.44  % (21388)------------------------------
% 0.21/0.44  % (21382)Success in time 0.079 s
%------------------------------------------------------------------------------
