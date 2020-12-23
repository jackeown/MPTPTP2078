%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:42 EST 2020

% Result     : Theorem 1.15s
% Output     : Refutation 1.15s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 145 expanded)
%              Number of leaves         :   27 (  68 expanded)
%              Depth                    :    5
%              Number of atoms          :  248 ( 397 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f189,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f36,f40,f44,f48,f56,f60,f64,f72,f76,f83,f96,f100,f107,f112,f116,f131,f148,f166,f179,f187])).

fof(f187,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | ~ spl4_6
    | ~ spl4_16
    | spl4_29 ),
    inference(avatar_contradiction_clause,[],[f184])).

fof(f184,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_6
    | ~ spl4_16
    | spl4_29 ),
    inference(unit_resulting_resolution,[],[f35,f39,f55,f178,f99])).

fof(f99,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_pre_topc(X1,X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ l1_pre_topc(X0) )
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl4_16
  <=> ! [X1,X0,X2] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(X1,X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
        | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f178,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_29 ),
    inference(avatar_component_clause,[],[f177])).

fof(f177,plain,
    ( spl4_29
  <=> m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).

fof(f55,plain,
    ( ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl4_6
  <=> ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f39,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f38])).

fof(f38,plain,
    ( spl4_2
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f35,plain,
    ( l1_pre_topc(sK0)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f34])).

fof(f34,plain,
    ( spl4_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f179,plain,
    ( ~ spl4_29
    | ~ spl4_8
    | spl4_27 ),
    inference(avatar_split_clause,[],[f170,f164,f62,f177])).

fof(f62,plain,
    ( spl4_8
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f164,plain,
    ( spl4_27
  <=> r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f170,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_8
    | spl4_27 ),
    inference(resolution,[],[f165,f63])).

fof(f63,plain,
    ( ! [X0,X1] :
        ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) )
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f62])).

fof(f165,plain,
    ( ~ r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0))
    | spl4_27 ),
    inference(avatar_component_clause,[],[f164])).

fof(f166,plain,
    ( ~ spl4_27
    | ~ spl4_3
    | ~ spl4_24 ),
    inference(avatar_split_clause,[],[f153,f146,f42,f164])).

fof(f42,plain,
    ( spl4_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f146,plain,
    ( spl4_24
  <=> ! [X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(X1)))
        | ~ r1_tarski(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f153,plain,
    ( ~ r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ spl4_3
    | ~ spl4_24 ),
    inference(resolution,[],[f147,f43])).

fof(f43,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f42])).

fof(f147,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(X1)))
        | ~ r1_tarski(X1,u1_struct_0(sK0)) )
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f146])).

fof(f148,plain,
    ( spl4_24
    | ~ spl4_11
    | ~ spl4_22 ),
    inference(avatar_split_clause,[],[f136,f129,f74,f146])).

fof(f74,plain,
    ( spl4_11
  <=> ! [X1,X0] :
        ( ~ r1_tarski(X0,X1)
        | r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f129,plain,
    ( spl4_22
  <=> ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
        | ~ r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f136,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(X1)))
        | ~ r1_tarski(X1,u1_struct_0(sK0)) )
    | ~ spl4_11
    | ~ spl4_22 ),
    inference(resolution,[],[f130,f75])).

fof(f75,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f74])).

fof(f130,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(X0)) )
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f129])).

fof(f131,plain,
    ( spl4_22
    | ~ spl4_18
    | ~ spl4_19 ),
    inference(avatar_split_clause,[],[f121,f114,f110,f129])).

fof(f110,plain,
    ( spl4_18
  <=> ! [X1,X0] :
        ( ~ r1_tarski(X0,X1)
        | m1_subset_1(k1_zfmisc_1(X0),k1_zfmisc_1(k1_zfmisc_1(X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f114,plain,
    ( spl4_19
  <=> ! [X0] :
        ( ~ m1_subset_1(k1_zfmisc_1(X0),k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f121,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
        | ~ r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl4_18
    | ~ spl4_19 ),
    inference(resolution,[],[f115,f111])).

fof(f111,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k1_zfmisc_1(X0),k1_zfmisc_1(k1_zfmisc_1(X1)))
        | ~ r1_tarski(X0,X1) )
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f110])).

fof(f115,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k1_zfmisc_1(X0),k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(X0)) )
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f114])).

fof(f116,plain,
    ( spl4_19
    | ~ spl4_8
    | ~ spl4_17 ),
    inference(avatar_split_clause,[],[f108,f105,f62,f114])).

fof(f105,plain,
    ( spl4_17
  <=> ! [X0] :
        ( ~ m1_subset_1(k1_zfmisc_1(X0),k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))
        | ~ r1_tarski(sK2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f108,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k1_zfmisc_1(X0),k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(X0)) )
    | ~ spl4_8
    | ~ spl4_17 ),
    inference(resolution,[],[f106,f63])).

fof(f106,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK2,X0)
        | ~ m1_subset_1(k1_zfmisc_1(X0),k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) )
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f105])).

fof(f112,plain,
    ( spl4_18
    | ~ spl4_7
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f79,f74,f58,f110])).

fof(f58,plain,
    ( spl4_7
  <=> ! [X1,X0] :
        ( ~ r1_tarski(X0,X1)
        | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f79,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | m1_subset_1(k1_zfmisc_1(X0),k1_zfmisc_1(k1_zfmisc_1(X1))) )
    | ~ spl4_7
    | ~ spl4_11 ),
    inference(resolution,[],[f75,f59])).

fof(f59,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | m1_subset_1(X0,k1_zfmisc_1(X1)) )
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f58])).

fof(f107,plain,
    ( spl4_17
    | ~ spl4_10
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f101,f94,f70,f105])).

fof(f70,plain,
    ( spl4_10
  <=> ! [X0,X2] :
        ( ~ r1_tarski(X2,X0)
        | r2_hidden(X2,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f94,plain,
    ( spl4_15
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))
        | ~ r2_hidden(sK2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f101,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k1_zfmisc_1(X0),k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))
        | ~ r1_tarski(sK2,X0) )
    | ~ spl4_10
    | ~ spl4_15 ),
    inference(resolution,[],[f95,f71])).

fof(f71,plain,
    ( ! [X2,X0] :
        ( r2_hidden(X2,k1_zfmisc_1(X0))
        | ~ r1_tarski(X2,X0) )
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f70])).

fof(f95,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK2,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) )
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f94])).

fof(f100,plain,(
    spl4_16 ),
    inference(avatar_split_clause,[],[f21,f98])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_pre_topc)).

fof(f96,plain,
    ( spl4_15
    | spl4_4
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f84,f81,f46,f94])).

fof(f46,plain,
    ( spl4_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f81,plain,
    ( spl4_12
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
        | m1_subset_1(X0,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f84,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))
        | ~ r2_hidden(sK2,X0) )
    | spl4_4
    | ~ spl4_12 ),
    inference(resolution,[],[f82,f47])).

fof(f47,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | spl4_4 ),
    inference(avatar_component_clause,[],[f46])).

fof(f82,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(X0,X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
        | ~ r2_hidden(X0,X1) )
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f81])).

fof(f83,plain,(
    spl4_12 ),
    inference(avatar_split_clause,[],[f29,f81])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f76,plain,(
    spl4_11 ),
    inference(avatar_split_clause,[],[f22,f74])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_zfmisc_1)).

fof(f72,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f31,f70])).

fof(f31,plain,(
    ! [X2,X0] :
      ( ~ r1_tarski(X2,X0)
      | r2_hidden(X2,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f23])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X0)
      | r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f64,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f28,f62])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f60,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f27,f58])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f56,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f32,f54])).

fof(f32,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f20,f19])).

fof(f19,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f20,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f48,plain,(
    ~ spl4_4 ),
    inference(avatar_split_clause,[],[f16,f46])).

fof(f16,plain,(
    ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f10])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_tops_2)).

fof(f44,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f15,f42])).

fof(f15,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f10])).

fof(f40,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f17,f38])).

fof(f17,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f36,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f18,f34])).

fof(f18,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:43:44 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.36  ipcrm: permission denied for id (721518592)
% 0.21/0.37  ipcrm: permission denied for id (721616898)
% 0.21/0.37  ipcrm: permission denied for id (721649667)
% 0.21/0.37  ipcrm: permission denied for id (721682436)
% 0.21/0.37  ipcrm: permission denied for id (721715205)
% 0.21/0.37  ipcrm: permission denied for id (721747974)
% 0.21/0.37  ipcrm: permission denied for id (721780743)
% 0.21/0.37  ipcrm: permission denied for id (721813512)
% 0.21/0.37  ipcrm: permission denied for id (721846281)
% 0.21/0.38  ipcrm: permission denied for id (721879050)
% 0.21/0.38  ipcrm: permission denied for id (721911819)
% 0.21/0.38  ipcrm: permission denied for id (721944588)
% 0.21/0.38  ipcrm: permission denied for id (722010126)
% 0.21/0.38  ipcrm: permission denied for id (722042895)
% 0.21/0.39  ipcrm: permission denied for id (722141202)
% 0.21/0.39  ipcrm: permission denied for id (722206740)
% 0.21/0.39  ipcrm: permission denied for id (722272278)
% 0.21/0.39  ipcrm: permission denied for id (722337816)
% 0.21/0.41  ipcrm: permission denied for id (722698275)
% 0.21/0.41  ipcrm: permission denied for id (722763813)
% 0.21/0.41  ipcrm: permission denied for id (722829351)
% 0.21/0.41  ipcrm: permission denied for id (722894889)
% 0.21/0.42  ipcrm: permission denied for id (722960427)
% 0.21/0.42  ipcrm: permission denied for id (723025965)
% 0.21/0.42  ipcrm: permission denied for id (723091503)
% 0.21/0.42  ipcrm: permission denied for id (723157041)
% 0.21/0.43  ipcrm: permission denied for id (723222579)
% 0.21/0.43  ipcrm: permission denied for id (723255348)
% 0.21/0.43  ipcrm: permission denied for id (723451962)
% 0.21/0.44  ipcrm: permission denied for id (723583038)
% 0.21/0.44  ipcrm: permission denied for id (723615807)
% 0.21/0.44  ipcrm: permission denied for id (723648576)
% 0.21/0.44  ipcrm: permission denied for id (723681345)
% 0.21/0.45  ipcrm: permission denied for id (723746883)
% 0.21/0.45  ipcrm: permission denied for id (723812421)
% 0.21/0.45  ipcrm: permission denied for id (723845190)
% 0.21/0.45  ipcrm: permission denied for id (723877959)
% 0.21/0.45  ipcrm: permission denied for id (723910728)
% 0.21/0.45  ipcrm: permission denied for id (723943497)
% 0.21/0.45  ipcrm: permission denied for id (723976266)
% 0.21/0.46  ipcrm: permission denied for id (724009035)
% 0.21/0.46  ipcrm: permission denied for id (724041804)
% 0.21/0.46  ipcrm: permission denied for id (724074573)
% 0.21/0.46  ipcrm: permission denied for id (724107342)
% 0.21/0.46  ipcrm: permission denied for id (724140111)
% 0.21/0.47  ipcrm: permission denied for id (724303956)
% 0.21/0.47  ipcrm: permission denied for id (724336725)
% 0.21/0.47  ipcrm: permission denied for id (724369494)
% 0.21/0.47  ipcrm: permission denied for id (724402263)
% 0.21/0.47  ipcrm: permission denied for id (724500570)
% 0.21/0.48  ipcrm: permission denied for id (724566108)
% 0.21/0.48  ipcrm: permission denied for id (724598877)
% 0.21/0.48  ipcrm: permission denied for id (724631646)
% 0.21/0.49  ipcrm: permission denied for id (724959336)
% 0.21/0.49  ipcrm: permission denied for id (724992105)
% 0.21/0.50  ipcrm: permission denied for id (725123181)
% 0.21/0.50  ipcrm: permission denied for id (725188719)
% 0.21/0.50  ipcrm: permission denied for id (725221488)
% 0.21/0.50  ipcrm: permission denied for id (725287026)
% 0.21/0.51  ipcrm: permission denied for id (725352564)
% 0.21/0.51  ipcrm: permission denied for id (725418102)
% 0.21/0.51  ipcrm: permission denied for id (725450871)
% 0.21/0.51  ipcrm: permission denied for id (725483640)
% 0.21/0.51  ipcrm: permission denied for id (725549178)
% 0.21/0.52  ipcrm: permission denied for id (721551485)
% 1.15/0.65  % (27865)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 1.15/0.65  % (27871)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 1.15/0.66  % (27865)Refutation found. Thanks to Tanya!
% 1.15/0.66  % SZS status Theorem for theBenchmark
% 1.15/0.66  % SZS output start Proof for theBenchmark
% 1.15/0.66  fof(f189,plain,(
% 1.15/0.66    $false),
% 1.15/0.66    inference(avatar_sat_refutation,[],[f36,f40,f44,f48,f56,f60,f64,f72,f76,f83,f96,f100,f107,f112,f116,f131,f148,f166,f179,f187])).
% 1.15/0.66  fof(f187,plain,(
% 1.15/0.66    ~spl4_1 | ~spl4_2 | ~spl4_6 | ~spl4_16 | spl4_29),
% 1.15/0.66    inference(avatar_contradiction_clause,[],[f184])).
% 1.15/0.66  fof(f184,plain,(
% 1.15/0.66    $false | (~spl4_1 | ~spl4_2 | ~spl4_6 | ~spl4_16 | spl4_29)),
% 1.15/0.66    inference(unit_resulting_resolution,[],[f35,f39,f55,f178,f99])).
% 1.15/0.66  fof(f99,plain,(
% 1.15/0.66    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X0)) ) | ~spl4_16),
% 1.15/0.66    inference(avatar_component_clause,[],[f98])).
% 1.15/0.66  fof(f98,plain,(
% 1.15/0.66    spl4_16 <=> ! [X1,X0,X2] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))),
% 1.15/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 1.15/0.66  fof(f178,plain,(
% 1.15/0.66    ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl4_29),
% 1.15/0.66    inference(avatar_component_clause,[],[f177])).
% 1.15/0.66  fof(f177,plain,(
% 1.15/0.66    spl4_29 <=> m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.15/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).
% 1.15/0.66  fof(f55,plain,(
% 1.15/0.66    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) ) | ~spl4_6),
% 1.15/0.66    inference(avatar_component_clause,[],[f54])).
% 1.15/0.66  fof(f54,plain,(
% 1.15/0.66    spl4_6 <=> ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0))),
% 1.15/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.15/0.66  fof(f39,plain,(
% 1.15/0.66    m1_pre_topc(sK1,sK0) | ~spl4_2),
% 1.15/0.66    inference(avatar_component_clause,[],[f38])).
% 1.15/0.66  fof(f38,plain,(
% 1.15/0.66    spl4_2 <=> m1_pre_topc(sK1,sK0)),
% 1.15/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.15/0.66  fof(f35,plain,(
% 1.15/0.66    l1_pre_topc(sK0) | ~spl4_1),
% 1.15/0.66    inference(avatar_component_clause,[],[f34])).
% 1.15/0.66  fof(f34,plain,(
% 1.15/0.66    spl4_1 <=> l1_pre_topc(sK0)),
% 1.15/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.15/0.66  fof(f179,plain,(
% 1.15/0.66    ~spl4_29 | ~spl4_8 | spl4_27),
% 1.15/0.66    inference(avatar_split_clause,[],[f170,f164,f62,f177])).
% 1.15/0.66  fof(f62,plain,(
% 1.15/0.66    spl4_8 <=> ! [X1,X0] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 1.15/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 1.15/0.66  fof(f164,plain,(
% 1.15/0.66    spl4_27 <=> r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0))),
% 1.15/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).
% 1.15/0.66  fof(f170,plain,(
% 1.15/0.66    ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl4_8 | spl4_27)),
% 1.15/0.66    inference(resolution,[],[f165,f63])).
% 1.15/0.66  fof(f63,plain,(
% 1.15/0.66    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) ) | ~spl4_8),
% 1.15/0.66    inference(avatar_component_clause,[],[f62])).
% 1.15/0.66  fof(f165,plain,(
% 1.15/0.66    ~r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0)) | spl4_27),
% 1.15/0.66    inference(avatar_component_clause,[],[f164])).
% 1.15/0.66  fof(f166,plain,(
% 1.15/0.66    ~spl4_27 | ~spl4_3 | ~spl4_24),
% 1.15/0.66    inference(avatar_split_clause,[],[f153,f146,f42,f164])).
% 1.15/0.66  fof(f42,plain,(
% 1.15/0.66    spl4_3 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))),
% 1.15/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.15/0.66  fof(f146,plain,(
% 1.15/0.66    spl4_24 <=> ! [X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(X1))) | ~r1_tarski(X1,u1_struct_0(sK0)))),
% 1.15/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 1.15/0.66  fof(f153,plain,(
% 1.15/0.66    ~r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0)) | (~spl4_3 | ~spl4_24)),
% 1.15/0.66    inference(resolution,[],[f147,f43])).
% 1.15/0.66  fof(f43,plain,(
% 1.15/0.66    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) | ~spl4_3),
% 1.15/0.66    inference(avatar_component_clause,[],[f42])).
% 1.15/0.66  fof(f147,plain,(
% 1.15/0.66    ( ! [X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(X1))) | ~r1_tarski(X1,u1_struct_0(sK0))) ) | ~spl4_24),
% 1.15/0.66    inference(avatar_component_clause,[],[f146])).
% 1.15/0.66  fof(f148,plain,(
% 1.15/0.66    spl4_24 | ~spl4_11 | ~spl4_22),
% 1.15/0.66    inference(avatar_split_clause,[],[f136,f129,f74,f146])).
% 1.15/0.66  fof(f74,plain,(
% 1.15/0.66    spl4_11 <=> ! [X1,X0] : (~r1_tarski(X0,X1) | r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)))),
% 1.15/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 1.15/0.66  fof(f129,plain,(
% 1.15/0.66    spl4_22 <=> ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(X0)) | ~r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.15/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 1.15/0.66  fof(f136,plain,(
% 1.15/0.66    ( ! [X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(X1))) | ~r1_tarski(X1,u1_struct_0(sK0))) ) | (~spl4_11 | ~spl4_22)),
% 1.15/0.66    inference(resolution,[],[f130,f75])).
% 1.15/0.66  fof(f75,plain,(
% 1.15/0.66    ( ! [X0,X1] : (r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) ) | ~spl4_11),
% 1.15/0.66    inference(avatar_component_clause,[],[f74])).
% 1.15/0.66  fof(f130,plain,(
% 1.15/0.66    ( ! [X0] : (~r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(X0))) ) | ~spl4_22),
% 1.15/0.66    inference(avatar_component_clause,[],[f129])).
% 1.15/0.66  fof(f131,plain,(
% 1.15/0.66    spl4_22 | ~spl4_18 | ~spl4_19),
% 1.15/0.66    inference(avatar_split_clause,[],[f121,f114,f110,f129])).
% 1.15/0.66  fof(f110,plain,(
% 1.15/0.66    spl4_18 <=> ! [X1,X0] : (~r1_tarski(X0,X1) | m1_subset_1(k1_zfmisc_1(X0),k1_zfmisc_1(k1_zfmisc_1(X1))))),
% 1.15/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 1.15/0.66  fof(f114,plain,(
% 1.15/0.66    spl4_19 <=> ! [X0] : (~m1_subset_1(k1_zfmisc_1(X0),k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) | ~m1_subset_1(sK2,k1_zfmisc_1(X0)))),
% 1.15/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 1.15/0.66  fof(f121,plain,(
% 1.15/0.66    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(X0)) | ~r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl4_18 | ~spl4_19)),
% 1.15/0.66    inference(resolution,[],[f115,f111])).
% 1.15/0.66  fof(f111,plain,(
% 1.15/0.66    ( ! [X0,X1] : (m1_subset_1(k1_zfmisc_1(X0),k1_zfmisc_1(k1_zfmisc_1(X1))) | ~r1_tarski(X0,X1)) ) | ~spl4_18),
% 1.15/0.66    inference(avatar_component_clause,[],[f110])).
% 1.15/0.66  fof(f115,plain,(
% 1.15/0.66    ( ! [X0] : (~m1_subset_1(k1_zfmisc_1(X0),k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) | ~m1_subset_1(sK2,k1_zfmisc_1(X0))) ) | ~spl4_19),
% 1.15/0.66    inference(avatar_component_clause,[],[f114])).
% 1.15/0.66  fof(f116,plain,(
% 1.15/0.66    spl4_19 | ~spl4_8 | ~spl4_17),
% 1.15/0.66    inference(avatar_split_clause,[],[f108,f105,f62,f114])).
% 1.15/0.66  fof(f105,plain,(
% 1.15/0.66    spl4_17 <=> ! [X0] : (~m1_subset_1(k1_zfmisc_1(X0),k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) | ~r1_tarski(sK2,X0))),
% 1.15/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 1.15/0.66  fof(f108,plain,(
% 1.15/0.66    ( ! [X0] : (~m1_subset_1(k1_zfmisc_1(X0),k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) | ~m1_subset_1(sK2,k1_zfmisc_1(X0))) ) | (~spl4_8 | ~spl4_17)),
% 1.15/0.66    inference(resolution,[],[f106,f63])).
% 1.15/0.66  fof(f106,plain,(
% 1.15/0.66    ( ! [X0] : (~r1_tarski(sK2,X0) | ~m1_subset_1(k1_zfmisc_1(X0),k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))) ) | ~spl4_17),
% 1.15/0.66    inference(avatar_component_clause,[],[f105])).
% 1.15/0.66  fof(f112,plain,(
% 1.15/0.66    spl4_18 | ~spl4_7 | ~spl4_11),
% 1.15/0.66    inference(avatar_split_clause,[],[f79,f74,f58,f110])).
% 1.15/0.66  fof(f58,plain,(
% 1.15/0.66    spl4_7 <=> ! [X1,X0] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 1.15/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 1.15/0.66  fof(f79,plain,(
% 1.15/0.66    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(k1_zfmisc_1(X0),k1_zfmisc_1(k1_zfmisc_1(X1)))) ) | (~spl4_7 | ~spl4_11)),
% 1.15/0.66    inference(resolution,[],[f75,f59])).
% 1.15/0.66  fof(f59,plain,(
% 1.15/0.66    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) ) | ~spl4_7),
% 1.15/0.66    inference(avatar_component_clause,[],[f58])).
% 1.15/0.66  fof(f107,plain,(
% 1.15/0.66    spl4_17 | ~spl4_10 | ~spl4_15),
% 1.15/0.66    inference(avatar_split_clause,[],[f101,f94,f70,f105])).
% 1.15/0.66  fof(f70,plain,(
% 1.15/0.66    spl4_10 <=> ! [X0,X2] : (~r1_tarski(X2,X0) | r2_hidden(X2,k1_zfmisc_1(X0)))),
% 1.15/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 1.15/0.66  fof(f94,plain,(
% 1.15/0.66    spl4_15 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) | ~r2_hidden(sK2,X0))),
% 1.15/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 1.15/0.66  fof(f101,plain,(
% 1.15/0.66    ( ! [X0] : (~m1_subset_1(k1_zfmisc_1(X0),k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) | ~r1_tarski(sK2,X0)) ) | (~spl4_10 | ~spl4_15)),
% 1.15/0.66    inference(resolution,[],[f95,f71])).
% 1.15/0.66  fof(f71,plain,(
% 1.15/0.66    ( ! [X2,X0] : (r2_hidden(X2,k1_zfmisc_1(X0)) | ~r1_tarski(X2,X0)) ) | ~spl4_10),
% 1.15/0.66    inference(avatar_component_clause,[],[f70])).
% 1.15/0.66  fof(f95,plain,(
% 1.15/0.66    ( ! [X0] : (~r2_hidden(sK2,X0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))) ) | ~spl4_15),
% 1.15/0.66    inference(avatar_component_clause,[],[f94])).
% 1.15/0.66  fof(f100,plain,(
% 1.15/0.66    spl4_16),
% 1.15/0.66    inference(avatar_split_clause,[],[f21,f98])).
% 1.15/0.66  fof(f21,plain,(
% 1.15/0.66    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) )),
% 1.15/0.66    inference(cnf_transformation,[],[f11])).
% 1.15/0.66  fof(f11,plain,(
% 1.15/0.66    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.15/0.66    inference(ennf_transformation,[],[f7])).
% 1.15/0.66  fof(f7,axiom,(
% 1.15/0.66    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))))),
% 1.15/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_pre_topc)).
% 1.15/0.66  fof(f96,plain,(
% 1.15/0.66    spl4_15 | spl4_4 | ~spl4_12),
% 1.15/0.66    inference(avatar_split_clause,[],[f84,f81,f46,f94])).
% 1.15/0.66  fof(f46,plain,(
% 1.15/0.66    spl4_4 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.15/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.15/0.66  fof(f81,plain,(
% 1.15/0.66    spl4_12 <=> ! [X1,X0,X2] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2))),
% 1.15/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 1.15/0.66  fof(f84,plain,(
% 1.15/0.66    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) | ~r2_hidden(sK2,X0)) ) | (spl4_4 | ~spl4_12)),
% 1.15/0.66    inference(resolution,[],[f82,f47])).
% 1.15/0.66  fof(f47,plain,(
% 1.15/0.66    ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | spl4_4),
% 1.15/0.66    inference(avatar_component_clause,[],[f46])).
% 1.15/0.66  fof(f82,plain,(
% 1.15/0.66    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) ) | ~spl4_12),
% 1.15/0.66    inference(avatar_component_clause,[],[f81])).
% 1.15/0.66  fof(f83,plain,(
% 1.15/0.66    spl4_12),
% 1.15/0.66    inference(avatar_split_clause,[],[f29,f81])).
% 1.15/0.66  fof(f29,plain,(
% 1.15/0.66    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2)) )),
% 1.15/0.66    inference(cnf_transformation,[],[f14])).
% 1.15/0.66  fof(f14,plain,(
% 1.15/0.66    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.15/0.66    inference(flattening,[],[f13])).
% 1.15/0.66  fof(f13,plain,(
% 1.15/0.66    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 1.15/0.66    inference(ennf_transformation,[],[f6])).
% 1.15/0.66  fof(f6,axiom,(
% 1.15/0.66    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 1.15/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 1.15/0.66  fof(f76,plain,(
% 1.15/0.66    spl4_11),
% 1.15/0.66    inference(avatar_split_clause,[],[f22,f74])).
% 1.15/0.66  fof(f22,plain,(
% 1.15/0.66    ( ! [X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))) )),
% 1.15/0.66    inference(cnf_transformation,[],[f12])).
% 1.15/0.66  fof(f12,plain,(
% 1.15/0.66    ! [X0,X1] : (r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 1.15/0.66    inference(ennf_transformation,[],[f2])).
% 1.15/0.66  fof(f2,axiom,(
% 1.15/0.66    ! [X0,X1] : (r1_tarski(X0,X1) => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)))),
% 1.15/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_zfmisc_1)).
% 1.15/0.66  fof(f72,plain,(
% 1.15/0.66    spl4_10),
% 1.15/0.66    inference(avatar_split_clause,[],[f31,f70])).
% 1.15/0.66  fof(f31,plain,(
% 1.15/0.66    ( ! [X2,X0] : (~r1_tarski(X2,X0) | r2_hidden(X2,k1_zfmisc_1(X0))) )),
% 1.15/0.66    inference(equality_resolution,[],[f23])).
% 1.15/0.66  fof(f23,plain,(
% 1.15/0.66    ( ! [X2,X0,X1] : (~r1_tarski(X2,X0) | r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.15/0.66    inference(cnf_transformation,[],[f1])).
% 1.15/0.66  fof(f1,axiom,(
% 1.15/0.66    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.15/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.15/0.66  fof(f64,plain,(
% 1.15/0.66    spl4_8),
% 1.15/0.66    inference(avatar_split_clause,[],[f28,f62])).
% 1.15/0.66  fof(f28,plain,(
% 1.15/0.66    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.15/0.66    inference(cnf_transformation,[],[f5])).
% 1.15/0.66  fof(f5,axiom,(
% 1.15/0.66    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.15/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.15/0.66  fof(f60,plain,(
% 1.15/0.66    spl4_7),
% 1.15/0.66    inference(avatar_split_clause,[],[f27,f58])).
% 1.15/0.66  fof(f27,plain,(
% 1.15/0.66    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.15/0.66    inference(cnf_transformation,[],[f5])).
% 1.15/0.66  fof(f56,plain,(
% 1.15/0.66    spl4_6),
% 1.15/0.66    inference(avatar_split_clause,[],[f32,f54])).
% 1.15/0.66  fof(f32,plain,(
% 1.15/0.66    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 1.15/0.66    inference(forward_demodulation,[],[f20,f19])).
% 1.15/0.66  fof(f19,plain,(
% 1.15/0.66    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.15/0.66    inference(cnf_transformation,[],[f3])).
% 1.15/0.66  fof(f3,axiom,(
% 1.15/0.66    ! [X0] : k2_subset_1(X0) = X0),
% 1.15/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 1.15/0.66  fof(f20,plain,(
% 1.15/0.66    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 1.15/0.66    inference(cnf_transformation,[],[f4])).
% 1.15/0.66  fof(f4,axiom,(
% 1.15/0.66    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 1.15/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 1.15/0.66  fof(f48,plain,(
% 1.15/0.66    ~spl4_4),
% 1.15/0.66    inference(avatar_split_clause,[],[f16,f46])).
% 1.15/0.66  fof(f16,plain,(
% 1.15/0.66    ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.15/0.66    inference(cnf_transformation,[],[f10])).
% 1.15/0.66  fof(f10,plain,(
% 1.15/0.66    ? [X0] : (? [X1] : (? [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0))),
% 1.15/0.66    inference(ennf_transformation,[],[f9])).
% 1.15/0.66  fof(f9,negated_conjecture,(
% 1.15/0.66    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) => m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))))),
% 1.15/0.66    inference(negated_conjecture,[],[f8])).
% 1.15/0.66  fof(f8,conjecture,(
% 1.15/0.66    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) => m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))))),
% 1.15/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_tops_2)).
% 1.15/0.66  fof(f44,plain,(
% 1.15/0.66    spl4_3),
% 1.15/0.66    inference(avatar_split_clause,[],[f15,f42])).
% 1.15/0.66  fof(f15,plain,(
% 1.15/0.66    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))),
% 1.15/0.66    inference(cnf_transformation,[],[f10])).
% 1.15/0.66  fof(f40,plain,(
% 1.15/0.66    spl4_2),
% 1.15/0.66    inference(avatar_split_clause,[],[f17,f38])).
% 1.15/0.66  fof(f17,plain,(
% 1.15/0.66    m1_pre_topc(sK1,sK0)),
% 1.15/0.66    inference(cnf_transformation,[],[f10])).
% 1.15/0.66  fof(f36,plain,(
% 1.15/0.66    spl4_1),
% 1.15/0.66    inference(avatar_split_clause,[],[f18,f34])).
% 1.15/0.66  fof(f18,plain,(
% 1.15/0.66    l1_pre_topc(sK0)),
% 1.15/0.66    inference(cnf_transformation,[],[f10])).
% 1.15/0.66  % SZS output end Proof for theBenchmark
% 1.15/0.66  % (27865)------------------------------
% 1.15/0.66  % (27865)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.15/0.66  % (27865)Termination reason: Refutation
% 1.15/0.66  
% 1.15/0.66  % (27865)Memory used [KB]: 10618
% 1.15/0.66  % (27865)Time elapsed: 0.080 s
% 1.15/0.66  % (27865)------------------------------
% 1.15/0.66  % (27865)------------------------------
% 1.31/0.67  % (27719)Success in time 0.307 s
%------------------------------------------------------------------------------
