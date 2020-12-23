%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:16 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 156 expanded)
%              Number of leaves         :   21 (  45 expanded)
%              Depth                    :   10
%              Number of atoms          :  283 ( 718 expanded)
%              Number of equality atoms :   12 (  50 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f206,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f104,f112,f116,f164,f167,f170,f181,f188,f193,f205])).

fof(f205,plain,(
    ~ spl6_2 ),
    inference(avatar_contradiction_clause,[],[f204])).

fof(f204,plain,
    ( $false
    | ~ spl6_2 ),
    inference(resolution,[],[f200,f39])).

fof(f39,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f200,plain,
    ( ~ r1_tarski(k1_xboole_0,u1_struct_0(sK0))
    | ~ spl6_2 ),
    inference(resolution,[],[f103,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f103,plain,
    ( r2_hidden(u1_struct_0(sK0),k1_xboole_0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl6_2
  <=> r2_hidden(u1_struct_0(sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f193,plain,(
    ~ spl6_13 ),
    inference(avatar_contradiction_clause,[],[f192])).

fof(f192,plain,
    ( $false
    | ~ spl6_13 ),
    inference(resolution,[],[f177,f36])).

fof(f36,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( r2_hidden(X3,X2)
                  <=> ( r2_hidden(X1,X3)
                      & v4_pre_topc(X3,X0)
                      & v3_pre_topc(X3,X0) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( r2_hidden(X3,X2)
                  <=> ( r2_hidden(X1,X3)
                      & v4_pre_topc(X3,X0)
                      & v3_pre_topc(X3,X0) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => ~ ( k1_xboole_0 = X2
                    & ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ( r2_hidden(X3,X2)
                        <=> ( r2_hidden(X1,X3)
                            & v4_pre_topc(X3,X0)
                            & v3_pre_topc(X3,X0) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ~ ( k1_xboole_0 = X2
                  & ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                     => ( r2_hidden(X3,X2)
                      <=> ( r2_hidden(X1,X3)
                          & v4_pre_topc(X3,X0)
                          & v3_pre_topc(X3,X0) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_connsp_2)).

fof(f177,plain,
    ( v2_struct_0(sK0)
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f176])).

fof(f176,plain,
    ( spl6_13
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f188,plain,(
    spl6_14 ),
    inference(avatar_contradiction_clause,[],[f187])).

fof(f187,plain,
    ( $false
    | spl6_14 ),
    inference(resolution,[],[f185,f38])).

fof(f38,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f185,plain,
    ( ~ l1_pre_topc(sK0)
    | spl6_14 ),
    inference(resolution,[],[f180,f43])).

fof(f43,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f180,plain,
    ( ~ l1_struct_0(sK0)
    | spl6_14 ),
    inference(avatar_component_clause,[],[f179])).

fof(f179,plain,
    ( spl6_14
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f181,plain,
    ( spl6_13
    | ~ spl6_14
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f174,f110,f179,f176])).

fof(f110,plain,
    ( spl6_7
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f174,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_7 ),
    inference(resolution,[],[f111,f64])).

fof(f64,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f111,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f110])).

fof(f170,plain,(
    spl6_12 ),
    inference(avatar_contradiction_clause,[],[f169])).

fof(f169,plain,
    ( $false
    | spl6_12 ),
    inference(resolution,[],[f163,f38])).

fof(f163,plain,
    ( ~ l1_pre_topc(sK0)
    | spl6_12 ),
    inference(avatar_component_clause,[],[f162])).

fof(f162,plain,
    ( spl6_12
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f167,plain,(
    spl6_11 ),
    inference(avatar_contradiction_clause,[],[f166])).

fof(f166,plain,
    ( $false
    | spl6_11 ),
    inference(resolution,[],[f160,f37])).

fof(f37,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f160,plain,
    ( ~ v2_pre_topc(sK0)
    | spl6_11 ),
    inference(avatar_component_clause,[],[f159])).

fof(f159,plain,
    ( spl6_11
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f164,plain,
    ( ~ spl6_11
    | ~ spl6_12
    | spl6_1 ),
    inference(avatar_split_clause,[],[f157,f75,f162,f159])).

fof(f75,plain,
    ( spl6_1
  <=> v3_pre_topc(u1_struct_0(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f157,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | spl6_1 ),
    inference(resolution,[],[f155,f102])).

fof(f102,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK0),sK0)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f75])).

fof(f155,plain,(
    ! [X0] :
      ( v3_pre_topc(u1_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f153])).

fof(f153,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | v3_pre_topc(u1_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(resolution,[],[f114,f61])).

fof(f61,plain,(
    ! [X0] :
      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

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
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
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
    inference(rectify,[],[f6])).

fof(f6,axiom,(
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

fof(f114,plain,(
    ! [X0] :
      ( ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | v3_pre_topc(u1_struct_0(X0),X0) ) ),
    inference(resolution,[],[f62,f69])).

fof(f69,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f41,f40])).

fof(f40,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f41,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).

fof(f116,plain,(
    spl6_6 ),
    inference(avatar_contradiction_clause,[],[f115])).

fof(f115,plain,
    ( $false
    | spl6_6 ),
    inference(resolution,[],[f108,f35])).

fof(f35,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f108,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | spl6_6 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl6_6
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f112,plain,
    ( ~ spl6_6
    | spl6_7
    | spl6_5 ),
    inference(avatar_split_clause,[],[f105,f100,f110,f107])).

fof(f100,plain,
    ( spl6_5
  <=> r2_hidden(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f105,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | spl6_5 ),
    inference(resolution,[],[f101,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f101,plain,
    ( ~ r2_hidden(sK1,u1_struct_0(sK0))
    | spl6_5 ),
    inference(avatar_component_clause,[],[f100])).

fof(f104,plain,
    ( ~ spl6_5
    | ~ spl6_1
    | spl6_2 ),
    inference(avatar_split_clause,[],[f98,f78,f75,f100])).

fof(f98,plain,
    ( r2_hidden(u1_struct_0(sK0),k1_xboole_0)
    | ~ v3_pre_topc(u1_struct_0(sK0),sK0)
    | ~ r2_hidden(sK1,u1_struct_0(sK0)) ),
    inference(global_subsumption,[],[f86,f97])).

fof(f97,plain,
    ( r2_hidden(u1_struct_0(sK0),k1_xboole_0)
    | ~ v3_pre_topc(u1_struct_0(sK0),sK0)
    | ~ v4_pre_topc(u1_struct_0(sK0),sK0)
    | ~ r2_hidden(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[],[f96,f69])).

fof(f96,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X3,k1_xboole_0)
      | ~ v3_pre_topc(X3,sK0)
      | ~ v4_pre_topc(X3,sK0)
      | ~ r2_hidden(sK1,X3) ) ),
    inference(forward_demodulation,[],[f32,f34])).

fof(f34,plain,(
    k1_xboole_0 = sK2 ),
    inference(cnf_transformation,[],[f16])).

fof(f32,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X3,sK0)
      | ~ v4_pre_topc(X3,sK0)
      | ~ r2_hidden(sK1,X3)
      | r2_hidden(X3,sK2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f86,plain,(
    v4_pre_topc(u1_struct_0(sK0),sK0) ),
    inference(global_subsumption,[],[f37,f38,f85])).

fof(f85,plain,
    ( v4_pre_topc(u1_struct_0(sK0),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(superposition,[],[f65,f84])).

fof(f84,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(resolution,[],[f83,f38])).

fof(f83,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | u1_struct_0(X0) = k2_struct_0(X0) ) ),
    inference(resolution,[],[f42,f43])).

fof(f42,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | u1_struct_0(X0) = k2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f65,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_pre_topc)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:53:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.23/0.50  % (22831)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.23/0.51  % (22822)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.23/0.51  % (22819)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.23/0.51  % (22834)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.23/0.51  % (22824)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.23/0.51  % (22838)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.23/0.51  % (22821)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.23/0.52  % (22822)Refutation not found, incomplete strategy% (22822)------------------------------
% 0.23/0.52  % (22822)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.52  % (22823)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.23/0.52  % (22826)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.23/0.52  % (22825)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.23/0.52  % (22830)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.23/0.52  % (22822)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.52  
% 0.23/0.52  % (22822)Memory used [KB]: 10618
% 0.23/0.52  % (22822)Time elapsed: 0.092 s
% 0.23/0.52  % (22822)------------------------------
% 0.23/0.52  % (22822)------------------------------
% 0.23/0.52  % (22831)Refutation found. Thanks to Tanya!
% 0.23/0.52  % SZS status Theorem for theBenchmark
% 0.23/0.52  % (22826)Refutation not found, incomplete strategy% (22826)------------------------------
% 0.23/0.52  % (22826)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.52  % (22826)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.52  % (22827)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.23/0.52  
% 0.23/0.52  % (22826)Memory used [KB]: 6140
% 0.23/0.52  % (22826)Time elapsed: 0.052 s
% 0.23/0.52  % (22826)------------------------------
% 0.23/0.52  % (22826)------------------------------
% 0.23/0.52  % (22827)Refutation not found, incomplete strategy% (22827)------------------------------
% 0.23/0.52  % (22827)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.52  % (22827)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.52  
% 0.23/0.52  % (22827)Memory used [KB]: 10618
% 0.23/0.52  % (22827)Time elapsed: 0.106 s
% 0.23/0.52  % (22827)------------------------------
% 0.23/0.52  % (22827)------------------------------
% 0.23/0.52  % (22835)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.23/0.52  % (22835)Refutation not found, incomplete strategy% (22835)------------------------------
% 0.23/0.52  % (22835)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.52  % (22835)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.52  
% 0.23/0.52  % (22835)Memory used [KB]: 1663
% 0.23/0.52  % (22835)Time elapsed: 0.106 s
% 0.23/0.52  % (22835)------------------------------
% 0.23/0.52  % (22835)------------------------------
% 0.23/0.53  % (22832)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.23/0.53  % (22842)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.23/0.53  % (22830)Refutation not found, incomplete strategy% (22830)------------------------------
% 0.23/0.53  % (22830)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.53  % (22830)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.53  
% 0.23/0.53  % (22830)Memory used [KB]: 1663
% 0.23/0.53  % (22830)Time elapsed: 0.108 s
% 0.23/0.53  % (22830)------------------------------
% 0.23/0.53  % (22830)------------------------------
% 0.23/0.53  % (22836)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.23/0.53  % (22839)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.23/0.53  % (22829)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.23/0.53  % (22836)Refutation not found, incomplete strategy% (22836)------------------------------
% 0.23/0.53  % (22836)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.53  % (22836)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.53  
% 0.23/0.53  % (22836)Memory used [KB]: 1663
% 0.23/0.53  % (22836)Time elapsed: 0.107 s
% 0.23/0.53  % (22836)------------------------------
% 0.23/0.53  % (22836)------------------------------
% 0.23/0.53  % (22841)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.23/0.53  % (22842)Refutation not found, incomplete strategy% (22842)------------------------------
% 0.23/0.53  % (22842)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.53  % (22842)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.53  
% 0.23/0.53  % (22842)Memory used [KB]: 10618
% 0.23/0.53  % (22842)Time elapsed: 0.109 s
% 0.23/0.53  % (22842)------------------------------
% 0.23/0.53  % (22842)------------------------------
% 0.23/0.53  % (22829)Refutation not found, incomplete strategy% (22829)------------------------------
% 0.23/0.53  % (22829)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.53  % (22829)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.53  
% 0.23/0.53  % (22829)Memory used [KB]: 10618
% 0.23/0.53  % (22829)Time elapsed: 0.105 s
% 0.23/0.53  % (22829)------------------------------
% 0.23/0.53  % (22829)------------------------------
% 0.23/0.53  % (22839)Refutation not found, incomplete strategy% (22839)------------------------------
% 0.23/0.53  % (22839)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.53  % (22839)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.53  
% 0.23/0.53  % (22839)Memory used [KB]: 6140
% 0.23/0.53  % (22839)Time elapsed: 0.109 s
% 0.23/0.53  % (22839)------------------------------
% 0.23/0.53  % (22839)------------------------------
% 0.23/0.53  % (22837)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.23/0.53  % (22840)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.23/0.53  % SZS output start Proof for theBenchmark
% 0.23/0.53  fof(f206,plain,(
% 0.23/0.53    $false),
% 0.23/0.53    inference(avatar_sat_refutation,[],[f104,f112,f116,f164,f167,f170,f181,f188,f193,f205])).
% 0.23/0.53  fof(f205,plain,(
% 0.23/0.53    ~spl6_2),
% 0.23/0.53    inference(avatar_contradiction_clause,[],[f204])).
% 0.23/0.53  fof(f204,plain,(
% 0.23/0.53    $false | ~spl6_2),
% 0.23/0.53    inference(resolution,[],[f200,f39])).
% 0.23/0.53  fof(f39,plain,(
% 0.23/0.53    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.23/0.53    inference(cnf_transformation,[],[f1])).
% 0.23/0.53  fof(f1,axiom,(
% 0.23/0.53    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.23/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.23/0.53  fof(f200,plain,(
% 0.23/0.53    ~r1_tarski(k1_xboole_0,u1_struct_0(sK0)) | ~spl6_2),
% 0.23/0.53    inference(resolution,[],[f103,f67])).
% 0.23/0.53  fof(f67,plain,(
% 0.23/0.53    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.23/0.53    inference(cnf_transformation,[],[f28])).
% 0.23/0.53  fof(f28,plain,(
% 0.23/0.53    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.23/0.53    inference(ennf_transformation,[],[f5])).
% 0.23/0.53  fof(f5,axiom,(
% 0.23/0.53    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.23/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.23/0.53  fof(f103,plain,(
% 0.23/0.53    r2_hidden(u1_struct_0(sK0),k1_xboole_0) | ~spl6_2),
% 0.23/0.53    inference(avatar_component_clause,[],[f78])).
% 0.23/0.53  fof(f78,plain,(
% 0.23/0.53    spl6_2 <=> r2_hidden(u1_struct_0(sK0),k1_xboole_0)),
% 0.23/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.23/0.53  fof(f193,plain,(
% 0.23/0.53    ~spl6_13),
% 0.23/0.53    inference(avatar_contradiction_clause,[],[f192])).
% 0.23/0.53  fof(f192,plain,(
% 0.23/0.53    $false | ~spl6_13),
% 0.23/0.53    inference(resolution,[],[f177,f36])).
% 0.23/0.53  fof(f36,plain,(
% 0.23/0.53    ~v2_struct_0(sK0)),
% 0.23/0.53    inference(cnf_transformation,[],[f16])).
% 0.23/0.53  fof(f16,plain,(
% 0.23/0.53    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : ((r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.23/0.53    inference(flattening,[],[f15])).
% 0.23/0.53  fof(f15,plain,(
% 0.23/0.53    ? [X0] : (? [X1] : (? [X2] : ((k1_xboole_0 = X2 & ! [X3] : ((r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.23/0.53    inference(ennf_transformation,[],[f13])).
% 0.23/0.53  fof(f13,negated_conjecture,(
% 0.23/0.53    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(k1_xboole_0 = X2 & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))))))))),
% 0.23/0.53    inference(negated_conjecture,[],[f12])).
% 0.23/0.53  fof(f12,conjecture,(
% 0.23/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(k1_xboole_0 = X2 & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))))))))),
% 0.23/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_connsp_2)).
% 0.23/0.53  fof(f177,plain,(
% 0.23/0.53    v2_struct_0(sK0) | ~spl6_13),
% 0.23/0.53    inference(avatar_component_clause,[],[f176])).
% 0.23/0.53  fof(f176,plain,(
% 0.23/0.53    spl6_13 <=> v2_struct_0(sK0)),
% 0.23/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 0.23/0.53  fof(f188,plain,(
% 0.23/0.53    spl6_14),
% 0.23/0.53    inference(avatar_contradiction_clause,[],[f187])).
% 0.23/0.53  fof(f187,plain,(
% 0.23/0.53    $false | spl6_14),
% 0.23/0.53    inference(resolution,[],[f185,f38])).
% 0.23/0.53  fof(f38,plain,(
% 0.23/0.53    l1_pre_topc(sK0)),
% 0.23/0.53    inference(cnf_transformation,[],[f16])).
% 0.23/0.53  fof(f185,plain,(
% 0.23/0.53    ~l1_pre_topc(sK0) | spl6_14),
% 0.23/0.53    inference(resolution,[],[f180,f43])).
% 0.23/0.53  fof(f43,plain,(
% 0.23/0.53    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.23/0.53    inference(cnf_transformation,[],[f18])).
% 0.23/0.53  fof(f18,plain,(
% 0.23/0.53    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.23/0.53    inference(ennf_transformation,[],[f9])).
% 0.23/0.53  fof(f9,axiom,(
% 0.23/0.53    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.23/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.23/0.53  fof(f180,plain,(
% 0.23/0.53    ~l1_struct_0(sK0) | spl6_14),
% 0.23/0.53    inference(avatar_component_clause,[],[f179])).
% 0.23/0.53  fof(f179,plain,(
% 0.23/0.53    spl6_14 <=> l1_struct_0(sK0)),
% 0.23/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 0.23/0.53  fof(f181,plain,(
% 0.23/0.53    spl6_13 | ~spl6_14 | ~spl6_7),
% 0.23/0.53    inference(avatar_split_clause,[],[f174,f110,f179,f176])).
% 0.23/0.53  fof(f110,plain,(
% 0.23/0.53    spl6_7 <=> v1_xboole_0(u1_struct_0(sK0))),
% 0.23/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.23/0.53  fof(f174,plain,(
% 0.23/0.53    ~l1_struct_0(sK0) | v2_struct_0(sK0) | ~spl6_7),
% 0.23/0.53    inference(resolution,[],[f111,f64])).
% 0.23/0.53  fof(f64,plain,(
% 0.23/0.53    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.23/0.53    inference(cnf_transformation,[],[f23])).
% 0.23/0.53  fof(f23,plain,(
% 0.23/0.53    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.23/0.53    inference(flattening,[],[f22])).
% 0.23/0.53  fof(f22,plain,(
% 0.23/0.53    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.23/0.53    inference(ennf_transformation,[],[f10])).
% 0.23/0.53  fof(f10,axiom,(
% 0.23/0.53    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.23/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.23/0.53  fof(f111,plain,(
% 0.23/0.53    v1_xboole_0(u1_struct_0(sK0)) | ~spl6_7),
% 0.23/0.53    inference(avatar_component_clause,[],[f110])).
% 0.23/0.53  fof(f170,plain,(
% 0.23/0.53    spl6_12),
% 0.23/0.53    inference(avatar_contradiction_clause,[],[f169])).
% 0.23/0.53  fof(f169,plain,(
% 0.23/0.53    $false | spl6_12),
% 0.23/0.53    inference(resolution,[],[f163,f38])).
% 0.23/0.53  fof(f163,plain,(
% 0.23/0.53    ~l1_pre_topc(sK0) | spl6_12),
% 0.23/0.53    inference(avatar_component_clause,[],[f162])).
% 0.23/0.53  fof(f162,plain,(
% 0.23/0.53    spl6_12 <=> l1_pre_topc(sK0)),
% 0.23/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.23/0.53  fof(f167,plain,(
% 0.23/0.53    spl6_11),
% 0.23/0.53    inference(avatar_contradiction_clause,[],[f166])).
% 0.23/0.53  fof(f166,plain,(
% 0.23/0.53    $false | spl6_11),
% 0.23/0.53    inference(resolution,[],[f160,f37])).
% 0.23/0.53  fof(f37,plain,(
% 0.23/0.53    v2_pre_topc(sK0)),
% 0.23/0.53    inference(cnf_transformation,[],[f16])).
% 0.23/0.53  fof(f160,plain,(
% 0.23/0.53    ~v2_pre_topc(sK0) | spl6_11),
% 0.23/0.53    inference(avatar_component_clause,[],[f159])).
% 0.23/0.53  fof(f159,plain,(
% 0.23/0.53    spl6_11 <=> v2_pre_topc(sK0)),
% 0.23/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.23/0.53  fof(f164,plain,(
% 0.23/0.53    ~spl6_11 | ~spl6_12 | spl6_1),
% 0.23/0.53    inference(avatar_split_clause,[],[f157,f75,f162,f159])).
% 0.23/0.53  fof(f75,plain,(
% 0.23/0.53    spl6_1 <=> v3_pre_topc(u1_struct_0(sK0),sK0)),
% 0.23/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.23/0.53  fof(f157,plain,(
% 0.23/0.53    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | spl6_1),
% 0.23/0.53    inference(resolution,[],[f155,f102])).
% 0.23/0.53  fof(f102,plain,(
% 0.23/0.53    ~v3_pre_topc(u1_struct_0(sK0),sK0) | spl6_1),
% 0.23/0.53    inference(avatar_component_clause,[],[f75])).
% 0.23/0.53  fof(f155,plain,(
% 0.23/0.53    ( ! [X0] : (v3_pre_topc(u1_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.23/0.53    inference(duplicate_literal_removal,[],[f153])).
% 0.23/0.53  fof(f153,plain,(
% 0.23/0.53    ( ! [X0] : (~l1_pre_topc(X0) | v3_pre_topc(u1_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.23/0.53    inference(resolution,[],[f114,f61])).
% 0.23/0.53  fof(f61,plain,(
% 0.23/0.53    ( ! [X0] : (r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.23/0.53    inference(cnf_transformation,[],[f20])).
% 0.23/0.53  fof(f20,plain,(
% 0.23/0.53    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 0.23/0.53    inference(flattening,[],[f19])).
% 0.23/0.53  fof(f19,plain,(
% 0.23/0.53    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : ((r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | (~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : ((r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 0.23/0.53    inference(ennf_transformation,[],[f14])).
% 0.23/0.53  fof(f14,plain,(
% 0.23/0.53    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X3,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 0.23/0.53    inference(rectify,[],[f6])).
% 0.23/0.53  fof(f6,axiom,(
% 0.23/0.53    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X1,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 0.23/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_pre_topc)).
% 0.23/0.53  fof(f114,plain,(
% 0.23/0.53    ( ! [X0] : (~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) | ~l1_pre_topc(X0) | v3_pre_topc(u1_struct_0(X0),X0)) )),
% 0.23/0.53    inference(resolution,[],[f62,f69])).
% 0.23/0.53  fof(f69,plain,(
% 0.23/0.53    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.23/0.53    inference(forward_demodulation,[],[f41,f40])).
% 0.23/0.53  fof(f40,plain,(
% 0.23/0.53    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.23/0.53    inference(cnf_transformation,[],[f2])).
% 0.23/0.53  fof(f2,axiom,(
% 0.23/0.53    ! [X0] : k2_subset_1(X0) = X0),
% 0.23/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 0.23/0.53  fof(f41,plain,(
% 0.23/0.53    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.23/0.53    inference(cnf_transformation,[],[f3])).
% 0.23/0.53  fof(f3,axiom,(
% 0.23/0.53    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.23/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.23/0.53  fof(f62,plain,(
% 0.23/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~r2_hidden(X1,u1_pre_topc(X0)) | v3_pre_topc(X1,X0)) )),
% 0.23/0.53    inference(cnf_transformation,[],[f21])).
% 0.23/0.53  fof(f21,plain,(
% 0.23/0.53    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.23/0.53    inference(ennf_transformation,[],[f8])).
% 0.23/0.53  fof(f8,axiom,(
% 0.23/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0)))))),
% 0.23/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).
% 0.23/0.53  fof(f116,plain,(
% 0.23/0.53    spl6_6),
% 0.23/0.53    inference(avatar_contradiction_clause,[],[f115])).
% 0.23/0.53  fof(f115,plain,(
% 0.23/0.53    $false | spl6_6),
% 0.23/0.53    inference(resolution,[],[f108,f35])).
% 0.23/0.53  fof(f35,plain,(
% 0.23/0.53    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.23/0.53    inference(cnf_transformation,[],[f16])).
% 0.23/0.53  fof(f108,plain,(
% 0.23/0.53    ~m1_subset_1(sK1,u1_struct_0(sK0)) | spl6_6),
% 0.23/0.53    inference(avatar_component_clause,[],[f107])).
% 0.23/0.53  fof(f107,plain,(
% 0.23/0.53    spl6_6 <=> m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.23/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.23/0.53  fof(f112,plain,(
% 0.23/0.53    ~spl6_6 | spl6_7 | spl6_5),
% 0.23/0.53    inference(avatar_split_clause,[],[f105,f100,f110,f107])).
% 0.23/0.53  fof(f100,plain,(
% 0.23/0.53    spl6_5 <=> r2_hidden(sK1,u1_struct_0(sK0))),
% 0.23/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.23/0.53  fof(f105,plain,(
% 0.23/0.53    v1_xboole_0(u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | spl6_5),
% 0.23/0.53    inference(resolution,[],[f101,f66])).
% 0.23/0.53  fof(f66,plain,(
% 0.23/0.53    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.23/0.53    inference(cnf_transformation,[],[f27])).
% 0.23/0.53  fof(f27,plain,(
% 0.23/0.53    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.23/0.53    inference(flattening,[],[f26])).
% 0.23/0.53  fof(f26,plain,(
% 0.23/0.53    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.23/0.53    inference(ennf_transformation,[],[f4])).
% 0.23/0.53  fof(f4,axiom,(
% 0.23/0.53    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.23/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.23/0.53  fof(f101,plain,(
% 0.23/0.53    ~r2_hidden(sK1,u1_struct_0(sK0)) | spl6_5),
% 0.23/0.53    inference(avatar_component_clause,[],[f100])).
% 0.23/0.53  fof(f104,plain,(
% 0.23/0.53    ~spl6_5 | ~spl6_1 | spl6_2),
% 0.23/0.53    inference(avatar_split_clause,[],[f98,f78,f75,f100])).
% 0.23/0.53  fof(f98,plain,(
% 0.23/0.53    r2_hidden(u1_struct_0(sK0),k1_xboole_0) | ~v3_pre_topc(u1_struct_0(sK0),sK0) | ~r2_hidden(sK1,u1_struct_0(sK0))),
% 0.23/0.53    inference(global_subsumption,[],[f86,f97])).
% 0.23/0.53  fof(f97,plain,(
% 0.23/0.53    r2_hidden(u1_struct_0(sK0),k1_xboole_0) | ~v3_pre_topc(u1_struct_0(sK0),sK0) | ~v4_pre_topc(u1_struct_0(sK0),sK0) | ~r2_hidden(sK1,u1_struct_0(sK0))),
% 0.23/0.53    inference(resolution,[],[f96,f69])).
% 0.23/0.53  fof(f96,plain,(
% 0.23/0.53    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X3,k1_xboole_0) | ~v3_pre_topc(X3,sK0) | ~v4_pre_topc(X3,sK0) | ~r2_hidden(sK1,X3)) )),
% 0.23/0.53    inference(forward_demodulation,[],[f32,f34])).
% 0.23/0.53  fof(f34,plain,(
% 0.23/0.53    k1_xboole_0 = sK2),
% 0.23/0.53    inference(cnf_transformation,[],[f16])).
% 0.23/0.53  fof(f32,plain,(
% 0.23/0.53    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X3,sK0) | ~v4_pre_topc(X3,sK0) | ~r2_hidden(sK1,X3) | r2_hidden(X3,sK2)) )),
% 0.23/0.53    inference(cnf_transformation,[],[f16])).
% 0.23/0.53  fof(f86,plain,(
% 0.23/0.53    v4_pre_topc(u1_struct_0(sK0),sK0)),
% 0.23/0.53    inference(global_subsumption,[],[f37,f38,f85])).
% 0.23/0.53  fof(f85,plain,(
% 0.23/0.53    v4_pre_topc(u1_struct_0(sK0),sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.23/0.53    inference(superposition,[],[f65,f84])).
% 0.23/0.53  fof(f84,plain,(
% 0.23/0.53    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.23/0.53    inference(resolution,[],[f83,f38])).
% 0.23/0.53  fof(f83,plain,(
% 0.23/0.53    ( ! [X0] : (~l1_pre_topc(X0) | u1_struct_0(X0) = k2_struct_0(X0)) )),
% 0.23/0.53    inference(resolution,[],[f42,f43])).
% 0.23/0.53  fof(f42,plain,(
% 0.23/0.53    ( ! [X0] : (~l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0)) )),
% 0.23/0.53    inference(cnf_transformation,[],[f17])).
% 0.23/0.53  fof(f17,plain,(
% 0.23/0.53    ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0))),
% 0.23/0.53    inference(ennf_transformation,[],[f7])).
% 0.23/0.53  fof(f7,axiom,(
% 0.23/0.53    ! [X0] : (l1_struct_0(X0) => u1_struct_0(X0) = k2_struct_0(X0))),
% 0.23/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.23/0.53  fof(f65,plain,(
% 0.23/0.53    ( ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.23/0.53    inference(cnf_transformation,[],[f25])).
% 0.23/0.53  fof(f25,plain,(
% 0.23/0.53    ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.23/0.53    inference(flattening,[],[f24])).
% 0.23/0.53  fof(f24,plain,(
% 0.23/0.53    ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.23/0.53    inference(ennf_transformation,[],[f11])).
% 0.23/0.53  fof(f11,axiom,(
% 0.23/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_struct_0(X0),X0))),
% 0.23/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_pre_topc)).
% 0.23/0.53  % SZS output end Proof for theBenchmark
% 0.23/0.53  % (22831)------------------------------
% 0.23/0.53  % (22831)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.53  % (22831)Termination reason: Refutation
% 0.23/0.53  
% 0.23/0.53  % (22831)Memory used [KB]: 10746
% 0.23/0.53  % (22831)Time elapsed: 0.097 s
% 0.23/0.53  % (22831)------------------------------
% 0.23/0.53  % (22831)------------------------------
% 0.23/0.53  % (22833)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.23/0.53  % (22818)Success in time 0.166 s
%------------------------------------------------------------------------------
