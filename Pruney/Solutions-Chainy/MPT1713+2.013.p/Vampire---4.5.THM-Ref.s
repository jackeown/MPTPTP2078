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
% DateTime   : Thu Dec  3 13:17:51 EST 2020

% Result     : Theorem 0.49s
% Output     : Refutation 0.49s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 191 expanded)
%              Number of leaves         :   26 (  72 expanded)
%              Depth                    :    9
%              Number of atoms          :  317 ( 624 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f244,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f73,f81,f90,f94,f106,f118,f125,f136,f141,f149,f163,f182,f235,f240,f243])).

fof(f243,plain,
    ( spl6_12
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f242,f139,f134,f120,f123])).

fof(f123,plain,
    ( spl6_12
  <=> r1_tsep_1(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f120,plain,
    ( spl6_11
  <=> r1_tsep_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f134,plain,
    ( spl6_13
  <=> l1_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f139,plain,
    ( spl6_14
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f242,plain,
    ( r1_tsep_1(sK1,sK2)
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f241,f135])).

fof(f135,plain,
    ( l1_struct_0(sK2)
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f134])).

fof(f241,plain,
    ( ~ l1_struct_0(sK2)
    | r1_tsep_1(sK1,sK2)
    | ~ spl6_11
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f143,f140])).

fof(f140,plain,
    ( l1_struct_0(sK1)
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f139])).

fof(f143,plain,
    ( ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK2)
    | r1_tsep_1(sK1,sK2)
    | ~ spl6_11 ),
    inference(resolution,[],[f121,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0)
      | r1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( l1_struct_0(X1)
        & l1_struct_0(X0) )
     => ( r1_tsep_1(X0,X1)
       => r1_tsep_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

fof(f121,plain,
    ( r1_tsep_1(sK2,sK1)
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f120])).

fof(f240,plain,
    ( spl6_2
    | ~ spl6_14
    | ~ spl6_27 ),
    inference(avatar_contradiction_clause,[],[f239])).

fof(f239,plain,
    ( $false
    | spl6_2
    | ~ spl6_14
    | ~ spl6_27 ),
    inference(subsumption_resolution,[],[f238,f72])).

fof(f72,plain,
    ( ~ v2_struct_0(sK1)
    | spl6_2 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl6_2
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f238,plain,
    ( v2_struct_0(sK1)
    | ~ spl6_14
    | ~ spl6_27 ),
    inference(subsumption_resolution,[],[f237,f140])).

fof(f237,plain,
    ( ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl6_27 ),
    inference(resolution,[],[f234,f49])).

fof(f49,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f234,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | ~ spl6_27 ),
    inference(avatar_component_clause,[],[f233])).

fof(f233,plain,
    ( spl6_27
  <=> v1_xboole_0(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f235,plain,
    ( spl6_27
    | ~ spl6_15
    | ~ spl6_21 ),
    inference(avatar_split_clause,[],[f227,f180,f147,f233])).

fof(f147,plain,
    ( spl6_15
  <=> r1_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f180,plain,
    ( spl6_21
  <=> r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f227,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | ~ spl6_15
    | ~ spl6_21 ),
    inference(resolution,[],[f220,f53])).

fof(f53,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ? [X1] : r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
     => v1_xboole_0(X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f220,plain,
    ( ! [X3] : ~ r2_hidden(X3,u1_struct_0(sK1))
    | ~ spl6_15
    | ~ spl6_21 ),
    inference(resolution,[],[f217,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f217,plain,
    ( ! [X0] : r1_tarski(u1_struct_0(sK1),X0)
    | ~ spl6_15
    | ~ spl6_21 ),
    inference(subsumption_resolution,[],[f212,f148])).

fof(f148,plain,
    ( r1_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f147])).

fof(f212,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))
        | r1_tarski(u1_struct_0(sK1),X0) )
    | ~ spl6_21 ),
    inference(resolution,[],[f189,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,k2_xboole_0(X1,X2)) )
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_xboole_1)).

fof(f189,plain,
    ( ! [X0] : r1_tarski(u1_struct_0(sK1),k2_xboole_0(X0,u1_struct_0(sK2)))
    | ~ spl6_21 ),
    inference(resolution,[],[f181,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f181,plain,
    ( r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ spl6_21 ),
    inference(avatar_component_clause,[],[f180])).

fof(f182,plain,
    ( spl6_21
    | ~ spl6_18 ),
    inference(avatar_split_clause,[],[f173,f161,f180])).

fof(f161,plain,
    ( spl6_18
  <=> m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f173,plain,
    ( r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ spl6_18 ),
    inference(resolution,[],[f162,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f162,plain,
    ( m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f161])).

fof(f163,plain,
    ( spl6_18
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f110,f104,f92,f161])).

fof(f92,plain,
    ( spl6_7
  <=> m1_pre_topc(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f104,plain,
    ( spl6_9
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f110,plain,
    ( m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f108,f105])).

fof(f105,plain,
    ( l1_pre_topc(sK2)
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f104])).

fof(f108,plain,
    ( ~ l1_pre_topc(sK2)
    | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl6_7 ),
    inference(resolution,[],[f93,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f93,plain,
    ( m1_pre_topc(sK1,sK2)
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f92])).

fof(f149,plain,
    ( spl6_15
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f130,f123,f116,f104,f147])).

fof(f116,plain,
    ( spl6_10
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f130,plain,
    ( r1_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f129,f126])).

fof(f126,plain,
    ( l1_struct_0(sK1)
    | ~ spl6_10 ),
    inference(resolution,[],[f117,f48])).

fof(f48,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f117,plain,
    ( l1_pre_topc(sK1)
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f116])).

fof(f129,plain,
    ( r1_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ l1_struct_0(sK1)
    | ~ spl6_9
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f127,f111])).

fof(f111,plain,
    ( l1_struct_0(sK2)
    | ~ spl6_9 ),
    inference(resolution,[],[f105,f48])).

fof(f127,plain,
    ( ~ l1_struct_0(sK2)
    | r1_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ l1_struct_0(sK1)
    | ~ spl6_12 ),
    inference(resolution,[],[f124,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tsep_1)).

fof(f124,plain,
    ( r1_tsep_1(sK1,sK2)
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f123])).

fof(f141,plain,
    ( spl6_14
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f126,f116,f139])).

fof(f136,plain,
    ( spl6_13
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f111,f104,f134])).

fof(f125,plain,
    ( spl6_11
    | spl6_12 ),
    inference(avatar_split_clause,[],[f35,f123,f120])).

fof(f35,plain,
    ( r1_tsep_1(sK1,sK2)
    | r1_tsep_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r1_tsep_1(X2,X1)
                | r1_tsep_1(X1,X2) )
              & m1_pre_topc(X1,X2)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r1_tsep_1(X2,X1)
                | r1_tsep_1(X1,X2) )
              & m1_pre_topc(X1,X2)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ( m1_pre_topc(X1,X2)
                 => ( ~ r1_tsep_1(X2,X1)
                    & ~ r1_tsep_1(X1,X2) ) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ( m1_pre_topc(X1,X2)
                 => ( ~ r1_tsep_1(X2,X1)
                    & ~ r1_tsep_1(X1,X2) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( m1_pre_topc(X1,X2)
               => ( ~ r1_tsep_1(X2,X1)
                  & ~ r1_tsep_1(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_tmap_1)).

fof(f118,plain,
    ( spl6_10
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f109,f104,f92,f116])).

fof(f109,plain,
    ( l1_pre_topc(sK1)
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f107,f105])).

fof(f107,plain,
    ( ~ l1_pre_topc(sK2)
    | l1_pre_topc(sK1)
    | ~ spl6_7 ),
    inference(resolution,[],[f93,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f106,plain,
    ( spl6_9
    | ~ spl6_4
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f101,f88,f79,f104])).

fof(f79,plain,
    ( spl6_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f88,plain,
    ( spl6_6
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f101,plain,
    ( l1_pre_topc(sK2)
    | ~ spl6_4
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f99,f80])).

fof(f80,plain,
    ( l1_pre_topc(sK0)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f79])).

fof(f99,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK2)
    | ~ spl6_6 ),
    inference(resolution,[],[f89,f47])).

fof(f89,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f88])).

fof(f94,plain,(
    spl6_7 ),
    inference(avatar_split_clause,[],[f38,f92])).

fof(f38,plain,(
    m1_pre_topc(sK1,sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f90,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f37,f88])).

fof(f37,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f81,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f42,f79])).

fof(f42,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f73,plain,(
    ~ spl6_2 ),
    inference(avatar_split_clause,[],[f39,f71])).

fof(f39,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:11:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.37  ipcrm: permission denied for id (790102018)
% 0.21/0.37  ipcrm: permission denied for id (790134787)
% 0.21/0.38  ipcrm: permission denied for id (790200332)
% 0.21/0.38  ipcrm: permission denied for id (790265871)
% 0.21/0.39  ipcrm: permission denied for id (790396951)
% 0.21/0.40  ipcrm: permission denied for id (790429722)
% 0.21/0.40  ipcrm: permission denied for id (790495261)
% 0.21/0.41  ipcrm: permission denied for id (790560805)
% 0.21/0.42  ipcrm: permission denied for id (790659121)
% 0.21/0.43  ipcrm: permission denied for id (790691891)
% 0.21/0.43  ipcrm: permission denied for id (790757429)
% 0.21/0.43  ipcrm: permission denied for id (790822968)
% 0.21/0.44  ipcrm: permission denied for id (790986816)
% 0.21/0.45  ipcrm: permission denied for id (791052354)
% 0.21/0.45  ipcrm: permission denied for id (791085123)
% 0.21/0.45  ipcrm: permission denied for id (791150664)
% 0.21/0.46  ipcrm: permission denied for id (791183438)
% 0.21/0.47  ipcrm: permission denied for id (791248981)
% 0.21/0.48  ipcrm: permission denied for id (791347290)
% 0.21/0.49  ipcrm: permission denied for id (791412833)
% 0.21/0.49  ipcrm: permission denied for id (791445603)
% 0.21/0.50  ipcrm: permission denied for id (791543917)
% 0.21/0.50  ipcrm: permission denied for id (791609455)
% 0.21/0.51  ipcrm: permission denied for id (791674999)
% 0.21/0.51  ipcrm: permission denied for id (791707768)
% 0.49/0.60  % (20442)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.49/0.61  % (20442)Refutation found. Thanks to Tanya!
% 0.49/0.61  % SZS status Theorem for theBenchmark
% 0.49/0.61  % SZS output start Proof for theBenchmark
% 0.49/0.61  fof(f244,plain,(
% 0.49/0.61    $false),
% 0.49/0.61    inference(avatar_sat_refutation,[],[f73,f81,f90,f94,f106,f118,f125,f136,f141,f149,f163,f182,f235,f240,f243])).
% 0.49/0.61  fof(f243,plain,(
% 0.49/0.61    spl6_12 | ~spl6_11 | ~spl6_13 | ~spl6_14),
% 0.49/0.61    inference(avatar_split_clause,[],[f242,f139,f134,f120,f123])).
% 0.49/0.61  fof(f123,plain,(
% 0.49/0.61    spl6_12 <=> r1_tsep_1(sK1,sK2)),
% 0.49/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.49/0.61  fof(f120,plain,(
% 0.49/0.61    spl6_11 <=> r1_tsep_1(sK2,sK1)),
% 0.49/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.49/0.61  fof(f134,plain,(
% 0.49/0.61    spl6_13 <=> l1_struct_0(sK2)),
% 0.49/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 0.49/0.61  fof(f139,plain,(
% 0.49/0.61    spl6_14 <=> l1_struct_0(sK1)),
% 0.49/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 0.49/0.61  fof(f242,plain,(
% 0.49/0.61    r1_tsep_1(sK1,sK2) | (~spl6_11 | ~spl6_13 | ~spl6_14)),
% 0.49/0.61    inference(subsumption_resolution,[],[f241,f135])).
% 0.49/0.61  fof(f135,plain,(
% 0.49/0.61    l1_struct_0(sK2) | ~spl6_13),
% 0.49/0.61    inference(avatar_component_clause,[],[f134])).
% 0.49/0.61  fof(f241,plain,(
% 0.49/0.61    ~l1_struct_0(sK2) | r1_tsep_1(sK1,sK2) | (~spl6_11 | ~spl6_14)),
% 0.49/0.61    inference(subsumption_resolution,[],[f143,f140])).
% 0.49/0.61  fof(f140,plain,(
% 0.49/0.61    l1_struct_0(sK1) | ~spl6_14),
% 0.49/0.61    inference(avatar_component_clause,[],[f139])).
% 0.49/0.61  fof(f143,plain,(
% 0.49/0.61    ~l1_struct_0(sK1) | ~l1_struct_0(sK2) | r1_tsep_1(sK1,sK2) | ~spl6_11),
% 0.49/0.61    inference(resolution,[],[f121,f43])).
% 0.49/0.61  fof(f43,plain,(
% 0.49/0.61    ( ! [X0,X1] : (~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0) | r1_tsep_1(X1,X0)) )),
% 0.49/0.61    inference(cnf_transformation,[],[f22])).
% 0.49/0.61  fof(f22,plain,(
% 0.49/0.61    ! [X0,X1] : (r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0))),
% 0.49/0.61    inference(flattening,[],[f21])).
% 0.49/0.61  fof(f21,plain,(
% 0.49/0.61    ! [X0,X1] : ((r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1)) | (~l1_struct_0(X1) | ~l1_struct_0(X0)))),
% 0.49/0.61    inference(ennf_transformation,[],[f13])).
% 0.49/0.61  fof(f13,axiom,(
% 0.49/0.61    ! [X0,X1] : ((l1_struct_0(X1) & l1_struct_0(X0)) => (r1_tsep_1(X0,X1) => r1_tsep_1(X1,X0)))),
% 0.49/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).
% 0.49/0.61  fof(f121,plain,(
% 0.49/0.61    r1_tsep_1(sK2,sK1) | ~spl6_11),
% 0.49/0.61    inference(avatar_component_clause,[],[f120])).
% 0.49/0.61  fof(f240,plain,(
% 0.49/0.61    spl6_2 | ~spl6_14 | ~spl6_27),
% 0.49/0.61    inference(avatar_contradiction_clause,[],[f239])).
% 0.49/0.61  fof(f239,plain,(
% 0.49/0.61    $false | (spl6_2 | ~spl6_14 | ~spl6_27)),
% 0.49/0.61    inference(subsumption_resolution,[],[f238,f72])).
% 0.49/0.61  fof(f72,plain,(
% 0.49/0.61    ~v2_struct_0(sK1) | spl6_2),
% 0.49/0.61    inference(avatar_component_clause,[],[f71])).
% 0.49/0.61  fof(f71,plain,(
% 0.49/0.61    spl6_2 <=> v2_struct_0(sK1)),
% 0.49/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.49/0.61  fof(f238,plain,(
% 0.49/0.61    v2_struct_0(sK1) | (~spl6_14 | ~spl6_27)),
% 0.49/0.61    inference(subsumption_resolution,[],[f237,f140])).
% 0.49/0.61  fof(f237,plain,(
% 0.49/0.61    ~l1_struct_0(sK1) | v2_struct_0(sK1) | ~spl6_27),
% 0.49/0.61    inference(resolution,[],[f234,f49])).
% 0.49/0.61  fof(f49,plain,(
% 0.49/0.61    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.49/0.61    inference(cnf_transformation,[],[f28])).
% 0.49/0.61  fof(f28,plain,(
% 0.49/0.61    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.49/0.61    inference(flattening,[],[f27])).
% 0.49/0.61  fof(f27,plain,(
% 0.49/0.61    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.49/0.61    inference(ennf_transformation,[],[f11])).
% 0.49/0.61  fof(f11,axiom,(
% 0.49/0.61    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.49/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.49/0.61  fof(f234,plain,(
% 0.49/0.61    v1_xboole_0(u1_struct_0(sK1)) | ~spl6_27),
% 0.49/0.61    inference(avatar_component_clause,[],[f233])).
% 0.49/0.61  fof(f233,plain,(
% 0.49/0.61    spl6_27 <=> v1_xboole_0(u1_struct_0(sK1))),
% 0.49/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).
% 0.49/0.61  fof(f235,plain,(
% 0.49/0.61    spl6_27 | ~spl6_15 | ~spl6_21),
% 0.49/0.61    inference(avatar_split_clause,[],[f227,f180,f147,f233])).
% 0.49/0.61  fof(f147,plain,(
% 0.49/0.61    spl6_15 <=> r1_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))),
% 0.49/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 0.49/0.61  fof(f180,plain,(
% 0.49/0.61    spl6_21 <=> r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2))),
% 0.49/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).
% 0.49/0.61  fof(f227,plain,(
% 0.49/0.61    v1_xboole_0(u1_struct_0(sK1)) | (~spl6_15 | ~spl6_21)),
% 0.49/0.61    inference(resolution,[],[f220,f53])).
% 0.49/0.61  fof(f53,plain,(
% 0.49/0.61    ( ! [X0] : (r2_hidden(sK3(X0),X0) | v1_xboole_0(X0)) )),
% 0.49/0.61    inference(cnf_transformation,[],[f31])).
% 0.49/0.61  fof(f31,plain,(
% 0.49/0.61    ! [X0] : (v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0))),
% 0.49/0.61    inference(ennf_transformation,[],[f17])).
% 0.49/0.61  fof(f17,plain,(
% 0.49/0.61    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) => v1_xboole_0(X0))),
% 0.49/0.61    inference(unused_predicate_definition_removal,[],[f1])).
% 0.49/0.61  fof(f1,axiom,(
% 0.49/0.61    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.49/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.49/0.61  fof(f220,plain,(
% 0.49/0.61    ( ! [X3] : (~r2_hidden(X3,u1_struct_0(sK1))) ) | (~spl6_15 | ~spl6_21)),
% 0.49/0.61    inference(resolution,[],[f217,f55])).
% 0.49/0.61  fof(f55,plain,(
% 0.49/0.61    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.49/0.61    inference(cnf_transformation,[],[f33])).
% 0.49/0.61  fof(f33,plain,(
% 0.49/0.61    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.49/0.61    inference(ennf_transformation,[],[f8])).
% 0.49/0.61  fof(f8,axiom,(
% 0.49/0.61    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.49/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.49/0.61  fof(f217,plain,(
% 0.49/0.61    ( ! [X0] : (r1_tarski(u1_struct_0(sK1),X0)) ) | (~spl6_15 | ~spl6_21)),
% 0.49/0.61    inference(subsumption_resolution,[],[f212,f148])).
% 0.49/0.61  fof(f148,plain,(
% 0.49/0.61    r1_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) | ~spl6_15),
% 0.49/0.61    inference(avatar_component_clause,[],[f147])).
% 0.49/0.61  fof(f212,plain,(
% 0.49/0.61    ( ! [X0] : (~r1_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) | r1_tarski(u1_struct_0(sK1),X0)) ) | ~spl6_21),
% 0.49/0.61    inference(resolution,[],[f189,f50])).
% 0.49/0.61  fof(f50,plain,(
% 0.49/0.61    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | r1_tarski(X0,X1)) )),
% 0.49/0.61    inference(cnf_transformation,[],[f30])).
% 0.49/0.61  fof(f30,plain,(
% 0.49/0.61    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 0.49/0.61    inference(flattening,[],[f29])).
% 0.49/0.61  fof(f29,plain,(
% 0.49/0.61    ! [X0,X1,X2] : (r1_tarski(X0,X1) | (~r1_xboole_0(X0,X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))))),
% 0.49/0.61    inference(ennf_transformation,[],[f6])).
% 0.49/0.61  fof(f6,axiom,(
% 0.49/0.61    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 0.49/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_xboole_1)).
% 0.49/0.61  fof(f189,plain,(
% 0.49/0.61    ( ! [X0] : (r1_tarski(u1_struct_0(sK1),k2_xboole_0(X0,u1_struct_0(sK2)))) ) | ~spl6_21),
% 0.49/0.61    inference(resolution,[],[f181,f54])).
% 0.49/0.61  fof(f54,plain,(
% 0.49/0.61    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(X0,k2_xboole_0(X2,X1))) )),
% 0.49/0.61    inference(cnf_transformation,[],[f32])).
% 0.49/0.61  fof(f32,plain,(
% 0.49/0.61    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 0.49/0.61    inference(ennf_transformation,[],[f3])).
% 0.49/0.61  fof(f3,axiom,(
% 0.49/0.61    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 0.49/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).
% 0.49/0.61  fof(f181,plain,(
% 0.49/0.61    r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2)) | ~spl6_21),
% 0.49/0.61    inference(avatar_component_clause,[],[f180])).
% 0.49/0.61  fof(f182,plain,(
% 0.49/0.61    spl6_21 | ~spl6_18),
% 0.49/0.61    inference(avatar_split_clause,[],[f173,f161,f180])).
% 0.49/0.61  fof(f161,plain,(
% 0.49/0.61    spl6_18 <=> m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.49/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 0.49/0.61  fof(f173,plain,(
% 0.49/0.61    r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2)) | ~spl6_18),
% 0.49/0.61    inference(resolution,[],[f162,f52])).
% 0.49/0.61  fof(f52,plain,(
% 0.49/0.61    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.49/0.61    inference(cnf_transformation,[],[f7])).
% 0.49/0.61  fof(f7,axiom,(
% 0.49/0.61    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.49/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.49/0.61  fof(f162,plain,(
% 0.49/0.61    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK2))) | ~spl6_18),
% 0.49/0.61    inference(avatar_component_clause,[],[f161])).
% 0.49/0.61  fof(f163,plain,(
% 0.49/0.61    spl6_18 | ~spl6_7 | ~spl6_9),
% 0.49/0.61    inference(avatar_split_clause,[],[f110,f104,f92,f161])).
% 0.49/0.61  fof(f92,plain,(
% 0.49/0.61    spl6_7 <=> m1_pre_topc(sK1,sK2)),
% 0.49/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.49/0.61  fof(f104,plain,(
% 0.49/0.61    spl6_9 <=> l1_pre_topc(sK2)),
% 0.49/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.49/0.61  fof(f110,plain,(
% 0.49/0.61    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK2))) | (~spl6_7 | ~spl6_9)),
% 0.49/0.61    inference(subsumption_resolution,[],[f108,f105])).
% 0.49/0.61  fof(f105,plain,(
% 0.49/0.61    l1_pre_topc(sK2) | ~spl6_9),
% 0.49/0.61    inference(avatar_component_clause,[],[f104])).
% 0.49/0.61  fof(f108,plain,(
% 0.49/0.61    ~l1_pre_topc(sK2) | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK2))) | ~spl6_7),
% 0.49/0.61    inference(resolution,[],[f93,f46])).
% 0.49/0.61  fof(f46,plain,(
% 0.49/0.61    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.49/0.61    inference(cnf_transformation,[],[f24])).
% 0.49/0.61  fof(f24,plain,(
% 0.49/0.61    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.49/0.61    inference(ennf_transformation,[],[f14])).
% 0.49/0.61  fof(f14,axiom,(
% 0.49/0.61    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.49/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.49/0.61  fof(f93,plain,(
% 0.49/0.61    m1_pre_topc(sK1,sK2) | ~spl6_7),
% 0.49/0.61    inference(avatar_component_clause,[],[f92])).
% 0.49/0.61  fof(f149,plain,(
% 0.49/0.61    spl6_15 | ~spl6_9 | ~spl6_10 | ~spl6_12),
% 0.49/0.61    inference(avatar_split_clause,[],[f130,f123,f116,f104,f147])).
% 0.49/0.61  fof(f116,plain,(
% 0.49/0.61    spl6_10 <=> l1_pre_topc(sK1)),
% 0.49/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.49/0.61  fof(f130,plain,(
% 0.49/0.61    r1_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) | (~spl6_9 | ~spl6_10 | ~spl6_12)),
% 0.49/0.61    inference(subsumption_resolution,[],[f129,f126])).
% 0.49/0.61  fof(f126,plain,(
% 0.49/0.61    l1_struct_0(sK1) | ~spl6_10),
% 0.49/0.61    inference(resolution,[],[f117,f48])).
% 0.49/0.61  fof(f48,plain,(
% 0.49/0.61    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.49/0.61    inference(cnf_transformation,[],[f26])).
% 0.49/0.61  fof(f26,plain,(
% 0.49/0.61    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.49/0.61    inference(ennf_transformation,[],[f9])).
% 0.49/0.61  fof(f9,axiom,(
% 0.49/0.61    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.49/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.49/0.61  fof(f117,plain,(
% 0.49/0.61    l1_pre_topc(sK1) | ~spl6_10),
% 0.49/0.61    inference(avatar_component_clause,[],[f116])).
% 0.49/0.61  fof(f129,plain,(
% 0.49/0.61    r1_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) | ~l1_struct_0(sK1) | (~spl6_9 | ~spl6_12)),
% 0.49/0.61    inference(subsumption_resolution,[],[f127,f111])).
% 0.49/0.61  fof(f111,plain,(
% 0.49/0.61    l1_struct_0(sK2) | ~spl6_9),
% 0.49/0.61    inference(resolution,[],[f105,f48])).
% 0.49/0.61  fof(f127,plain,(
% 0.49/0.61    ~l1_struct_0(sK2) | r1_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) | ~l1_struct_0(sK1) | ~spl6_12),
% 0.49/0.61    inference(resolution,[],[f124,f45])).
% 0.49/0.61  fof(f45,plain,(
% 0.49/0.61    ( ! [X0,X1] : (~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~l1_struct_0(X0)) )),
% 0.49/0.61    inference(cnf_transformation,[],[f23])).
% 0.49/0.61  fof(f23,plain,(
% 0.49/0.61    ! [X0] : (! [X1] : ((r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 0.49/0.61    inference(ennf_transformation,[],[f12])).
% 0.49/0.61  fof(f12,axiom,(
% 0.49/0.61    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => (r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)))))),
% 0.49/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tsep_1)).
% 0.49/0.61  fof(f124,plain,(
% 0.49/0.61    r1_tsep_1(sK1,sK2) | ~spl6_12),
% 0.49/0.61    inference(avatar_component_clause,[],[f123])).
% 0.49/0.61  fof(f141,plain,(
% 0.49/0.61    spl6_14 | ~spl6_10),
% 0.49/0.61    inference(avatar_split_clause,[],[f126,f116,f139])).
% 0.49/0.61  fof(f136,plain,(
% 0.49/0.61    spl6_13 | ~spl6_9),
% 0.49/0.61    inference(avatar_split_clause,[],[f111,f104,f134])).
% 0.49/0.61  fof(f125,plain,(
% 0.49/0.61    spl6_11 | spl6_12),
% 0.49/0.61    inference(avatar_split_clause,[],[f35,f123,f120])).
% 0.49/0.61  fof(f35,plain,(
% 0.49/0.61    r1_tsep_1(sK1,sK2) | r1_tsep_1(sK2,sK1)),
% 0.49/0.61    inference(cnf_transformation,[],[f20])).
% 0.49/0.61  fof(f20,plain,(
% 0.49/0.61    ? [X0] : (? [X1] : (? [X2] : ((r1_tsep_1(X2,X1) | r1_tsep_1(X1,X2)) & m1_pre_topc(X1,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.49/0.61    inference(flattening,[],[f19])).
% 0.49/0.61  fof(f19,plain,(
% 0.49/0.61    ? [X0] : (? [X1] : (? [X2] : (((r1_tsep_1(X2,X1) | r1_tsep_1(X1,X2)) & m1_pre_topc(X1,X2)) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.49/0.61    inference(ennf_transformation,[],[f18])).
% 0.49/0.61  fof(f18,plain,(
% 0.49/0.61    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (m1_pre_topc(X1,X2) => (~r1_tsep_1(X2,X1) & ~r1_tsep_1(X1,X2))))))),
% 0.49/0.61    inference(pure_predicate_removal,[],[f16])).
% 0.49/0.61  fof(f16,negated_conjecture,(
% 0.49/0.61    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (m1_pre_topc(X1,X2) => (~r1_tsep_1(X2,X1) & ~r1_tsep_1(X1,X2))))))),
% 0.49/0.61    inference(negated_conjecture,[],[f15])).
% 0.49/0.61  fof(f15,conjecture,(
% 0.49/0.61    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (m1_pre_topc(X1,X2) => (~r1_tsep_1(X2,X1) & ~r1_tsep_1(X1,X2))))))),
% 0.49/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_tmap_1)).
% 0.49/0.61  fof(f118,plain,(
% 0.49/0.61    spl6_10 | ~spl6_7 | ~spl6_9),
% 0.49/0.61    inference(avatar_split_clause,[],[f109,f104,f92,f116])).
% 0.49/0.61  fof(f109,plain,(
% 0.49/0.61    l1_pre_topc(sK1) | (~spl6_7 | ~spl6_9)),
% 0.49/0.61    inference(subsumption_resolution,[],[f107,f105])).
% 0.49/0.61  fof(f107,plain,(
% 0.49/0.61    ~l1_pre_topc(sK2) | l1_pre_topc(sK1) | ~spl6_7),
% 0.49/0.61    inference(resolution,[],[f93,f47])).
% 0.49/0.61  fof(f47,plain,(
% 0.49/0.61    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | l1_pre_topc(X1)) )),
% 0.49/0.61    inference(cnf_transformation,[],[f25])).
% 0.49/0.61  fof(f25,plain,(
% 0.49/0.61    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.49/0.61    inference(ennf_transformation,[],[f10])).
% 0.49/0.61  fof(f10,axiom,(
% 0.49/0.61    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.49/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.49/0.61  fof(f106,plain,(
% 0.49/0.61    spl6_9 | ~spl6_4 | ~spl6_6),
% 0.49/0.61    inference(avatar_split_clause,[],[f101,f88,f79,f104])).
% 0.49/0.61  fof(f79,plain,(
% 0.49/0.61    spl6_4 <=> l1_pre_topc(sK0)),
% 0.49/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.49/0.61  fof(f88,plain,(
% 0.49/0.61    spl6_6 <=> m1_pre_topc(sK2,sK0)),
% 0.49/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.49/0.61  fof(f101,plain,(
% 0.49/0.61    l1_pre_topc(sK2) | (~spl6_4 | ~spl6_6)),
% 0.49/0.61    inference(subsumption_resolution,[],[f99,f80])).
% 0.49/0.61  fof(f80,plain,(
% 0.49/0.61    l1_pre_topc(sK0) | ~spl6_4),
% 0.49/0.61    inference(avatar_component_clause,[],[f79])).
% 0.49/0.61  fof(f99,plain,(
% 0.49/0.61    ~l1_pre_topc(sK0) | l1_pre_topc(sK2) | ~spl6_6),
% 0.49/0.61    inference(resolution,[],[f89,f47])).
% 0.49/0.61  fof(f89,plain,(
% 0.49/0.61    m1_pre_topc(sK2,sK0) | ~spl6_6),
% 0.49/0.61    inference(avatar_component_clause,[],[f88])).
% 0.49/0.61  fof(f94,plain,(
% 0.49/0.61    spl6_7),
% 0.49/0.61    inference(avatar_split_clause,[],[f38,f92])).
% 0.49/0.61  fof(f38,plain,(
% 0.49/0.61    m1_pre_topc(sK1,sK2)),
% 0.49/0.61    inference(cnf_transformation,[],[f20])).
% 0.49/0.61  fof(f90,plain,(
% 0.49/0.61    spl6_6),
% 0.49/0.61    inference(avatar_split_clause,[],[f37,f88])).
% 0.49/0.61  fof(f37,plain,(
% 0.49/0.61    m1_pre_topc(sK2,sK0)),
% 0.49/0.61    inference(cnf_transformation,[],[f20])).
% 0.49/0.61  fof(f81,plain,(
% 0.49/0.61    spl6_4),
% 0.49/0.61    inference(avatar_split_clause,[],[f42,f79])).
% 0.49/0.61  fof(f42,plain,(
% 0.49/0.61    l1_pre_topc(sK0)),
% 0.49/0.61    inference(cnf_transformation,[],[f20])).
% 0.49/0.61  fof(f73,plain,(
% 0.49/0.61    ~spl6_2),
% 0.49/0.61    inference(avatar_split_clause,[],[f39,f71])).
% 0.49/0.61  fof(f39,plain,(
% 0.49/0.61    ~v2_struct_0(sK1)),
% 0.49/0.61    inference(cnf_transformation,[],[f20])).
% 0.49/0.61  % SZS output end Proof for theBenchmark
% 0.49/0.61  % (20442)------------------------------
% 0.49/0.61  % (20442)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.49/0.61  % (20442)Termination reason: Refutation
% 0.49/0.61  
% 0.49/0.61  % (20442)Memory used [KB]: 6268
% 0.49/0.61  % (20442)Time elapsed: 0.031 s
% 0.49/0.61  % (20442)------------------------------
% 0.49/0.61  % (20442)------------------------------
% 0.49/0.61  % (20264)Success in time 0.254 s
%------------------------------------------------------------------------------
