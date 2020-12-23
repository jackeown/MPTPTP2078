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
% DateTime   : Thu Dec  3 13:21:29 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 180 expanded)
%              Number of leaves         :   24 (  72 expanded)
%              Depth                    :   12
%              Number of atoms          :  316 ( 634 expanded)
%              Number of equality atoms :   32 (  65 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f225,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f52,f57,f62,f73,f78,f86,f91,f96,f105,f110,f118,f148,f188,f205,f214,f219,f224])).

fof(f224,plain,
    ( spl6_22
    | ~ spl6_23 ),
    inference(avatar_contradiction_clause,[],[f223])).

fof(f223,plain,
    ( $false
    | spl6_22
    | ~ spl6_23 ),
    inference(subsumption_resolution,[],[f221,f213])).

fof(f213,plain,
    ( ~ m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl6_22 ),
    inference(avatar_component_clause,[],[f211])).

fof(f211,plain,
    ( spl6_22
  <=> m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f221,plain,
    ( m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_23 ),
    inference(resolution,[],[f218,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f218,plain,
    ( r1_tarski(k1_tarski(sK2),u1_struct_0(sK0))
    | ~ spl6_23 ),
    inference(avatar_component_clause,[],[f216])).

fof(f216,plain,
    ( spl6_23
  <=> r1_tarski(k1_tarski(sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f219,plain,
    ( spl6_23
    | ~ spl6_21 ),
    inference(avatar_split_clause,[],[f209,f202,f216])).

fof(f202,plain,
    ( spl6_21
  <=> r2_hidden(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f209,plain,
    ( r1_tarski(k1_tarski(sK2),u1_struct_0(sK0))
    | ~ spl6_21 ),
    inference(resolution,[],[f204,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f204,plain,
    ( r2_hidden(sK2,u1_struct_0(sK0))
    | ~ spl6_21 ),
    inference(avatar_component_clause,[],[f202])).

fof(f214,plain,
    ( ~ spl6_22
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | spl6_10
    | spl6_11 ),
    inference(avatar_split_clause,[],[f191,f115,f107,f93,f88,f83,f75,f59,f54,f49,f211])).

fof(f49,plain,
    ( spl6_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f54,plain,
    ( spl6_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f59,plain,
    ( spl6_3
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f75,plain,
    ( spl6_5
  <=> v2_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f83,plain,
    ( spl6_6
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f88,plain,
    ( spl6_7
  <=> r1_tarski(k1_tarski(sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f93,plain,
    ( spl6_8
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f107,plain,
    ( spl6_10
  <=> k6_domain_1(u1_struct_0(sK0),sK2) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f115,plain,
    ( spl6_11
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f191,plain,
    ( ~ m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | spl6_10
    | spl6_11 ),
    inference(subsumption_resolution,[],[f171,f190])).

fof(f190,plain,
    ( k1_tarski(sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k1_tarski(sK2)))
    | ~ spl6_6
    | spl6_10
    | spl6_11 ),
    inference(backward_demodulation,[],[f109,f189])).

fof(f189,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK2) = k1_tarski(sK2)
    | ~ spl6_6
    | spl6_11 ),
    inference(resolution,[],[f120,f85])).

fof(f85,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f83])).

fof(f120,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k1_tarski(X0) = k6_domain_1(u1_struct_0(sK0),X0) )
    | spl6_11 ),
    inference(resolution,[],[f117,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f117,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | spl6_11 ),
    inference(avatar_component_clause,[],[f115])).

fof(f109,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
    | spl6_10 ),
    inference(avatar_component_clause,[],[f107])).

fof(f171,plain,
    ( ~ m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tarski(sK2) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k1_tarski(sK2)))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_5
    | ~ spl6_7
    | ~ spl6_8 ),
    inference(resolution,[],[f129,f90])).

fof(f90,plain,
    ( r1_tarski(k1_tarski(sK2),sK1)
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f88])).

fof(f129,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X0)) = X0 )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_5
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f126,f95])).

fof(f95,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f93])).

fof(f126,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X0,sK1)
        | k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X0)) = X0
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_5 ),
    inference(resolution,[],[f66,f77])).

fof(f77,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f75])).

fof(f66,plain,
    ( ! [X0,X1] :
        ( ~ v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X1,X0)
        | k9_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,X1)) = X1
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f65,f51])).

fof(f51,plain,
    ( ~ v2_struct_0(sK0)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f49])).

fof(f65,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X1,X0)
        | k9_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,X1)) = X1
        | ~ v2_tex_2(X0,sK0) )
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f63,f56])).

fof(f56,plain,
    ( v2_pre_topc(sK0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f54])).

fof(f63,plain,
    ( ! [X0,X1] :
        ( ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X1,X0)
        | k9_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,X1)) = X1
        | ~ v2_tex_2(X0,sK0) )
    | ~ spl6_3 ),
    inference(resolution,[],[f61,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X2,X1)
      | k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2
      | ~ v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r1_tarski(X2,X1)
                 => k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_tex_2)).

fof(f61,plain,
    ( l1_pre_topc(sK0)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f59])).

fof(f205,plain,
    ( spl6_21
    | ~ spl6_19 ),
    inference(avatar_split_clause,[],[f193,f185,f202])).

fof(f185,plain,
    ( spl6_19
  <=> sP5(sK2,u1_struct_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f193,plain,
    ( r2_hidden(sK2,u1_struct_0(sK0))
    | ~ spl6_19 ),
    inference(resolution,[],[f187,f40])).

fof(f40,plain,(
    ! [X0,X3,X1] :
      ( ~ sP5(X3,X1,X0)
      | r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f187,plain,
    ( sP5(sK2,u1_struct_0(sK0),sK1)
    | ~ spl6_19 ),
    inference(avatar_component_clause,[],[f185])).

fof(f188,plain,
    ( spl6_19
    | ~ spl6_4
    | ~ spl6_15 ),
    inference(avatar_split_clause,[],[f183,f145,f70,f185])).

fof(f70,plain,
    ( spl6_4
  <=> r2_hidden(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f145,plain,
    ( spl6_15
  <=> sK1 = k3_xboole_0(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f183,plain,
    ( sP5(sK2,u1_struct_0(sK0),sK1)
    | ~ spl6_4
    | ~ spl6_15 ),
    inference(resolution,[],[f154,f72])).

fof(f72,plain,
    ( r2_hidden(sK2,sK1)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f70])).

fof(f154,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | sP5(X0,u1_struct_0(sK0),sK1) )
    | ~ spl6_15 ),
    inference(superposition,[],[f46,f147])).

fof(f147,plain,
    ( sK1 = k3_xboole_0(sK1,u1_struct_0(sK0))
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f145])).

fof(f46,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k3_xboole_0(X0,X1))
      | sP5(X3,X1,X0) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( sP5(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f148,plain,
    ( spl6_15
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f112,f102,f145])).

fof(f102,plain,
    ( spl6_9
  <=> r1_tarski(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f112,plain,
    ( sK1 = k3_xboole_0(sK1,u1_struct_0(sK0))
    | ~ spl6_9 ),
    inference(resolution,[],[f104,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f104,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f102])).

fof(f118,plain,
    ( ~ spl6_11
    | ~ spl6_4
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f113,f93,f70,f115])).

fof(f113,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl6_4
    | ~ spl6_8 ),
    inference(resolution,[],[f79,f95])).

fof(f79,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(X0))
        | ~ v1_xboole_0(X0) )
    | ~ spl6_4 ),
    inference(resolution,[],[f72,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f110,plain,(
    ~ spl6_10 ),
    inference(avatar_split_clause,[],[f21,f107])).

fof(f21,plain,(
    k6_domain_1(u1_struct_0(sK0),sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v2_tex_2(X1,X0)
             => ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ( r2_hidden(X2,X1)
                   => k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tex_2(X1,X0)
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r2_hidden(X2,X1)
                 => k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_tex_2)).

fof(f105,plain,
    ( spl6_9
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f100,f93,f102])).

fof(f100,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl6_8 ),
    inference(resolution,[],[f95,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f96,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f22,f93])).

fof(f22,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f12])).

fof(f91,plain,
    ( spl6_7
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f81,f70,f88])).

fof(f81,plain,
    ( r1_tarski(k1_tarski(sK2),sK1)
    | ~ spl6_4 ),
    inference(resolution,[],[f72,f34])).

fof(f86,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f19,f83])).

% (13363)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
fof(f19,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f12])).

% (13366)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
fof(f78,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f23,f75])).

fof(f23,plain,(
    v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f73,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f20,f70])).

fof(f20,plain,(
    r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f62,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f26,f59])).

fof(f26,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f57,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f25,f54])).

fof(f25,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f52,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f24,f49])).

fof(f24,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n001.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 11:50:44 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.49  % (13367)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.50  % (13384)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.50  % (13381)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.50  % (13375)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.50  % (13372)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.51  % (13381)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f225,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(avatar_sat_refutation,[],[f52,f57,f62,f73,f78,f86,f91,f96,f105,f110,f118,f148,f188,f205,f214,f219,f224])).
% 0.20/0.51  fof(f224,plain,(
% 0.20/0.51    spl6_22 | ~spl6_23),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f223])).
% 0.20/0.51  fof(f223,plain,(
% 0.20/0.51    $false | (spl6_22 | ~spl6_23)),
% 0.20/0.51    inference(subsumption_resolution,[],[f221,f213])).
% 0.20/0.51  fof(f213,plain,(
% 0.20/0.51    ~m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK0))) | spl6_22),
% 0.20/0.51    inference(avatar_component_clause,[],[f211])).
% 0.20/0.51  fof(f211,plain,(
% 0.20/0.51    spl6_22 <=> m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).
% 0.20/0.51  fof(f221,plain,(
% 0.20/0.51    m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl6_23),
% 0.20/0.51    inference(resolution,[],[f218,f36])).
% 0.20/0.51  fof(f36,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f5])).
% 0.20/0.51  fof(f5,axiom,(
% 0.20/0.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.51  fof(f218,plain,(
% 0.20/0.51    r1_tarski(k1_tarski(sK2),u1_struct_0(sK0)) | ~spl6_23),
% 0.20/0.51    inference(avatar_component_clause,[],[f216])).
% 0.20/0.51  fof(f216,plain,(
% 0.20/0.51    spl6_23 <=> r1_tarski(k1_tarski(sK2),u1_struct_0(sK0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).
% 0.20/0.51  fof(f219,plain,(
% 0.20/0.51    spl6_23 | ~spl6_21),
% 0.20/0.51    inference(avatar_split_clause,[],[f209,f202,f216])).
% 0.20/0.51  fof(f202,plain,(
% 0.20/0.51    spl6_21 <=> r2_hidden(sK2,u1_struct_0(sK0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).
% 0.20/0.51  fof(f209,plain,(
% 0.20/0.51    r1_tarski(k1_tarski(sK2),u1_struct_0(sK0)) | ~spl6_21),
% 0.20/0.51    inference(resolution,[],[f204,f34])).
% 0.20/0.51  fof(f34,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f4])).
% 0.20/0.51  fof(f4,axiom,(
% 0.20/0.51    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.20/0.51  fof(f204,plain,(
% 0.20/0.51    r2_hidden(sK2,u1_struct_0(sK0)) | ~spl6_21),
% 0.20/0.51    inference(avatar_component_clause,[],[f202])).
% 0.20/0.51  fof(f214,plain,(
% 0.20/0.51    ~spl6_22 | spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | spl6_10 | spl6_11),
% 0.20/0.51    inference(avatar_split_clause,[],[f191,f115,f107,f93,f88,f83,f75,f59,f54,f49,f211])).
% 0.20/0.51  fof(f49,plain,(
% 0.20/0.51    spl6_1 <=> v2_struct_0(sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.20/0.51  fof(f54,plain,(
% 0.20/0.51    spl6_2 <=> v2_pre_topc(sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.20/0.51  fof(f59,plain,(
% 0.20/0.51    spl6_3 <=> l1_pre_topc(sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.20/0.51  fof(f75,plain,(
% 0.20/0.51    spl6_5 <=> v2_tex_2(sK1,sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.20/0.51  fof(f83,plain,(
% 0.20/0.51    spl6_6 <=> m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.20/0.51  fof(f88,plain,(
% 0.20/0.51    spl6_7 <=> r1_tarski(k1_tarski(sK2),sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.20/0.51  fof(f93,plain,(
% 0.20/0.51    spl6_8 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.20/0.51  fof(f107,plain,(
% 0.20/0.51    spl6_10 <=> k6_domain_1(u1_struct_0(sK0),sK2) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.20/0.51  fof(f115,plain,(
% 0.20/0.51    spl6_11 <=> v1_xboole_0(u1_struct_0(sK0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.20/0.51  fof(f191,plain,(
% 0.20/0.51    ~m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK0))) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | spl6_10 | spl6_11)),
% 0.20/0.51    inference(subsumption_resolution,[],[f171,f190])).
% 0.20/0.51  fof(f190,plain,(
% 0.20/0.51    k1_tarski(sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k1_tarski(sK2))) | (~spl6_6 | spl6_10 | spl6_11)),
% 0.20/0.51    inference(backward_demodulation,[],[f109,f189])).
% 0.20/0.51  fof(f189,plain,(
% 0.20/0.51    k6_domain_1(u1_struct_0(sK0),sK2) = k1_tarski(sK2) | (~spl6_6 | spl6_11)),
% 0.20/0.51    inference(resolution,[],[f120,f85])).
% 0.20/0.51  fof(f85,plain,(
% 0.20/0.51    m1_subset_1(sK2,u1_struct_0(sK0)) | ~spl6_6),
% 0.20/0.51    inference(avatar_component_clause,[],[f83])).
% 0.20/0.51  fof(f120,plain,(
% 0.20/0.51    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k1_tarski(X0) = k6_domain_1(u1_struct_0(sK0),X0)) ) | spl6_11),
% 0.20/0.51    inference(resolution,[],[f117,f33])).
% 0.20/0.51  fof(f33,plain,(
% 0.20/0.51    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k1_tarski(X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f17])).
% 0.20/0.51  fof(f17,plain,(
% 0.20/0.51    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.20/0.51    inference(flattening,[],[f16])).
% 0.20/0.51  fof(f16,plain,(
% 0.20/0.51    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f7])).
% 0.20/0.51  fof(f7,axiom,(
% 0.20/0.51    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.20/0.51  fof(f117,plain,(
% 0.20/0.51    ~v1_xboole_0(u1_struct_0(sK0)) | spl6_11),
% 0.20/0.51    inference(avatar_component_clause,[],[f115])).
% 0.20/0.51  fof(f109,plain,(
% 0.20/0.51    k6_domain_1(u1_struct_0(sK0),sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) | spl6_10),
% 0.20/0.51    inference(avatar_component_clause,[],[f107])).
% 0.20/0.51  fof(f171,plain,(
% 0.20/0.51    ~m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK0))) | k1_tarski(sK2) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k1_tarski(sK2))) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_5 | ~spl6_7 | ~spl6_8)),
% 0.20/0.51    inference(resolution,[],[f129,f90])).
% 0.20/0.51  fof(f90,plain,(
% 0.20/0.51    r1_tarski(k1_tarski(sK2),sK1) | ~spl6_7),
% 0.20/0.51    inference(avatar_component_clause,[],[f88])).
% 0.20/0.51  fof(f129,plain,(
% 0.20/0.51    ( ! [X0] : (~r1_tarski(X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X0)) = X0) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_5 | ~spl6_8)),
% 0.20/0.51    inference(subsumption_resolution,[],[f126,f95])).
% 0.20/0.51  fof(f95,plain,(
% 0.20/0.51    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl6_8),
% 0.20/0.51    inference(avatar_component_clause,[],[f93])).
% 0.20/0.51  fof(f126,plain,(
% 0.20/0.51    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,sK1) | k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X0)) = X0 | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_5)),
% 0.20/0.51    inference(resolution,[],[f66,f77])).
% 0.20/0.51  fof(f77,plain,(
% 0.20/0.51    v2_tex_2(sK1,sK0) | ~spl6_5),
% 0.20/0.51    inference(avatar_component_clause,[],[f75])).
% 0.20/0.51  fof(f66,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~v2_tex_2(X0,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X1,X0) | k9_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,X1)) = X1 | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (spl6_1 | ~spl6_2 | ~spl6_3)),
% 0.20/0.51    inference(subsumption_resolution,[],[f65,f51])).
% 0.20/0.51  fof(f51,plain,(
% 0.20/0.51    ~v2_struct_0(sK0) | spl6_1),
% 0.20/0.51    inference(avatar_component_clause,[],[f49])).
% 0.20/0.51  fof(f65,plain,(
% 0.20/0.51    ( ! [X0,X1] : (v2_struct_0(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X1,X0) | k9_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,X1)) = X1 | ~v2_tex_2(X0,sK0)) ) | (~spl6_2 | ~spl6_3)),
% 0.20/0.51    inference(subsumption_resolution,[],[f63,f56])).
% 0.20/0.51  fof(f56,plain,(
% 0.20/0.51    v2_pre_topc(sK0) | ~spl6_2),
% 0.20/0.51    inference(avatar_component_clause,[],[f54])).
% 0.20/0.51  fof(f63,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X1,X0) | k9_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,X1)) = X1 | ~v2_tex_2(X0,sK0)) ) | ~spl6_3),
% 0.20/0.51    inference(resolution,[],[f61,f28])).
% 0.20/0.51  fof(f28,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X2,X1) | k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~v2_tex_2(X1,X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f14])).
% 0.20/0.51  fof(f14,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.51    inference(flattening,[],[f13])).
% 0.20/0.51  fof(f13,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f8])).
% 0.20/0.51  fof(f8,axiom,(
% 0.20/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X2,X1) => k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2)))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_tex_2)).
% 0.20/0.51  fof(f61,plain,(
% 0.20/0.51    l1_pre_topc(sK0) | ~spl6_3),
% 0.20/0.51    inference(avatar_component_clause,[],[f59])).
% 0.20/0.51  fof(f205,plain,(
% 0.20/0.51    spl6_21 | ~spl6_19),
% 0.20/0.51    inference(avatar_split_clause,[],[f193,f185,f202])).
% 0.20/0.51  fof(f185,plain,(
% 0.20/0.51    spl6_19 <=> sP5(sK2,u1_struct_0(sK0),sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).
% 0.20/0.51  fof(f193,plain,(
% 0.20/0.51    r2_hidden(sK2,u1_struct_0(sK0)) | ~spl6_19),
% 0.20/0.51    inference(resolution,[],[f187,f40])).
% 0.20/0.51  fof(f40,plain,(
% 0.20/0.51    ( ! [X0,X3,X1] : (~sP5(X3,X1,X0) | r2_hidden(X3,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).
% 0.20/0.51  fof(f187,plain,(
% 0.20/0.51    sP5(sK2,u1_struct_0(sK0),sK1) | ~spl6_19),
% 0.20/0.51    inference(avatar_component_clause,[],[f185])).
% 0.20/0.51  fof(f188,plain,(
% 0.20/0.51    spl6_19 | ~spl6_4 | ~spl6_15),
% 0.20/0.51    inference(avatar_split_clause,[],[f183,f145,f70,f185])).
% 0.20/0.51  fof(f70,plain,(
% 0.20/0.51    spl6_4 <=> r2_hidden(sK2,sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.20/0.51  fof(f145,plain,(
% 0.20/0.51    spl6_15 <=> sK1 = k3_xboole_0(sK1,u1_struct_0(sK0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 0.20/0.51  fof(f183,plain,(
% 0.20/0.51    sP5(sK2,u1_struct_0(sK0),sK1) | (~spl6_4 | ~spl6_15)),
% 0.20/0.51    inference(resolution,[],[f154,f72])).
% 0.20/0.51  fof(f72,plain,(
% 0.20/0.51    r2_hidden(sK2,sK1) | ~spl6_4),
% 0.20/0.51    inference(avatar_component_clause,[],[f70])).
% 0.20/0.51  fof(f154,plain,(
% 0.20/0.51    ( ! [X0] : (~r2_hidden(X0,sK1) | sP5(X0,u1_struct_0(sK0),sK1)) ) | ~spl6_15),
% 0.20/0.51    inference(superposition,[],[f46,f147])).
% 0.20/0.51  fof(f147,plain,(
% 0.20/0.51    sK1 = k3_xboole_0(sK1,u1_struct_0(sK0)) | ~spl6_15),
% 0.20/0.51    inference(avatar_component_clause,[],[f145])).
% 0.20/0.51  fof(f46,plain,(
% 0.20/0.51    ( ! [X0,X3,X1] : (~r2_hidden(X3,k3_xboole_0(X0,X1)) | sP5(X3,X1,X0)) )),
% 0.20/0.51    inference(equality_resolution,[],[f42])).
% 0.20/0.51  fof(f42,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (sP5(X3,X1,X0) | ~r2_hidden(X3,X2) | k3_xboole_0(X0,X1) != X2) )),
% 0.20/0.51    inference(cnf_transformation,[],[f1])).
% 0.20/0.51  fof(f148,plain,(
% 0.20/0.51    spl6_15 | ~spl6_9),
% 0.20/0.51    inference(avatar_split_clause,[],[f112,f102,f145])).
% 0.20/0.51  fof(f102,plain,(
% 0.20/0.51    spl6_9 <=> r1_tarski(sK1,u1_struct_0(sK0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.20/0.51  fof(f112,plain,(
% 0.20/0.51    sK1 = k3_xboole_0(sK1,u1_struct_0(sK0)) | ~spl6_9),
% 0.20/0.51    inference(resolution,[],[f104,f32])).
% 0.20/0.51  fof(f32,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.20/0.51    inference(cnf_transformation,[],[f15])).
% 0.20/0.51  fof(f15,plain,(
% 0.20/0.51    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.20/0.51    inference(ennf_transformation,[],[f2])).
% 0.20/0.51  fof(f2,axiom,(
% 0.20/0.51    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.20/0.51  fof(f104,plain,(
% 0.20/0.51    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl6_9),
% 0.20/0.51    inference(avatar_component_clause,[],[f102])).
% 0.20/0.51  fof(f118,plain,(
% 0.20/0.51    ~spl6_11 | ~spl6_4 | ~spl6_8),
% 0.20/0.51    inference(avatar_split_clause,[],[f113,f93,f70,f115])).
% 0.20/0.51  fof(f113,plain,(
% 0.20/0.51    ~v1_xboole_0(u1_struct_0(sK0)) | (~spl6_4 | ~spl6_8)),
% 0.20/0.51    inference(resolution,[],[f79,f95])).
% 0.20/0.51  fof(f79,plain,(
% 0.20/0.51    ( ! [X0] : (~m1_subset_1(sK1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) ) | ~spl6_4),
% 0.20/0.51    inference(resolution,[],[f72,f45])).
% 0.20/0.51  fof(f45,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f18])).
% 0.20/0.51  fof(f18,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.20/0.51    inference(ennf_transformation,[],[f6])).
% 0.20/0.51  fof(f6,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 0.20/0.51  fof(f110,plain,(
% 0.20/0.51    ~spl6_10),
% 0.20/0.51    inference(avatar_split_clause,[],[f21,f107])).
% 0.20/0.51  fof(f21,plain,(
% 0.20/0.51    k6_domain_1(u1_struct_0(sK0),sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))),
% 0.20/0.51    inference(cnf_transformation,[],[f12])).
% 0.20/0.51  fof(f12,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : (? [X2] : (k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.51    inference(flattening,[],[f11])).
% 0.20/0.51  fof(f11,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : ((? [X2] : ((k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & r2_hidden(X2,X1)) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f10])).
% 0.20/0.51  fof(f10,negated_conjecture,(
% 0.20/0.51    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,X1) => k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))))))))),
% 0.20/0.51    inference(negated_conjecture,[],[f9])).
% 0.20/0.51  fof(f9,conjecture,(
% 0.20/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,X1) => k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))))))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_tex_2)).
% 0.20/0.51  fof(f105,plain,(
% 0.20/0.51    spl6_9 | ~spl6_8),
% 0.20/0.51    inference(avatar_split_clause,[],[f100,f93,f102])).
% 0.20/0.51  fof(f100,plain,(
% 0.20/0.51    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl6_8),
% 0.20/0.51    inference(resolution,[],[f95,f37])).
% 0.20/0.51  fof(f37,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f5])).
% 0.20/0.51  fof(f96,plain,(
% 0.20/0.51    spl6_8),
% 0.20/0.51    inference(avatar_split_clause,[],[f22,f93])).
% 0.20/0.51  fof(f22,plain,(
% 0.20/0.51    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.51    inference(cnf_transformation,[],[f12])).
% 0.20/0.51  fof(f91,plain,(
% 0.20/0.51    spl6_7 | ~spl6_4),
% 0.20/0.51    inference(avatar_split_clause,[],[f81,f70,f88])).
% 0.20/0.51  fof(f81,plain,(
% 0.20/0.51    r1_tarski(k1_tarski(sK2),sK1) | ~spl6_4),
% 0.20/0.51    inference(resolution,[],[f72,f34])).
% 0.20/0.51  fof(f86,plain,(
% 0.20/0.51    spl6_6),
% 0.20/0.51    inference(avatar_split_clause,[],[f19,f83])).
% 0.20/0.51  % (13363)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.51  fof(f19,plain,(
% 0.20/0.51    m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.20/0.51    inference(cnf_transformation,[],[f12])).
% 0.20/0.51  % (13366)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.51  fof(f78,plain,(
% 0.20/0.51    spl6_5),
% 0.20/0.51    inference(avatar_split_clause,[],[f23,f75])).
% 0.20/0.51  fof(f23,plain,(
% 0.20/0.51    v2_tex_2(sK1,sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f12])).
% 0.20/0.51  fof(f73,plain,(
% 0.20/0.51    spl6_4),
% 0.20/0.51    inference(avatar_split_clause,[],[f20,f70])).
% 0.20/0.51  fof(f20,plain,(
% 0.20/0.51    r2_hidden(sK2,sK1)),
% 0.20/0.51    inference(cnf_transformation,[],[f12])).
% 0.20/0.51  fof(f62,plain,(
% 0.20/0.51    spl6_3),
% 0.20/0.51    inference(avatar_split_clause,[],[f26,f59])).
% 0.20/0.51  fof(f26,plain,(
% 0.20/0.51    l1_pre_topc(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f12])).
% 0.20/0.51  fof(f57,plain,(
% 0.20/0.51    spl6_2),
% 0.20/0.51    inference(avatar_split_clause,[],[f25,f54])).
% 0.20/0.51  fof(f25,plain,(
% 0.20/0.51    v2_pre_topc(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f12])).
% 0.20/0.51  fof(f52,plain,(
% 0.20/0.51    ~spl6_1),
% 0.20/0.51    inference(avatar_split_clause,[],[f24,f49])).
% 0.20/0.51  fof(f24,plain,(
% 0.20/0.51    ~v2_struct_0(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f12])).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (13381)------------------------------
% 0.20/0.51  % (13381)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (13381)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (13381)Memory used [KB]: 10874
% 0.20/0.51  % (13381)Time elapsed: 0.087 s
% 0.20/0.51  % (13381)------------------------------
% 0.20/0.51  % (13381)------------------------------
% 0.20/0.51  % (13356)Success in time 0.154 s
%------------------------------------------------------------------------------
