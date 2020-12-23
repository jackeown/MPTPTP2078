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
% DateTime   : Thu Dec  3 13:21:17 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 149 expanded)
%              Number of leaves         :   24 (  57 expanded)
%              Depth                    :   12
%              Number of atoms          :  242 ( 412 expanded)
%              Number of equality atoms :   38 (  52 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f328,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f56,f61,f66,f76,f82,f89,f97,f116,f123,f218,f224,f327])).

% (2904)Refutation not found, incomplete strategy% (2904)------------------------------
% (2904)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f327,plain,
    ( spl4_8
    | ~ spl4_1
    | ~ spl4_12
    | ~ spl4_11
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f326,f221,f113,f120,f53,f94])).

fof(f94,plain,
    ( spl4_8
  <=> v2_tex_2(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f53,plain,
    ( spl4_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f120,plain,
    ( spl4_12
  <=> v3_pre_topc(k2_struct_0(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f113,plain,
    ( spl4_11
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f221,plain,
    ( spl4_20
  <=> k1_xboole_0 = sK2(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f326,plain,
    ( ~ v3_pre_topc(k2_struct_0(sK0),sK0)
    | ~ l1_pre_topc(sK0)
    | v2_tex_2(k1_xboole_0,sK0)
    | ~ spl4_11
    | ~ spl4_20 ),
    inference(trivial_inequality_removal,[],[f325])).

fof(f325,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ v3_pre_topc(k2_struct_0(sK0),sK0)
    | ~ l1_pre_topc(sK0)
    | v2_tex_2(k1_xboole_0,sK0)
    | ~ spl4_11
    | ~ spl4_20 ),
    inference(forward_demodulation,[],[f324,f223])).

fof(f223,plain,
    ( k1_xboole_0 = sK2(sK0,k1_xboole_0)
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f221])).

fof(f324,plain,
    ( ~ v3_pre_topc(k2_struct_0(sK0),sK0)
    | ~ l1_pre_topc(sK0)
    | k1_xboole_0 != sK2(sK0,k1_xboole_0)
    | v2_tex_2(k1_xboole_0,sK0)
    | ~ spl4_11 ),
    inference(superposition,[],[f297,f115])).

fof(f115,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f113])).

fof(f297,plain,(
    ! [X1] :
      ( ~ v3_pre_topc(u1_struct_0(X1),X1)
      | ~ l1_pre_topc(X1)
      | k1_xboole_0 != sK2(X1,k1_xboole_0)
      | v2_tex_2(k1_xboole_0,X1) ) ),
    inference(forward_demodulation,[],[f296,f104])).

fof(f104,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f46,f48])).

fof(f48,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f46,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f296,plain,(
    ! [X1] :
      ( sK2(X1,k1_xboole_0) != k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v3_pre_topc(u1_struct_0(X1),X1)
      | v2_tex_2(k1_xboole_0,X1) ) ),
    inference(forward_demodulation,[],[f292,f125])).

fof(f125,plain,(
    ! [X2,X3] : k9_subset_1(X2,X3,X2) = k4_xboole_0(X3,k4_xboole_0(X3,X2)) ),
    inference(resolution,[],[f51,f83])).

fof(f83,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f36,f34])).

fof(f34,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f36,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k4_xboole_0(X1,k4_xboole_0(X1,X2)) ) ),
    inference(definition_unfolding,[],[f50,f49])).

fof(f49,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f292,plain,(
    ! [X1] :
      ( ~ l1_pre_topc(X1)
      | ~ v3_pre_topc(u1_struct_0(X1),X1)
      | sK2(X1,k1_xboole_0) != k9_subset_1(u1_struct_0(X1),k1_xboole_0,u1_struct_0(X1))
      | v2_tex_2(k1_xboole_0,X1) ) ),
    inference(resolution,[],[f193,f83])).

fof(f193,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v3_pre_topc(X1,X0)
      | sK2(X0,k1_xboole_0) != k9_subset_1(u1_struct_0(X0),k1_xboole_0,X1)
      | v2_tex_2(k1_xboole_0,X0) ) ),
    inference(resolution,[],[f40,f35])).

fof(f35,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f40,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X3,X0)
      | k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1)
      | v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ~ ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                            & v3_pre_topc(X3,X0) ) )
                    & r1_tarski(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tex_2)).

fof(f224,plain,
    ( spl4_20
    | ~ spl4_19 ),
    inference(avatar_split_clause,[],[f219,f215,f221])).

fof(f215,plain,
    ( spl4_19
  <=> r1_tarski(sK2(sK0,k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f219,plain,
    ( k1_xboole_0 = sK2(sK0,k1_xboole_0)
    | ~ spl4_19 ),
    inference(resolution,[],[f217,f46])).

fof(f217,plain,
    ( r1_tarski(sK2(sK0,k1_xboole_0),k1_xboole_0)
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f215])).

fof(f218,plain,
    ( spl4_8
    | spl4_19
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f213,f53,f215,f94])).

fof(f213,plain,
    ( r1_tarski(sK2(sK0,k1_xboole_0),k1_xboole_0)
    | v2_tex_2(k1_xboole_0,sK0)
    | ~ spl4_1 ),
    inference(resolution,[],[f134,f55])).

fof(f55,plain,
    ( l1_pre_topc(sK0)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f53])).

fof(f134,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | r1_tarski(sK2(X0,k1_xboole_0),k1_xboole_0)
      | v2_tex_2(k1_xboole_0,X0) ) ),
    inference(resolution,[],[f45,f35])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | r1_tarski(sK2(X0,X1),X1)
      | v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f123,plain,
    ( spl4_12
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f118,f58,f53,f120])).

fof(f58,plain,
    ( spl4_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f118,plain,
    ( ~ l1_pre_topc(sK0)
    | v3_pre_topc(k2_struct_0(sK0),sK0)
    | ~ spl4_2 ),
    inference(resolution,[],[f47,f60])).

fof(f60,plain,
    ( v2_pre_topc(sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f58])).

fof(f47,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v3_pre_topc(k2_struct_0(X0),X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_tops_1)).

fof(f116,plain,
    ( spl4_11
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f111,f79,f113])).

fof(f79,plain,
    ( spl4_6
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f111,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl4_6 ),
    inference(resolution,[],[f38,f81])).

fof(f81,plain,
    ( l1_struct_0(sK0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f79])).

fof(f38,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f97,plain,
    ( ~ spl4_8
    | spl4_3
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f91,f86,f63,f94])).

fof(f63,plain,
    ( spl4_3
  <=> v2_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f86,plain,
    ( spl4_7
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f91,plain,
    ( ~ v2_tex_2(k1_xboole_0,sK0)
    | spl4_3
    | ~ spl4_7 ),
    inference(backward_demodulation,[],[f65,f88])).

fof(f88,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f86])).

fof(f65,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f63])).

fof(f89,plain,
    ( spl4_7
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f84,f73,f86])).

fof(f73,plain,
    ( spl4_5
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f84,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_5 ),
    inference(resolution,[],[f37,f75])).

fof(f75,plain,
    ( v1_xboole_0(sK1)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f73])).

fof(f37,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f82,plain,
    ( spl4_6
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f77,f53,f79])).

fof(f77,plain,
    ( l1_struct_0(sK0)
    | ~ spl4_1 ),
    inference(resolution,[],[f39,f55])).

fof(f39,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f76,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f29,f73])).

fof(f29,plain,(
    v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_xboole_0(X1) )
           => v2_tex_2(X1,X0) ) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_xboole_0(X1) )
           => v2_tex_2(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tex_2)).

fof(f66,plain,(
    ~ spl4_3 ),
    inference(avatar_split_clause,[],[f31,f63])).

fof(f31,plain,(
    ~ v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f61,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f32,f58])).

fof(f32,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f56,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f33,f53])).

fof(f33,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:08:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (2905)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.50  % (2920)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.50  % (2898)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.50  % (2916)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.51  % (2908)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.51  % (2910)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.51  % (2900)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.51  % (2916)Refutation not found, incomplete strategy% (2916)------------------------------
% 0.20/0.51  % (2916)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (2916)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (2916)Memory used [KB]: 10746
% 0.20/0.51  % (2916)Time elapsed: 0.066 s
% 0.20/0.51  % (2916)------------------------------
% 0.20/0.51  % (2916)------------------------------
% 0.20/0.52  % (2912)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.52  % (2902)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.52  % (2897)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.52  % (2918)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.52  % (2910)Refutation found. Thanks to Tanya!
% 0.20/0.52  % SZS status Theorem for theBenchmark
% 0.20/0.52  % (2894)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.52  % (2920)Refutation not found, incomplete strategy% (2920)------------------------------
% 0.20/0.52  % (2920)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (2920)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (2920)Memory used [KB]: 10874
% 0.20/0.52  % (2920)Time elapsed: 0.120 s
% 0.20/0.52  % (2920)------------------------------
% 0.20/0.52  % (2920)------------------------------
% 0.20/0.53  % (2906)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  % (2898)Refutation not found, incomplete strategy% (2898)------------------------------
% 0.20/0.53  % (2898)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (2898)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (2898)Memory used [KB]: 6268
% 0.20/0.53  % (2898)Time elapsed: 0.100 s
% 0.20/0.53  % (2898)------------------------------
% 0.20/0.53  % (2898)------------------------------
% 0.20/0.53  % (2896)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.53  % (2899)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.53  % (2913)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.53  % (2921)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.53  % (2901)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.53  % (2895)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.53  % (2915)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.53  % (2923)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.53  % (2919)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.53  % (2907)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.53  % (2909)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.53  % (2914)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.54  % (2911)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.54  % (2911)Refutation not found, incomplete strategy% (2911)------------------------------
% 0.20/0.54  % (2911)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (2911)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (2911)Memory used [KB]: 10618
% 0.20/0.54  % (2911)Time elapsed: 0.128 s
% 0.20/0.54  % (2911)------------------------------
% 0.20/0.54  % (2911)------------------------------
% 0.20/0.54  % (2914)Refutation not found, incomplete strategy% (2914)------------------------------
% 0.20/0.54  % (2914)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (2914)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (2914)Memory used [KB]: 10746
% 0.20/0.54  % (2914)Time elapsed: 0.132 s
% 0.20/0.54  % (2914)------------------------------
% 0.20/0.54  % (2914)------------------------------
% 0.20/0.54  % (2917)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.54  % (2922)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.54  % (2904)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.54  % (2903)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.54  % (2909)Refutation not found, incomplete strategy% (2909)------------------------------
% 0.20/0.54  % (2909)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (2909)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (2909)Memory used [KB]: 6268
% 0.20/0.54  % (2909)Time elapsed: 0.129 s
% 0.20/0.54  % (2909)------------------------------
% 0.20/0.54  % (2909)------------------------------
% 0.20/0.54  % (2915)Refutation not found, incomplete strategy% (2915)------------------------------
% 0.20/0.54  % (2915)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % SZS output start Proof for theBenchmark
% 0.20/0.54  fof(f328,plain,(
% 0.20/0.54    $false),
% 0.20/0.54    inference(avatar_sat_refutation,[],[f56,f61,f66,f76,f82,f89,f97,f116,f123,f218,f224,f327])).
% 0.20/0.54  % (2904)Refutation not found, incomplete strategy% (2904)------------------------------
% 0.20/0.54  % (2904)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  fof(f327,plain,(
% 0.20/0.54    spl4_8 | ~spl4_1 | ~spl4_12 | ~spl4_11 | ~spl4_20),
% 0.20/0.54    inference(avatar_split_clause,[],[f326,f221,f113,f120,f53,f94])).
% 0.20/0.54  fof(f94,plain,(
% 0.20/0.54    spl4_8 <=> v2_tex_2(k1_xboole_0,sK0)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.20/0.54  fof(f53,plain,(
% 0.20/0.54    spl4_1 <=> l1_pre_topc(sK0)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.54  fof(f120,plain,(
% 0.20/0.54    spl4_12 <=> v3_pre_topc(k2_struct_0(sK0),sK0)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.20/0.54  fof(f113,plain,(
% 0.20/0.54    spl4_11 <=> u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.20/0.54  fof(f221,plain,(
% 0.20/0.54    spl4_20 <=> k1_xboole_0 = sK2(sK0,k1_xboole_0)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 0.20/0.54  fof(f326,plain,(
% 0.20/0.54    ~v3_pre_topc(k2_struct_0(sK0),sK0) | ~l1_pre_topc(sK0) | v2_tex_2(k1_xboole_0,sK0) | (~spl4_11 | ~spl4_20)),
% 0.20/0.54    inference(trivial_inequality_removal,[],[f325])).
% 0.20/0.54  fof(f325,plain,(
% 0.20/0.54    k1_xboole_0 != k1_xboole_0 | ~v3_pre_topc(k2_struct_0(sK0),sK0) | ~l1_pre_topc(sK0) | v2_tex_2(k1_xboole_0,sK0) | (~spl4_11 | ~spl4_20)),
% 0.20/0.54    inference(forward_demodulation,[],[f324,f223])).
% 0.20/0.54  fof(f223,plain,(
% 0.20/0.54    k1_xboole_0 = sK2(sK0,k1_xboole_0) | ~spl4_20),
% 0.20/0.54    inference(avatar_component_clause,[],[f221])).
% 0.20/0.54  fof(f324,plain,(
% 0.20/0.54    ~v3_pre_topc(k2_struct_0(sK0),sK0) | ~l1_pre_topc(sK0) | k1_xboole_0 != sK2(sK0,k1_xboole_0) | v2_tex_2(k1_xboole_0,sK0) | ~spl4_11),
% 0.20/0.54    inference(superposition,[],[f297,f115])).
% 0.20/0.54  fof(f115,plain,(
% 0.20/0.54    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl4_11),
% 0.20/0.54    inference(avatar_component_clause,[],[f113])).
% 0.20/0.54  fof(f297,plain,(
% 0.20/0.54    ( ! [X1] : (~v3_pre_topc(u1_struct_0(X1),X1) | ~l1_pre_topc(X1) | k1_xboole_0 != sK2(X1,k1_xboole_0) | v2_tex_2(k1_xboole_0,X1)) )),
% 0.20/0.54    inference(forward_demodulation,[],[f296,f104])).
% 0.20/0.54  fof(f104,plain,(
% 0.20/0.54    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.20/0.54    inference(resolution,[],[f46,f48])).
% 0.20/0.54  fof(f48,plain,(
% 0.20/0.54    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f2])).
% 0.20/0.54  fof(f2,axiom,(
% 0.20/0.54    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.20/0.54  fof(f46,plain,(
% 0.20/0.54    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.20/0.54    inference(cnf_transformation,[],[f25])).
% 0.20/0.54  fof(f25,plain,(
% 0.20/0.54    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.20/0.54    inference(ennf_transformation,[],[f3])).
% 0.20/0.54  fof(f3,axiom,(
% 0.20/0.54    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.20/0.54  fof(f296,plain,(
% 0.20/0.54    ( ! [X1] : (sK2(X1,k1_xboole_0) != k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,u1_struct_0(X1))) | ~l1_pre_topc(X1) | ~v3_pre_topc(u1_struct_0(X1),X1) | v2_tex_2(k1_xboole_0,X1)) )),
% 0.20/0.54    inference(forward_demodulation,[],[f292,f125])).
% 0.20/0.54  fof(f125,plain,(
% 0.20/0.54    ( ! [X2,X3] : (k9_subset_1(X2,X3,X2) = k4_xboole_0(X3,k4_xboole_0(X3,X2))) )),
% 0.20/0.54    inference(resolution,[],[f51,f83])).
% 0.20/0.54  fof(f83,plain,(
% 0.20/0.54    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.20/0.54    inference(forward_demodulation,[],[f36,f34])).
% 0.20/0.54  fof(f34,plain,(
% 0.20/0.54    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.20/0.54    inference(cnf_transformation,[],[f5])).
% 0.20/0.54  fof(f5,axiom,(
% 0.20/0.54    ! [X0] : k2_subset_1(X0) = X0),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 0.20/0.54  fof(f36,plain,(
% 0.20/0.54    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f6])).
% 0.20/0.54  fof(f6,axiom,(
% 0.20/0.54    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.20/0.54  fof(f51,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k4_xboole_0(X1,k4_xboole_0(X1,X2))) )),
% 0.20/0.54    inference(definition_unfolding,[],[f50,f49])).
% 0.20/0.54  fof(f49,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f4])).
% 0.20/0.54  fof(f4,axiom,(
% 0.20/0.54    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.20/0.54  fof(f50,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f28])).
% 0.20/0.54  fof(f28,plain,(
% 0.20/0.54    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.20/0.54    inference(ennf_transformation,[],[f7])).
% 0.20/0.54  fof(f7,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.20/0.54  fof(f292,plain,(
% 0.20/0.54    ( ! [X1] : (~l1_pre_topc(X1) | ~v3_pre_topc(u1_struct_0(X1),X1) | sK2(X1,k1_xboole_0) != k9_subset_1(u1_struct_0(X1),k1_xboole_0,u1_struct_0(X1)) | v2_tex_2(k1_xboole_0,X1)) )),
% 0.20/0.54    inference(resolution,[],[f193,f83])).
% 0.20/0.54  fof(f193,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v3_pre_topc(X1,X0) | sK2(X0,k1_xboole_0) != k9_subset_1(u1_struct_0(X0),k1_xboole_0,X1) | v2_tex_2(k1_xboole_0,X0)) )),
% 0.20/0.54    inference(resolution,[],[f40,f35])).
% 0.20/0.54  fof(f35,plain,(
% 0.20/0.54    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f8])).
% 0.20/0.54  fof(f8,axiom,(
% 0.20/0.54    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.20/0.54  fof(f40,plain,(
% 0.20/0.54    ( ! [X0,X3,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X3,X0) | k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1) | v2_tex_2(X1,X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f24])).
% 0.20/0.54  fof(f24,plain,(
% 0.20/0.54    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.54    inference(flattening,[],[f23])).
% 0.20/0.54  fof(f23,plain,(
% 0.20/0.54    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((? [X3] : ((k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.54    inference(ennf_transformation,[],[f13])).
% 0.20/0.54  fof(f13,axiom,(
% 0.20/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0))) & r1_tarski(X2,X1))))))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tex_2)).
% 0.20/0.54  fof(f224,plain,(
% 0.20/0.54    spl4_20 | ~spl4_19),
% 0.20/0.54    inference(avatar_split_clause,[],[f219,f215,f221])).
% 0.20/0.54  fof(f215,plain,(
% 0.20/0.54    spl4_19 <=> r1_tarski(sK2(sK0,k1_xboole_0),k1_xboole_0)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.20/0.54  fof(f219,plain,(
% 0.20/0.54    k1_xboole_0 = sK2(sK0,k1_xboole_0) | ~spl4_19),
% 0.20/0.54    inference(resolution,[],[f217,f46])).
% 0.20/0.54  fof(f217,plain,(
% 0.20/0.54    r1_tarski(sK2(sK0,k1_xboole_0),k1_xboole_0) | ~spl4_19),
% 0.20/0.54    inference(avatar_component_clause,[],[f215])).
% 0.20/0.54  fof(f218,plain,(
% 0.20/0.54    spl4_8 | spl4_19 | ~spl4_1),
% 0.20/0.54    inference(avatar_split_clause,[],[f213,f53,f215,f94])).
% 0.20/0.54  fof(f213,plain,(
% 0.20/0.54    r1_tarski(sK2(sK0,k1_xboole_0),k1_xboole_0) | v2_tex_2(k1_xboole_0,sK0) | ~spl4_1),
% 0.20/0.54    inference(resolution,[],[f134,f55])).
% 0.20/0.54  fof(f55,plain,(
% 0.20/0.54    l1_pre_topc(sK0) | ~spl4_1),
% 0.20/0.54    inference(avatar_component_clause,[],[f53])).
% 0.20/0.54  fof(f134,plain,(
% 0.20/0.54    ( ! [X0] : (~l1_pre_topc(X0) | r1_tarski(sK2(X0,k1_xboole_0),k1_xboole_0) | v2_tex_2(k1_xboole_0,X0)) )),
% 0.20/0.54    inference(resolution,[],[f45,f35])).
% 0.20/0.54  fof(f45,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | r1_tarski(sK2(X0,X1),X1) | v2_tex_2(X1,X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f24])).
% 0.20/0.54  fof(f123,plain,(
% 0.20/0.54    spl4_12 | ~spl4_1 | ~spl4_2),
% 0.20/0.54    inference(avatar_split_clause,[],[f118,f58,f53,f120])).
% 0.20/0.54  fof(f58,plain,(
% 0.20/0.54    spl4_2 <=> v2_pre_topc(sK0)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.54  fof(f118,plain,(
% 0.20/0.54    ~l1_pre_topc(sK0) | v3_pre_topc(k2_struct_0(sK0),sK0) | ~spl4_2),
% 0.20/0.54    inference(resolution,[],[f47,f60])).
% 0.20/0.54  fof(f60,plain,(
% 0.20/0.54    v2_pre_topc(sK0) | ~spl4_2),
% 0.20/0.54    inference(avatar_component_clause,[],[f58])).
% 0.20/0.54  fof(f47,plain,(
% 0.20/0.54    ( ! [X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v3_pre_topc(k2_struct_0(X0),X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f27])).
% 0.20/0.54  fof(f27,plain,(
% 0.20/0.54    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.54    inference(flattening,[],[f26])).
% 0.20/0.54  fof(f26,plain,(
% 0.20/0.54    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.54    inference(ennf_transformation,[],[f12])).
% 0.20/0.54  fof(f12,axiom,(
% 0.20/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_struct_0(X0),X0))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_tops_1)).
% 0.20/0.54  fof(f116,plain,(
% 0.20/0.54    spl4_11 | ~spl4_6),
% 0.20/0.54    inference(avatar_split_clause,[],[f111,f79,f113])).
% 0.20/0.54  fof(f79,plain,(
% 0.20/0.54    spl4_6 <=> l1_struct_0(sK0)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.20/0.54  fof(f111,plain,(
% 0.20/0.54    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl4_6),
% 0.20/0.54    inference(resolution,[],[f38,f81])).
% 0.20/0.54  fof(f81,plain,(
% 0.20/0.54    l1_struct_0(sK0) | ~spl4_6),
% 0.20/0.54    inference(avatar_component_clause,[],[f79])).
% 0.20/0.54  fof(f38,plain,(
% 0.20/0.54    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f21])).
% 0.20/0.54  fof(f21,plain,(
% 0.20/0.54    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.20/0.54    inference(ennf_transformation,[],[f10])).
% 0.20/0.54  fof(f10,axiom,(
% 0.20/0.54    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.20/0.54  fof(f97,plain,(
% 0.20/0.54    ~spl4_8 | spl4_3 | ~spl4_7),
% 0.20/0.54    inference(avatar_split_clause,[],[f91,f86,f63,f94])).
% 0.20/0.54  fof(f63,plain,(
% 0.20/0.54    spl4_3 <=> v2_tex_2(sK1,sK0)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.54  fof(f86,plain,(
% 0.20/0.54    spl4_7 <=> k1_xboole_0 = sK1),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.20/0.54  fof(f91,plain,(
% 0.20/0.54    ~v2_tex_2(k1_xboole_0,sK0) | (spl4_3 | ~spl4_7)),
% 0.20/0.54    inference(backward_demodulation,[],[f65,f88])).
% 0.20/0.54  fof(f88,plain,(
% 0.20/0.54    k1_xboole_0 = sK1 | ~spl4_7),
% 0.20/0.54    inference(avatar_component_clause,[],[f86])).
% 0.20/0.54  fof(f65,plain,(
% 0.20/0.54    ~v2_tex_2(sK1,sK0) | spl4_3),
% 0.20/0.54    inference(avatar_component_clause,[],[f63])).
% 0.20/0.54  fof(f89,plain,(
% 0.20/0.54    spl4_7 | ~spl4_5),
% 0.20/0.54    inference(avatar_split_clause,[],[f84,f73,f86])).
% 0.20/0.54  fof(f73,plain,(
% 0.20/0.54    spl4_5 <=> v1_xboole_0(sK1)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.20/0.54  fof(f84,plain,(
% 0.20/0.54    k1_xboole_0 = sK1 | ~spl4_5),
% 0.20/0.54    inference(resolution,[],[f37,f75])).
% 0.20/0.54  fof(f75,plain,(
% 0.20/0.54    v1_xboole_0(sK1) | ~spl4_5),
% 0.20/0.54    inference(avatar_component_clause,[],[f73])).
% 0.20/0.54  fof(f37,plain,(
% 0.20/0.54    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.20/0.54    inference(cnf_transformation,[],[f20])).
% 0.20/0.54  fof(f20,plain,(
% 0.20/0.54    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.20/0.54    inference(ennf_transformation,[],[f1])).
% 0.20/0.54  fof(f1,axiom,(
% 0.20/0.54    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.20/0.54  fof(f82,plain,(
% 0.20/0.54    spl4_6 | ~spl4_1),
% 0.20/0.54    inference(avatar_split_clause,[],[f77,f53,f79])).
% 0.20/0.54  fof(f77,plain,(
% 0.20/0.54    l1_struct_0(sK0) | ~spl4_1),
% 0.20/0.54    inference(resolution,[],[f39,f55])).
% 0.20/0.54  fof(f39,plain,(
% 0.20/0.54    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f22])).
% 0.20/0.54  fof(f22,plain,(
% 0.20/0.54    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.20/0.54    inference(ennf_transformation,[],[f11])).
% 0.20/0.54  fof(f11,axiom,(
% 0.20/0.54    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.20/0.54  fof(f76,plain,(
% 0.20/0.54    spl4_5),
% 0.20/0.54    inference(avatar_split_clause,[],[f29,f73])).
% 0.20/0.54  fof(f29,plain,(
% 0.20/0.54    v1_xboole_0(sK1)),
% 0.20/0.54    inference(cnf_transformation,[],[f19])).
% 0.20/0.54  fof(f19,plain,(
% 0.20/0.54    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.20/0.54    inference(flattening,[],[f18])).
% 0.20/0.54  fof(f18,plain,(
% 0.20/0.54    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.20/0.54    inference(ennf_transformation,[],[f16])).
% 0.20/0.54  fof(f16,plain,(
% 0.20/0.54    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 0.20/0.54    inference(pure_predicate_removal,[],[f15])).
% 0.20/0.54  fof(f15,negated_conjecture,(
% 0.20/0.54    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 0.20/0.54    inference(negated_conjecture,[],[f14])).
% 0.20/0.54  fof(f14,conjecture,(
% 0.20/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tex_2)).
% 0.20/0.54  fof(f66,plain,(
% 0.20/0.54    ~spl4_3),
% 0.20/0.54    inference(avatar_split_clause,[],[f31,f63])).
% 0.20/0.54  fof(f31,plain,(
% 0.20/0.54    ~v2_tex_2(sK1,sK0)),
% 0.20/0.54    inference(cnf_transformation,[],[f19])).
% 0.20/0.54  fof(f61,plain,(
% 0.20/0.54    spl4_2),
% 0.20/0.54    inference(avatar_split_clause,[],[f32,f58])).
% 0.20/0.54  fof(f32,plain,(
% 0.20/0.54    v2_pre_topc(sK0)),
% 0.20/0.54    inference(cnf_transformation,[],[f19])).
% 0.20/0.54  fof(f56,plain,(
% 0.20/0.54    spl4_1),
% 0.20/0.54    inference(avatar_split_clause,[],[f33,f53])).
% 0.20/0.54  fof(f33,plain,(
% 0.20/0.54    l1_pre_topc(sK0)),
% 0.20/0.54    inference(cnf_transformation,[],[f19])).
% 0.20/0.54  % SZS output end Proof for theBenchmark
% 0.20/0.54  % (2910)------------------------------
% 0.20/0.54  % (2910)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (2910)Termination reason: Refutation
% 0.20/0.54  
% 0.20/0.54  % (2910)Memory used [KB]: 10874
% 0.20/0.54  % (2910)Time elapsed: 0.124 s
% 0.20/0.54  % (2910)------------------------------
% 0.20/0.54  % (2910)------------------------------
% 0.20/0.55  % (2893)Success in time 0.191 s
%------------------------------------------------------------------------------
