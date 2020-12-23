%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:21:21 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 166 expanded)
%              Number of leaves         :   24 (  66 expanded)
%              Depth                    :    8
%              Number of atoms          :  268 ( 591 expanded)
%              Number of equality atoms :   16 (  50 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f225,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f51,f56,f61,f66,f71,f76,f82,f87,f95,f100,f106,f162,f169,f172,f208,f213,f224])).

fof(f224,plain,
    ( ~ spl6_25
    | spl6_26 ),
    inference(avatar_contradiction_clause,[],[f222])).

fof(f222,plain,
    ( $false
    | ~ spl6_25
    | spl6_26 ),
    inference(unit_resulting_resolution,[],[f207,f212,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f212,plain,
    ( ~ m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl6_26 ),
    inference(avatar_component_clause,[],[f210])).

fof(f210,plain,
    ( spl6_26
  <=> m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f207,plain,
    ( r1_tarski(k1_tarski(sK2),u1_struct_0(sK0))
    | ~ spl6_25 ),
    inference(avatar_component_clause,[],[f205])).

fof(f205,plain,
    ( spl6_25
  <=> r1_tarski(k1_tarski(sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f213,plain,
    ( spl6_11
    | ~ spl6_6
    | ~ spl6_26
    | spl6_20 ),
    inference(avatar_split_clause,[],[f180,f159,f210,f73,f103])).

fof(f103,plain,
    ( spl6_11
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f73,plain,
    ( spl6_6
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f159,plain,
    ( spl6_20
  <=> m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f180,plain,
    ( ~ m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | spl6_20 ),
    inference(superposition,[],[f161,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f161,plain,
    ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl6_20 ),
    inference(avatar_component_clause,[],[f159])).

fof(f208,plain,
    ( spl6_25
    | ~ spl6_9
    | ~ spl6_21 ),
    inference(avatar_split_clause,[],[f203,f166,f92,f205])).

fof(f92,plain,
    ( spl6_9
  <=> r1_tarski(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f166,plain,
    ( spl6_21
  <=> r1_tarski(k1_tarski(sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f203,plain,
    ( r1_tarski(k1_tarski(sK2),u1_struct_0(sK0))
    | ~ spl6_9
    | ~ spl6_21 ),
    inference(duplicate_literal_removal,[],[f199])).

fof(f199,plain,
    ( r1_tarski(k1_tarski(sK2),u1_struct_0(sK0))
    | r1_tarski(k1_tarski(sK2),u1_struct_0(sK0))
    | ~ spl6_9
    | ~ spl6_21 ),
    inference(resolution,[],[f178,f108])).

fof(f108,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK5(X1,u1_struct_0(sK0)),sK1)
        | r1_tarski(X1,u1_struct_0(sK0)) )
    | ~ spl6_9 ),
    inference(resolution,[],[f101,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f101,plain,
    ( ! [X0] :
        ( r2_hidden(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,sK1) )
    | ~ spl6_9 ),
    inference(resolution,[],[f94,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f94,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f92])).

fof(f178,plain,
    ( ! [X0] :
        ( r2_hidden(sK5(k1_tarski(sK2),X0),sK1)
        | r1_tarski(k1_tarski(sK2),X0) )
    | ~ spl6_21 ),
    inference(resolution,[],[f174,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f174,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_tarski(sK2))
        | r2_hidden(X0,sK1) )
    | ~ spl6_21 ),
    inference(resolution,[],[f167,f38])).

fof(f167,plain,
    ( r1_tarski(k1_tarski(sK2),sK1)
    | ~ spl6_21 ),
    inference(avatar_component_clause,[],[f166])).

fof(f172,plain,
    ( ~ spl6_4
    | spl6_21 ),
    inference(avatar_contradiction_clause,[],[f170])).

fof(f170,plain,
    ( $false
    | ~ spl6_4
    | spl6_21 ),
    inference(unit_resulting_resolution,[],[f65,f168,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f168,plain,
    ( ~ r1_tarski(k1_tarski(sK2),sK1)
    | spl6_21 ),
    inference(avatar_component_clause,[],[f166])).

fof(f65,plain,
    ( r2_hidden(sK2,sK1)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl6_4
  <=> r2_hidden(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f169,plain,
    ( spl6_11
    | ~ spl6_6
    | ~ spl6_21
    | spl6_19 ),
    inference(avatar_split_clause,[],[f163,f155,f166,f73,f103])).

fof(f155,plain,
    ( spl6_19
  <=> r1_tarski(k6_domain_1(u1_struct_0(sK0),sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f163,plain,
    ( ~ r1_tarski(k1_tarski(sK2),sK1)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | spl6_19 ),
    inference(superposition,[],[f157,f37])).

fof(f157,plain,
    ( ~ r1_tarski(k6_domain_1(u1_struct_0(sK0),sK2),sK1)
    | spl6_19 ),
    inference(avatar_component_clause,[],[f155])).

fof(f162,plain,
    ( ~ spl6_5
    | spl6_1
    | ~ spl6_19
    | ~ spl6_20
    | ~ spl6_8
    | ~ spl6_3
    | ~ spl6_2
    | spl6_10 ),
    inference(avatar_split_clause,[],[f114,f97,f53,f58,f84,f159,f155,f48,f68])).

fof(f68,plain,
    ( spl6_5
  <=> v2_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f48,plain,
    ( spl6_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f84,plain,
    ( spl6_8
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f58,plain,
    ( spl6_3
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f53,plain,
    ( spl6_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f97,plain,
    ( spl6_10
  <=> k6_domain_1(u1_struct_0(sK0),sK2) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f114,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k6_domain_1(u1_struct_0(sK0),sK2),sK1)
    | v2_struct_0(sK0)
    | ~ v2_tex_2(sK1,sK0)
    | spl6_10 ),
    inference(trivial_inequality_removal,[],[f112])).

fof(f112,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK2) != k6_domain_1(u1_struct_0(sK0),sK2)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k6_domain_1(u1_struct_0(sK0),sK2),sK1)
    | v2_struct_0(sK0)
    | ~ v2_tex_2(sK1,sK0)
    | spl6_10 ),
    inference(superposition,[],[f99,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X2,X1)
      | v2_struct_0(X0)
      | ~ v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_tex_2)).

fof(f99,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
    | spl6_10 ),
    inference(avatar_component_clause,[],[f97])).

fof(f106,plain,
    ( spl6_7
    | ~ spl6_11
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f90,f84,f103,f79])).

fof(f79,plain,
    ( spl6_7
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f90,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(sK1)
    | ~ spl6_8 ),
    inference(resolution,[],[f86,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f86,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f84])).

fof(f100,plain,(
    ~ spl6_10 ),
    inference(avatar_split_clause,[],[f24,f97])).

fof(f24,plain,(
    k6_domain_1(u1_struct_0(sK0),sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

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
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
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
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_tex_2)).

fof(f95,plain,
    ( spl6_9
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f89,f84,f92])).

fof(f89,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl6_8 ),
    inference(resolution,[],[f86,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f87,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f25,f84])).

fof(f25,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f13])).

fof(f82,plain,
    ( ~ spl6_7
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f77,f63,f79])).

fof(f77,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl6_4 ),
    inference(resolution,[],[f65,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f76,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f22,f73])).

fof(f22,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f71,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f26,f68])).

fof(f26,plain,(
    v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f66,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f23,f63])).

fof(f23,plain,(
    r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f61,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f29,f58])).

fof(f29,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f56,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f28,f53])).

fof(f28,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f51,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f27,f48])).

fof(f27,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:29:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (9254)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.50  % (9262)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.50  % (9251)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.51  % (9245)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.51  % (9253)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.51  % (9252)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.51  % (9245)Refutation not found, incomplete strategy% (9245)------------------------------
% 0.20/0.51  % (9245)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (9245)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (9245)Memory used [KB]: 10746
% 0.20/0.51  % (9245)Time elapsed: 0.106 s
% 0.20/0.51  % (9245)------------------------------
% 0.20/0.51  % (9245)------------------------------
% 0.20/0.51  % (9244)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.51  % (9263)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.52  % (9270)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.52  % (9255)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  % (9265)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.52  % (9248)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.52  % (9265)Refutation found. Thanks to Tanya!
% 0.20/0.52  % SZS status Theorem for theBenchmark
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f225,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(avatar_sat_refutation,[],[f51,f56,f61,f66,f71,f76,f82,f87,f95,f100,f106,f162,f169,f172,f208,f213,f224])).
% 0.20/0.52  fof(f224,plain,(
% 0.20/0.52    ~spl6_25 | spl6_26),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f222])).
% 0.20/0.52  fof(f222,plain,(
% 0.20/0.52    $false | (~spl6_25 | spl6_26)),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f207,f212,f43])).
% 0.20/0.52  fof(f43,plain,(
% 0.20/0.52    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f7])).
% 0.20/0.52  fof(f7,axiom,(
% 0.20/0.52    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.52  fof(f212,plain,(
% 0.20/0.52    ~m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK0))) | spl6_26),
% 0.20/0.52    inference(avatar_component_clause,[],[f210])).
% 0.20/0.52  fof(f210,plain,(
% 0.20/0.52    spl6_26 <=> m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).
% 0.20/0.52  fof(f207,plain,(
% 0.20/0.52    r1_tarski(k1_tarski(sK2),u1_struct_0(sK0)) | ~spl6_25),
% 0.20/0.52    inference(avatar_component_clause,[],[f205])).
% 0.20/0.52  fof(f205,plain,(
% 0.20/0.52    spl6_25 <=> r1_tarski(k1_tarski(sK2),u1_struct_0(sK0))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).
% 0.20/0.52  fof(f213,plain,(
% 0.20/0.52    spl6_11 | ~spl6_6 | ~spl6_26 | spl6_20),
% 0.20/0.52    inference(avatar_split_clause,[],[f180,f159,f210,f73,f103])).
% 0.20/0.52  fof(f103,plain,(
% 0.20/0.52    spl6_11 <=> v1_xboole_0(u1_struct_0(sK0))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.20/0.52  fof(f73,plain,(
% 0.20/0.52    spl6_6 <=> m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.20/0.52  fof(f159,plain,(
% 0.20/0.52    spl6_20 <=> m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).
% 0.20/0.52  fof(f180,plain,(
% 0.20/0.52    ~m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0)) | spl6_20),
% 0.20/0.52    inference(superposition,[],[f161,f37])).
% 0.20/0.52  fof(f37,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f18])).
% 0.20/0.52  fof(f18,plain,(
% 0.20/0.52    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.20/0.52    inference(flattening,[],[f17])).
% 0.20/0.52  fof(f17,plain,(
% 0.20/0.52    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f8])).
% 0.20/0.52  fof(f8,axiom,(
% 0.20/0.52    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.20/0.52  fof(f161,plain,(
% 0.20/0.52    ~m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0))) | spl6_20),
% 0.20/0.52    inference(avatar_component_clause,[],[f159])).
% 0.20/0.52  fof(f208,plain,(
% 0.20/0.52    spl6_25 | ~spl6_9 | ~spl6_21),
% 0.20/0.52    inference(avatar_split_clause,[],[f203,f166,f92,f205])).
% 0.20/0.52  fof(f92,plain,(
% 0.20/0.52    spl6_9 <=> r1_tarski(sK1,u1_struct_0(sK0))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.20/0.52  fof(f166,plain,(
% 0.20/0.52    spl6_21 <=> r1_tarski(k1_tarski(sK2),sK1)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).
% 0.20/0.52  fof(f203,plain,(
% 0.20/0.52    r1_tarski(k1_tarski(sK2),u1_struct_0(sK0)) | (~spl6_9 | ~spl6_21)),
% 0.20/0.52    inference(duplicate_literal_removal,[],[f199])).
% 0.20/0.52  fof(f199,plain,(
% 0.20/0.52    r1_tarski(k1_tarski(sK2),u1_struct_0(sK0)) | r1_tarski(k1_tarski(sK2),u1_struct_0(sK0)) | (~spl6_9 | ~spl6_21)),
% 0.20/0.52    inference(resolution,[],[f178,f108])).
% 0.20/0.52  fof(f108,plain,(
% 0.20/0.52    ( ! [X1] : (~r2_hidden(sK5(X1,u1_struct_0(sK0)),sK1) | r1_tarski(X1,u1_struct_0(sK0))) ) | ~spl6_9),
% 0.20/0.52    inference(resolution,[],[f101,f40])).
% 0.20/0.52  fof(f40,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f19])).
% 0.20/0.52  fof(f19,plain,(
% 0.20/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f2])).
% 0.20/0.52  fof(f2,axiom,(
% 0.20/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.52  fof(f101,plain,(
% 0.20/0.52    ( ! [X0] : (r2_hidden(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,sK1)) ) | ~spl6_9),
% 0.20/0.52    inference(resolution,[],[f94,f38])).
% 0.20/0.52  fof(f38,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f19])).
% 0.20/0.52  fof(f94,plain,(
% 0.20/0.52    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl6_9),
% 0.20/0.52    inference(avatar_component_clause,[],[f92])).
% 0.20/0.52  fof(f178,plain,(
% 0.20/0.52    ( ! [X0] : (r2_hidden(sK5(k1_tarski(sK2),X0),sK1) | r1_tarski(k1_tarski(sK2),X0)) ) | ~spl6_21),
% 0.20/0.52    inference(resolution,[],[f174,f39])).
% 0.20/0.52  fof(f39,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f19])).
% 0.20/0.52  fof(f174,plain,(
% 0.20/0.52    ( ! [X0] : (~r2_hidden(X0,k1_tarski(sK2)) | r2_hidden(X0,sK1)) ) | ~spl6_21),
% 0.20/0.52    inference(resolution,[],[f167,f38])).
% 0.20/0.52  fof(f167,plain,(
% 0.20/0.52    r1_tarski(k1_tarski(sK2),sK1) | ~spl6_21),
% 0.20/0.52    inference(avatar_component_clause,[],[f166])).
% 0.20/0.52  fof(f172,plain,(
% 0.20/0.52    ~spl6_4 | spl6_21),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f170])).
% 0.20/0.52  fof(f170,plain,(
% 0.20/0.52    $false | (~spl6_4 | spl6_21)),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f65,f168,f41])).
% 0.20/0.52  fof(f41,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f3])).
% 0.20/0.52  fof(f3,axiom,(
% 0.20/0.52    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.20/0.52  fof(f168,plain,(
% 0.20/0.52    ~r1_tarski(k1_tarski(sK2),sK1) | spl6_21),
% 0.20/0.52    inference(avatar_component_clause,[],[f166])).
% 0.20/0.52  fof(f65,plain,(
% 0.20/0.52    r2_hidden(sK2,sK1) | ~spl6_4),
% 0.20/0.52    inference(avatar_component_clause,[],[f63])).
% 0.20/0.52  fof(f63,plain,(
% 0.20/0.52    spl6_4 <=> r2_hidden(sK2,sK1)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.20/0.52  fof(f169,plain,(
% 0.20/0.52    spl6_11 | ~spl6_6 | ~spl6_21 | spl6_19),
% 0.20/0.52    inference(avatar_split_clause,[],[f163,f155,f166,f73,f103])).
% 0.20/0.52  fof(f155,plain,(
% 0.20/0.52    spl6_19 <=> r1_tarski(k6_domain_1(u1_struct_0(sK0),sK2),sK1)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).
% 0.20/0.52  fof(f163,plain,(
% 0.20/0.52    ~r1_tarski(k1_tarski(sK2),sK1) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0)) | spl6_19),
% 0.20/0.52    inference(superposition,[],[f157,f37])).
% 0.20/0.52  fof(f157,plain,(
% 0.20/0.52    ~r1_tarski(k6_domain_1(u1_struct_0(sK0),sK2),sK1) | spl6_19),
% 0.20/0.52    inference(avatar_component_clause,[],[f155])).
% 0.20/0.52  fof(f162,plain,(
% 0.20/0.52    ~spl6_5 | spl6_1 | ~spl6_19 | ~spl6_20 | ~spl6_8 | ~spl6_3 | ~spl6_2 | spl6_10),
% 0.20/0.52    inference(avatar_split_clause,[],[f114,f97,f53,f58,f84,f159,f155,f48,f68])).
% 0.20/0.52  fof(f68,plain,(
% 0.20/0.52    spl6_5 <=> v2_tex_2(sK1,sK0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.20/0.52  fof(f48,plain,(
% 0.20/0.52    spl6_1 <=> v2_struct_0(sK0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.20/0.52  fof(f84,plain,(
% 0.20/0.52    spl6_8 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.20/0.52  fof(f58,plain,(
% 0.20/0.52    spl6_3 <=> l1_pre_topc(sK0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.20/0.53  fof(f53,plain,(
% 0.20/0.53    spl6_2 <=> v2_pre_topc(sK0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.20/0.53  fof(f97,plain,(
% 0.20/0.53    spl6_10 <=> k6_domain_1(u1_struct_0(sK0),sK2) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.20/0.53  fof(f114,plain,(
% 0.20/0.53    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(k6_domain_1(u1_struct_0(sK0),sK2),sK1) | v2_struct_0(sK0) | ~v2_tex_2(sK1,sK0) | spl6_10),
% 0.20/0.53    inference(trivial_inequality_removal,[],[f112])).
% 0.20/0.53  fof(f112,plain,(
% 0.20/0.53    k6_domain_1(u1_struct_0(sK0),sK2) != k6_domain_1(u1_struct_0(sK0),sK2) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(k6_domain_1(u1_struct_0(sK0),sK2),sK1) | v2_struct_0(sK0) | ~v2_tex_2(sK1,sK0) | spl6_10),
% 0.20/0.53    inference(superposition,[],[f99,f31])).
% 0.20/0.53  fof(f31,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X2,X1) | v2_struct_0(X0) | ~v2_tex_2(X1,X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f16])).
% 0.20/0.53  fof(f16,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.53    inference(flattening,[],[f15])).
% 0.20/0.53  fof(f15,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f9])).
% 0.20/0.53  fof(f9,axiom,(
% 0.20/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X2,X1) => k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2)))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_tex_2)).
% 0.20/0.53  fof(f99,plain,(
% 0.20/0.53    k6_domain_1(u1_struct_0(sK0),sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) | spl6_10),
% 0.20/0.53    inference(avatar_component_clause,[],[f97])).
% 0.20/0.53  fof(f106,plain,(
% 0.20/0.53    spl6_7 | ~spl6_11 | ~spl6_8),
% 0.20/0.53    inference(avatar_split_clause,[],[f90,f84,f103,f79])).
% 0.20/0.53  fof(f79,plain,(
% 0.20/0.53    spl6_7 <=> v1_xboole_0(sK1)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.20/0.53  fof(f90,plain,(
% 0.20/0.53    ~v1_xboole_0(u1_struct_0(sK0)) | v1_xboole_0(sK1) | ~spl6_8),
% 0.20/0.53    inference(resolution,[],[f86,f30])).
% 0.20/0.53  fof(f30,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0) | v1_xboole_0(X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f14])).
% 0.20/0.53  fof(f14,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f6])).
% 0.20/0.53  fof(f6,axiom,(
% 0.20/0.53    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).
% 0.20/0.53  fof(f86,plain,(
% 0.20/0.53    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl6_8),
% 0.20/0.53    inference(avatar_component_clause,[],[f84])).
% 0.20/0.53  fof(f100,plain,(
% 0.20/0.53    ~spl6_10),
% 0.20/0.53    inference(avatar_split_clause,[],[f24,f97])).
% 0.20/0.53  fof(f24,plain,(
% 0.20/0.53    k6_domain_1(u1_struct_0(sK0),sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))),
% 0.20/0.53    inference(cnf_transformation,[],[f13])).
% 0.20/0.53  fof(f13,plain,(
% 0.20/0.53    ? [X0] : (? [X1] : (? [X2] : (k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.53    inference(flattening,[],[f12])).
% 0.20/0.53  fof(f12,plain,(
% 0.20/0.53    ? [X0] : (? [X1] : ((? [X2] : ((k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & r2_hidden(X2,X1)) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f11])).
% 0.20/0.53  fof(f11,negated_conjecture,(
% 0.20/0.53    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,X1) => k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))))))))),
% 0.20/0.53    inference(negated_conjecture,[],[f10])).
% 0.20/0.53  fof(f10,conjecture,(
% 0.20/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,X1) => k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))))))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_tex_2)).
% 0.20/0.53  fof(f95,plain,(
% 0.20/0.53    spl6_9 | ~spl6_8),
% 0.20/0.53    inference(avatar_split_clause,[],[f89,f84,f92])).
% 0.20/0.53  fof(f89,plain,(
% 0.20/0.53    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl6_8),
% 0.20/0.53    inference(resolution,[],[f86,f44])).
% 0.20/0.53  fof(f44,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f7])).
% 0.20/0.53  fof(f87,plain,(
% 0.20/0.53    spl6_8),
% 0.20/0.53    inference(avatar_split_clause,[],[f25,f84])).
% 0.20/0.53  fof(f25,plain,(
% 0.20/0.53    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.53    inference(cnf_transformation,[],[f13])).
% 0.20/0.53  fof(f82,plain,(
% 0.20/0.53    ~spl6_7 | ~spl6_4),
% 0.20/0.53    inference(avatar_split_clause,[],[f77,f63,f79])).
% 0.20/0.53  fof(f77,plain,(
% 0.20/0.53    ~v1_xboole_0(sK1) | ~spl6_4),
% 0.20/0.53    inference(resolution,[],[f65,f36])).
% 0.20/0.53  fof(f36,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f1])).
% 0.20/0.53  fof(f1,axiom,(
% 0.20/0.53    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.20/0.53  fof(f76,plain,(
% 0.20/0.53    spl6_6),
% 0.20/0.53    inference(avatar_split_clause,[],[f22,f73])).
% 0.20/0.53  fof(f22,plain,(
% 0.20/0.53    m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.20/0.53    inference(cnf_transformation,[],[f13])).
% 0.20/0.53  fof(f71,plain,(
% 0.20/0.53    spl6_5),
% 0.20/0.53    inference(avatar_split_clause,[],[f26,f68])).
% 0.20/0.53  fof(f26,plain,(
% 0.20/0.53    v2_tex_2(sK1,sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f13])).
% 0.20/0.53  fof(f66,plain,(
% 0.20/0.53    spl6_4),
% 0.20/0.53    inference(avatar_split_clause,[],[f23,f63])).
% 0.20/0.53  fof(f23,plain,(
% 0.20/0.53    r2_hidden(sK2,sK1)),
% 0.20/0.53    inference(cnf_transformation,[],[f13])).
% 0.20/0.53  fof(f61,plain,(
% 0.20/0.53    spl6_3),
% 0.20/0.53    inference(avatar_split_clause,[],[f29,f58])).
% 0.20/0.53  fof(f29,plain,(
% 0.20/0.53    l1_pre_topc(sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f13])).
% 0.20/0.53  fof(f56,plain,(
% 0.20/0.53    spl6_2),
% 0.20/0.53    inference(avatar_split_clause,[],[f28,f53])).
% 0.20/0.53  fof(f28,plain,(
% 0.20/0.53    v2_pre_topc(sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f13])).
% 0.20/0.53  fof(f51,plain,(
% 0.20/0.53    ~spl6_1),
% 0.20/0.53    inference(avatar_split_clause,[],[f27,f48])).
% 0.20/0.53  fof(f27,plain,(
% 0.20/0.53    ~v2_struct_0(sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f13])).
% 0.20/0.53  % SZS output end Proof for theBenchmark
% 0.20/0.53  % (9265)------------------------------
% 0.20/0.53  % (9265)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (9265)Termination reason: Refutation
% 0.20/0.53  
% 0.20/0.53  % (9265)Memory used [KB]: 10874
% 0.20/0.53  % (9265)Time elapsed: 0.086 s
% 0.20/0.53  % (9265)------------------------------
% 0.20/0.53  % (9265)------------------------------
% 0.20/0.53  % (9242)Success in time 0.174 s
%------------------------------------------------------------------------------
