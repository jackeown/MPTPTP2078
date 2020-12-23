%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:21:23 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 205 expanded)
%              Number of leaves         :   28 (  96 expanded)
%              Depth                    :    9
%              Number of atoms          :  332 ( 929 expanded)
%              Number of equality atoms :   39 ( 129 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f229,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f57,f62,f67,f72,f77,f82,f87,f92,f109,f122,f123,f130,f194,f220,f225,f228])).

fof(f228,plain,
    ( ~ spl4_28
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_7
    | spl4_8
    | ~ spl4_11
    | spl4_27 ),
    inference(avatar_split_clause,[],[f226,f217,f114,f89,f84,f79,f74,f69,f222])).

fof(f222,plain,
    ( spl4_28
  <=> m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f69,plain,
    ( spl4_4
  <=> v2_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f74,plain,
    ( spl4_5
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f79,plain,
    ( spl4_6
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f84,plain,
    ( spl4_7
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f89,plain,
    ( spl4_8
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f114,plain,
    ( spl4_11
  <=> r1_tarski(k2_tarski(sK2,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f217,plain,
    ( spl4_27
  <=> k2_tarski(sK2,sK2) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k2_tarski(sK2,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f226,plain,
    ( ~ m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_7
    | spl4_8
    | ~ spl4_11
    | spl4_27 ),
    inference(unit_resulting_resolution,[],[f91,f86,f81,f71,f76,f219,f116,f41])).

fof(f41,plain,(
    ! [X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ r1_tarski(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ( sK3(X0,X1) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK3(X0,X1)))
                & r1_tarski(sK3(X0,X1),X1)
                & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3
                  | ~ r1_tarski(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f26,f27])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2
          & r1_tarski(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( sK3(X0,X1) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK3(X0,X1)))
        & r1_tarski(sK3(X0,X1),X1)
        & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ? [X2] :
                  ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2
                  & r1_tarski(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3
                  | ~ r1_tarski(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ? [X2] :
                  ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2
                  & r1_tarski(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2
                  | ~ r1_tarski(X2,X1)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f15])).

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
    inference(flattening,[],[f14])).

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

fof(f116,plain,
    ( r1_tarski(k2_tarski(sK2,sK2),sK1)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f114])).

fof(f219,plain,
    ( k2_tarski(sK2,sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k2_tarski(sK2,sK2)))
    | spl4_27 ),
    inference(avatar_component_clause,[],[f217])).

fof(f76,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f74])).

fof(f71,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f69])).

fof(f81,plain,
    ( l1_pre_topc(sK0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f79])).

fof(f86,plain,
    ( v2_pre_topc(sK0)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f84])).

fof(f91,plain,
    ( ~ v2_struct_0(sK0)
    | spl4_8 ),
    inference(avatar_component_clause,[],[f89])).

fof(f225,plain,
    ( spl4_13
    | ~ spl4_3
    | spl4_28
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f215,f156,f222,f64,f127])).

fof(f127,plain,
    ( spl4_13
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f64,plain,
    ( spl4_3
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f156,plain,
    ( spl4_18
  <=> k6_domain_1(u1_struct_0(sK0),sK2) = k2_tarski(sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f215,plain,
    ( m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl4_18 ),
    inference(superposition,[],[f47,f158])).

fof(f158,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK2) = k2_tarski(sK2,sK2)
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f156])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(f220,plain,
    ( ~ spl4_27
    | spl4_1
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f214,f156,f54,f217])).

fof(f54,plain,
    ( spl4_1
  <=> k6_domain_1(u1_struct_0(sK0),sK2) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f214,plain,
    ( k2_tarski(sK2,sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k2_tarski(sK2,sK2)))
    | spl4_1
    | ~ spl4_18 ),
    inference(backward_demodulation,[],[f56,f158])).

fof(f56,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f54])).

fof(f194,plain,
    ( spl4_18
    | ~ spl4_3
    | spl4_13 ),
    inference(avatar_split_clause,[],[f181,f127,f64,f156])).

fof(f181,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK2) = k2_tarski(sK2,sK2)
    | ~ spl4_3
    | spl4_13 ),
    inference(unit_resulting_resolution,[],[f66,f129,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k2_tarski(X1,X1)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f46,f39])).

fof(f39,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f46,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f129,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | spl4_13 ),
    inference(avatar_component_clause,[],[f127])).

fof(f66,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f64])).

fof(f130,plain,
    ( ~ spl4_13
    | ~ spl4_5
    | spl4_12 ),
    inference(avatar_split_clause,[],[f125,f119,f74,f127])).

fof(f119,plain,
    ( spl4_12
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f125,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl4_5
    | spl4_12 ),
    inference(unit_resulting_resolution,[],[f76,f121,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f121,plain,
    ( ~ v1_xboole_0(sK1)
    | spl4_12 ),
    inference(avatar_component_clause,[],[f119])).

fof(f123,plain,
    ( spl4_11
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f112,f106,f114])).

fof(f106,plain,
    ( spl4_10
  <=> m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f112,plain,
    ( r1_tarski(k2_tarski(sK2,sK2),sK1)
    | ~ spl4_10 ),
    inference(resolution,[],[f108,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f108,plain,
    ( m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(sK1))
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f106])).

fof(f122,plain,
    ( ~ spl4_12
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f110,f106,f119])).

fof(f110,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl4_10 ),
    inference(unit_resulting_resolution,[],[f50,f108,f40])).

fof(f50,plain,(
    ! [X0] : ~ v1_xboole_0(k2_tarski(X0,X0)) ),
    inference(definition_unfolding,[],[f38,f39])).

fof(f38,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).

fof(f109,plain,
    ( spl4_10
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f103,f59,f106])).

fof(f59,plain,
    ( spl4_2
  <=> r2_hidden(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f103,plain,
    ( m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(sK1))
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f61,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f45,f39])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

fof(f61,plain,
    ( r2_hidden(sK2,sK1)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f59])).

fof(f92,plain,(
    ~ spl4_8 ),
    inference(avatar_split_clause,[],[f30,f89])).

fof(f30,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
    & r2_hidden(sK2,sK1)
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & v2_tex_2(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f23,f22,f21])).

fof(f21,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
                & r2_hidden(X2,X1)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & v2_tex_2(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k6_domain_1(u1_struct_0(sK0),X2) != k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)))
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & v2_tex_2(X1,sK0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( k6_domain_1(u1_struct_0(sK0),X2) != k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)))
            & r2_hidden(X2,X1)
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        & v2_tex_2(X1,sK0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( k6_domain_1(u1_struct_0(sK0),X2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)))
          & r2_hidden(X2,sK1)
          & m1_subset_1(X2,u1_struct_0(sK0)) )
      & v2_tex_2(sK1,sK0)
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X2] :
        ( k6_domain_1(u1_struct_0(sK0),X2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)))
        & r2_hidden(X2,sK1)
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( k6_domain_1(u1_struct_0(sK0),sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
      & r2_hidden(sK2,sK1)
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

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

fof(f87,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f31,f84])).

fof(f31,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f82,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f32,f79])).

fof(f32,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f77,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f33,f74])).

fof(f33,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f24])).

fof(f72,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f34,f69])).

fof(f34,plain,(
    v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f67,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f35,f64])).

fof(f35,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f62,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f36,f59])).

fof(f36,plain,(
    r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f57,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f37,f54])).

fof(f37,plain,(
    k6_domain_1(u1_struct_0(sK0),sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:44:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.42  % (14261)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.46  % (14268)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.47  % (14259)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.47  % (14258)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.47  % (14259)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f229,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(avatar_sat_refutation,[],[f57,f62,f67,f72,f77,f82,f87,f92,f109,f122,f123,f130,f194,f220,f225,f228])).
% 0.20/0.47  fof(f228,plain,(
% 0.20/0.47    ~spl4_28 | ~spl4_4 | ~spl4_5 | ~spl4_6 | ~spl4_7 | spl4_8 | ~spl4_11 | spl4_27),
% 0.20/0.47    inference(avatar_split_clause,[],[f226,f217,f114,f89,f84,f79,f74,f69,f222])).
% 0.20/0.47  fof(f222,plain,(
% 0.20/0.47    spl4_28 <=> m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 0.20/0.47  fof(f69,plain,(
% 0.20/0.47    spl4_4 <=> v2_tex_2(sK1,sK0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.20/0.47  fof(f74,plain,(
% 0.20/0.47    spl4_5 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.20/0.47  fof(f79,plain,(
% 0.20/0.47    spl4_6 <=> l1_pre_topc(sK0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.20/0.47  fof(f84,plain,(
% 0.20/0.47    spl4_7 <=> v2_pre_topc(sK0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.20/0.47  fof(f89,plain,(
% 0.20/0.47    spl4_8 <=> v2_struct_0(sK0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.20/0.47  fof(f114,plain,(
% 0.20/0.47    spl4_11 <=> r1_tarski(k2_tarski(sK2,sK2),sK1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.20/0.47  fof(f217,plain,(
% 0.20/0.47    spl4_27 <=> k2_tarski(sK2,sK2) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k2_tarski(sK2,sK2)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).
% 0.20/0.47  fof(f226,plain,(
% 0.20/0.47    ~m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl4_4 | ~spl4_5 | ~spl4_6 | ~spl4_7 | spl4_8 | ~spl4_11 | spl4_27)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f91,f86,f81,f71,f76,f219,f116,f41])).
% 0.20/0.47  fof(f41,plain,(
% 0.20/0.47    ( ! [X0,X3,X1] : (~l1_pre_topc(X0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f28])).
% 0.20/0.47  fof(f28,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | (sK3(X0,X1) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK3(X0,X1))) & r1_tarski(sK3(X0,X1),X1) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f26,f27])).
% 0.20/0.47  fof(f27,plain,(
% 0.20/0.47    ! [X1,X0] : (? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (sK3(X0,X1) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK3(X0,X1))) & r1_tarski(sK3(X0,X1),X1) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f26,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.47    inference(rectify,[],[f25])).
% 0.20/0.47  fof(f25,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.47    inference(nnf_transformation,[],[f15])).
% 0.20/0.47  fof(f15,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.47    inference(flattening,[],[f14])).
% 0.20/0.47  fof(f14,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f8])).
% 0.20/0.47  fof(f8,axiom,(
% 0.20/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X2,X1) => k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2)))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_tex_2)).
% 0.20/0.47  fof(f116,plain,(
% 0.20/0.47    r1_tarski(k2_tarski(sK2,sK2),sK1) | ~spl4_11),
% 0.20/0.47    inference(avatar_component_clause,[],[f114])).
% 0.20/0.47  fof(f219,plain,(
% 0.20/0.47    k2_tarski(sK2,sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k2_tarski(sK2,sK2))) | spl4_27),
% 0.20/0.47    inference(avatar_component_clause,[],[f217])).
% 0.20/0.47  fof(f76,plain,(
% 0.20/0.47    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_5),
% 0.20/0.47    inference(avatar_component_clause,[],[f74])).
% 0.20/0.47  fof(f71,plain,(
% 0.20/0.47    v2_tex_2(sK1,sK0) | ~spl4_4),
% 0.20/0.47    inference(avatar_component_clause,[],[f69])).
% 0.20/0.47  fof(f81,plain,(
% 0.20/0.47    l1_pre_topc(sK0) | ~spl4_6),
% 0.20/0.47    inference(avatar_component_clause,[],[f79])).
% 0.20/0.47  fof(f86,plain,(
% 0.20/0.47    v2_pre_topc(sK0) | ~spl4_7),
% 0.20/0.47    inference(avatar_component_clause,[],[f84])).
% 0.20/0.47  fof(f91,plain,(
% 0.20/0.47    ~v2_struct_0(sK0) | spl4_8),
% 0.20/0.47    inference(avatar_component_clause,[],[f89])).
% 0.20/0.47  fof(f225,plain,(
% 0.20/0.47    spl4_13 | ~spl4_3 | spl4_28 | ~spl4_18),
% 0.20/0.47    inference(avatar_split_clause,[],[f215,f156,f222,f64,f127])).
% 0.20/0.47  fof(f127,plain,(
% 0.20/0.47    spl4_13 <=> v1_xboole_0(u1_struct_0(sK0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.20/0.47  fof(f64,plain,(
% 0.20/0.47    spl4_3 <=> m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.47  fof(f156,plain,(
% 0.20/0.47    spl4_18 <=> k6_domain_1(u1_struct_0(sK0),sK2) = k2_tarski(sK2,sK2)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.20/0.47  fof(f215,plain,(
% 0.20/0.47    m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0)) | ~spl4_18),
% 0.20/0.47    inference(superposition,[],[f47,f158])).
% 0.20/0.47  fof(f158,plain,(
% 0.20/0.47    k6_domain_1(u1_struct_0(sK0),sK2) = k2_tarski(sK2,sK2) | ~spl4_18),
% 0.20/0.47    inference(avatar_component_clause,[],[f156])).
% 0.20/0.47  fof(f47,plain,(
% 0.20/0.47    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f20])).
% 0.20/0.47  fof(f20,plain,(
% 0.20/0.47    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.20/0.47    inference(flattening,[],[f19])).
% 0.20/0.47  fof(f19,plain,(
% 0.20/0.47    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f6])).
% 0.20/0.47  fof(f6,axiom,(
% 0.20/0.47    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).
% 0.20/0.47  fof(f220,plain,(
% 0.20/0.47    ~spl4_27 | spl4_1 | ~spl4_18),
% 0.20/0.47    inference(avatar_split_clause,[],[f214,f156,f54,f217])).
% 0.20/0.47  fof(f54,plain,(
% 0.20/0.47    spl4_1 <=> k6_domain_1(u1_struct_0(sK0),sK2) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.47  fof(f214,plain,(
% 0.20/0.47    k2_tarski(sK2,sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k2_tarski(sK2,sK2))) | (spl4_1 | ~spl4_18)),
% 0.20/0.47    inference(backward_demodulation,[],[f56,f158])).
% 0.20/0.47  fof(f56,plain,(
% 0.20/0.47    k6_domain_1(u1_struct_0(sK0),sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) | spl4_1),
% 0.20/0.47    inference(avatar_component_clause,[],[f54])).
% 0.20/0.47  fof(f194,plain,(
% 0.20/0.47    spl4_18 | ~spl4_3 | spl4_13),
% 0.20/0.47    inference(avatar_split_clause,[],[f181,f127,f64,f156])).
% 0.20/0.47  fof(f181,plain,(
% 0.20/0.47    k6_domain_1(u1_struct_0(sK0),sK2) = k2_tarski(sK2,sK2) | (~spl4_3 | spl4_13)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f66,f129,f52])).
% 0.20/0.47  fof(f52,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k2_tarski(X1,X1) | v1_xboole_0(X0)) )),
% 0.20/0.47    inference(definition_unfolding,[],[f46,f39])).
% 0.20/0.47  fof(f39,plain,(
% 0.20/0.47    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f1])).
% 0.20/0.47  fof(f1,axiom,(
% 0.20/0.47    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.47  fof(f46,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f18])).
% 0.20/0.47  fof(f18,plain,(
% 0.20/0.47    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.20/0.47    inference(flattening,[],[f17])).
% 0.20/0.47  fof(f17,plain,(
% 0.20/0.47    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f7])).
% 0.20/0.47  fof(f7,axiom,(
% 0.20/0.47    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.20/0.47  fof(f129,plain,(
% 0.20/0.47    ~v1_xboole_0(u1_struct_0(sK0)) | spl4_13),
% 0.20/0.47    inference(avatar_component_clause,[],[f127])).
% 0.20/0.47  fof(f66,plain,(
% 0.20/0.47    m1_subset_1(sK2,u1_struct_0(sK0)) | ~spl4_3),
% 0.20/0.47    inference(avatar_component_clause,[],[f64])).
% 0.20/0.47  fof(f130,plain,(
% 0.20/0.47    ~spl4_13 | ~spl4_5 | spl4_12),
% 0.20/0.47    inference(avatar_split_clause,[],[f125,f119,f74,f127])).
% 0.20/0.47  fof(f119,plain,(
% 0.20/0.47    spl4_12 <=> v1_xboole_0(sK1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.20/0.47  fof(f125,plain,(
% 0.20/0.47    ~v1_xboole_0(u1_struct_0(sK0)) | (~spl4_5 | spl4_12)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f76,f121,f40])).
% 0.20/0.47  fof(f40,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f13])).
% 0.20/0.47  fof(f13,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f4])).
% 0.20/0.47  fof(f4,axiom,(
% 0.20/0.47    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).
% 0.20/0.47  fof(f121,plain,(
% 0.20/0.47    ~v1_xboole_0(sK1) | spl4_12),
% 0.20/0.47    inference(avatar_component_clause,[],[f119])).
% 0.20/0.47  fof(f123,plain,(
% 0.20/0.47    spl4_11 | ~spl4_10),
% 0.20/0.47    inference(avatar_split_clause,[],[f112,f106,f114])).
% 0.20/0.47  fof(f106,plain,(
% 0.20/0.47    spl4_10 <=> m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(sK1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.20/0.47  fof(f112,plain,(
% 0.20/0.47    r1_tarski(k2_tarski(sK2,sK2),sK1) | ~spl4_10),
% 0.20/0.47    inference(resolution,[],[f108,f48])).
% 0.20/0.47  fof(f48,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f29])).
% 0.20/0.47  fof(f29,plain,(
% 0.20/0.47    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.20/0.47    inference(nnf_transformation,[],[f5])).
% 0.20/0.47  fof(f5,axiom,(
% 0.20/0.47    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.47  fof(f108,plain,(
% 0.20/0.47    m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(sK1)) | ~spl4_10),
% 0.20/0.47    inference(avatar_component_clause,[],[f106])).
% 0.20/0.47  fof(f122,plain,(
% 0.20/0.47    ~spl4_12 | ~spl4_10),
% 0.20/0.47    inference(avatar_split_clause,[],[f110,f106,f119])).
% 0.20/0.47  fof(f110,plain,(
% 0.20/0.47    ~v1_xboole_0(sK1) | ~spl4_10),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f50,f108,f40])).
% 0.20/0.47  fof(f50,plain,(
% 0.20/0.47    ( ! [X0] : (~v1_xboole_0(k2_tarski(X0,X0))) )),
% 0.20/0.47    inference(definition_unfolding,[],[f38,f39])).
% 0.20/0.47  fof(f38,plain,(
% 0.20/0.47    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f2])).
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).
% 0.20/0.47  fof(f109,plain,(
% 0.20/0.47    spl4_10 | ~spl4_2),
% 0.20/0.47    inference(avatar_split_clause,[],[f103,f59,f106])).
% 0.20/0.47  fof(f59,plain,(
% 0.20/0.47    spl4_2 <=> r2_hidden(sK2,sK1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.47  fof(f103,plain,(
% 0.20/0.47    m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(sK1)) | ~spl4_2),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f61,f51])).
% 0.20/0.47  fof(f51,plain,(
% 0.20/0.47    ( ! [X0,X1] : (m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 0.20/0.47    inference(definition_unfolding,[],[f45,f39])).
% 0.20/0.47  fof(f45,plain,(
% 0.20/0.47    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f16])).
% 0.20/0.47  fof(f16,plain,(
% 0.20/0.47    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 0.20/0.47    inference(ennf_transformation,[],[f3])).
% 0.20/0.47  fof(f3,axiom,(
% 0.20/0.47    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).
% 0.20/0.47  fof(f61,plain,(
% 0.20/0.47    r2_hidden(sK2,sK1) | ~spl4_2),
% 0.20/0.47    inference(avatar_component_clause,[],[f59])).
% 0.20/0.47  fof(f92,plain,(
% 0.20/0.47    ~spl4_8),
% 0.20/0.47    inference(avatar_split_clause,[],[f30,f89])).
% 0.20/0.47  fof(f30,plain,(
% 0.20/0.47    ~v2_struct_0(sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f24])).
% 0.20/0.47  fof(f24,plain,(
% 0.20/0.47    ((k6_domain_1(u1_struct_0(sK0),sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) & r2_hidden(sK2,sK1) & m1_subset_1(sK2,u1_struct_0(sK0))) & v2_tex_2(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f23,f22,f21])).
% 0.20/0.47  fof(f21,plain,(
% 0.20/0.47    ? [X0] : (? [X1] : (? [X2] : (k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (k6_domain_1(u1_struct_0(sK0),X2) != k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(sK0))) & v2_tex_2(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f22,plain,(
% 0.20/0.47    ? [X1] : (? [X2] : (k6_domain_1(u1_struct_0(sK0),X2) != k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(sK0))) & v2_tex_2(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (k6_domain_1(u1_struct_0(sK0),X2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2))) & r2_hidden(X2,sK1) & m1_subset_1(X2,u1_struct_0(sK0))) & v2_tex_2(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f23,plain,(
% 0.20/0.47    ? [X2] : (k6_domain_1(u1_struct_0(sK0),X2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2))) & r2_hidden(X2,sK1) & m1_subset_1(X2,u1_struct_0(sK0))) => (k6_domain_1(u1_struct_0(sK0),sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) & r2_hidden(sK2,sK1) & m1_subset_1(sK2,u1_struct_0(sK0)))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f12,plain,(
% 0.20/0.47    ? [X0] : (? [X1] : (? [X2] : (k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.47    inference(flattening,[],[f11])).
% 0.20/0.47  fof(f11,plain,(
% 0.20/0.47    ? [X0] : (? [X1] : ((? [X2] : ((k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & r2_hidden(X2,X1)) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f10])).
% 0.20/0.47  fof(f10,negated_conjecture,(
% 0.20/0.47    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,X1) => k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))))))))),
% 0.20/0.47    inference(negated_conjecture,[],[f9])).
% 0.20/0.47  fof(f9,conjecture,(
% 0.20/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,X1) => k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))))))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_tex_2)).
% 0.20/0.47  fof(f87,plain,(
% 0.20/0.47    spl4_7),
% 0.20/0.47    inference(avatar_split_clause,[],[f31,f84])).
% 0.20/0.47  fof(f31,plain,(
% 0.20/0.47    v2_pre_topc(sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f24])).
% 0.20/0.47  fof(f82,plain,(
% 0.20/0.47    spl4_6),
% 0.20/0.47    inference(avatar_split_clause,[],[f32,f79])).
% 0.20/0.47  fof(f32,plain,(
% 0.20/0.47    l1_pre_topc(sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f24])).
% 0.20/0.47  fof(f77,plain,(
% 0.20/0.47    spl4_5),
% 0.20/0.47    inference(avatar_split_clause,[],[f33,f74])).
% 0.20/0.47  fof(f33,plain,(
% 0.20/0.47    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.47    inference(cnf_transformation,[],[f24])).
% 0.20/0.47  fof(f72,plain,(
% 0.20/0.47    spl4_4),
% 0.20/0.47    inference(avatar_split_clause,[],[f34,f69])).
% 0.20/0.47  fof(f34,plain,(
% 0.20/0.47    v2_tex_2(sK1,sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f24])).
% 0.20/0.47  fof(f67,plain,(
% 0.20/0.47    spl4_3),
% 0.20/0.47    inference(avatar_split_clause,[],[f35,f64])).
% 0.20/0.47  fof(f35,plain,(
% 0.20/0.47    m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.20/0.47    inference(cnf_transformation,[],[f24])).
% 0.20/0.47  fof(f62,plain,(
% 0.20/0.47    spl4_2),
% 0.20/0.47    inference(avatar_split_clause,[],[f36,f59])).
% 0.20/0.47  fof(f36,plain,(
% 0.20/0.47    r2_hidden(sK2,sK1)),
% 0.20/0.47    inference(cnf_transformation,[],[f24])).
% 0.20/0.47  fof(f57,plain,(
% 0.20/0.47    ~spl4_1),
% 0.20/0.47    inference(avatar_split_clause,[],[f37,f54])).
% 0.20/0.47  fof(f37,plain,(
% 0.20/0.47    k6_domain_1(u1_struct_0(sK0),sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))),
% 0.20/0.47    inference(cnf_transformation,[],[f24])).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (14259)------------------------------
% 0.20/0.47  % (14259)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (14259)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (14259)Memory used [KB]: 6268
% 0.20/0.47  % (14259)Time elapsed: 0.054 s
% 0.20/0.47  % (14259)------------------------------
% 0.20/0.47  % (14259)------------------------------
% 0.20/0.47  % (14252)Success in time 0.115 s
%------------------------------------------------------------------------------
