%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:56 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 142 expanded)
%              Number of leaves         :   13 (  37 expanded)
%              Depth                    :   16
%              Number of atoms          :  233 ( 671 expanded)
%              Number of equality atoms :   23 (  78 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f165,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f59,f74,f138,f141,f156,f163])).

fof(f163,plain,
    ( ~ spl6_5
    | ~ spl6_7
    | spl6_10 ),
    inference(avatar_contradiction_clause,[],[f157])).

fof(f157,plain,
    ( $false
    | ~ spl6_5
    | ~ spl6_7
    | spl6_10 ),
    inference(unit_resulting_resolution,[],[f132,f155,f90])).

fof(f90,plain,
    ( ! [X0] :
        ( r1_tarski(X0,u1_struct_0(sK0))
        | ~ r1_tarski(X0,sK1) )
    | ~ spl6_5 ),
    inference(duplicate_literal_removal,[],[f87])).

fof(f87,plain,
    ( ! [X0] :
        ( r1_tarski(X0,u1_struct_0(sK0))
        | ~ r1_tarski(X0,sK1)
        | r1_tarski(X0,u1_struct_0(sK0)) )
    | ~ spl6_5 ),
    inference(resolution,[],[f85,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f85,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK5(X0,u1_struct_0(sK0)),X1)
        | r1_tarski(X0,u1_struct_0(sK0))
        | ~ r1_tarski(X1,sK1) )
    | ~ spl6_5 ),
    inference(resolution,[],[f83,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f83,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK5(X0,u1_struct_0(sK0)),sK1)
        | r1_tarski(X0,u1_struct_0(sK0)) )
    | ~ spl6_5 ),
    inference(resolution,[],[f77,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f77,plain,
    ( ! [X0] :
        ( r2_hidden(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,sK1) )
    | ~ spl6_5 ),
    inference(resolution,[],[f73,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f73,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl6_5
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f155,plain,
    ( ~ r1_tarski(k1_enumset1(sK2,sK2,sK2),u1_struct_0(sK0))
    | spl6_10 ),
    inference(avatar_component_clause,[],[f153])).

fof(f153,plain,
    ( spl6_10
  <=> r1_tarski(k1_enumset1(sK2,sK2,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f132,plain,
    ( r1_tarski(k1_enumset1(sK2,sK2,sK2),sK1)
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f131])).

fof(f131,plain,
    ( spl6_7
  <=> r1_tarski(k1_enumset1(sK2,sK2,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f156,plain,
    ( ~ spl6_10
    | spl6_8 ),
    inference(avatar_split_clause,[],[f151,f135,f153])).

fof(f135,plain,
    ( spl6_8
  <=> m1_subset_1(k1_enumset1(sK2,sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f151,plain,
    ( ~ r1_tarski(k1_enumset1(sK2,sK2,sK2),u1_struct_0(sK0))
    | spl6_8 ),
    inference(resolution,[],[f137,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f137,plain,
    ( ~ m1_subset_1(k1_enumset1(sK2,sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl6_8 ),
    inference(avatar_component_clause,[],[f135])).

fof(f141,plain,
    ( ~ spl6_2
    | spl6_7 ),
    inference(avatar_contradiction_clause,[],[f139])).

fof(f139,plain,
    ( $false
    | ~ spl6_2
    | spl6_7 ),
    inference(unit_resulting_resolution,[],[f58,f133,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_enumset1(X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f41,f46])).

fof(f46,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f27,f35])).

fof(f35,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f27,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f133,plain,
    ( ~ r1_tarski(k1_enumset1(sK2,sK2,sK2),sK1)
    | spl6_7 ),
    inference(avatar_component_clause,[],[f131])).

fof(f58,plain,
    ( r2_hidden(sK2,sK1)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl6_2
  <=> r2_hidden(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f138,plain,
    ( ~ spl6_7
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f129,f135,f131])).

fof(f129,plain,
    ( ~ m1_subset_1(k1_enumset1(sK2,sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k1_enumset1(sK2,sK2,sK2),sK1) ),
    inference(equality_resolution,[],[f128])).

fof(f128,plain,(
    ! [X0] :
      ( k1_enumset1(sK2,sK2,sK2) != X0
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X0,sK1) ) ),
    inference(global_subsumption,[],[f26,f25,f24,f127])).

fof(f127,plain,(
    ! [X0] :
      ( k1_enumset1(sK2,sK2,sK2) != X0
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X0,sK1)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_tex_2(sK1,sK0) ) ),
    inference(duplicate_literal_removal,[],[f126])).

fof(f126,plain,(
    ! [X0] :
      ( k1_enumset1(sK2,sK2,sK2) != X0
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X0,sK1)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X0,sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_tex_2(sK1,sK0) ) ),
    inference(resolution,[],[f120,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(sK4(X0,X1,X2),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X2,X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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

fof(f120,plain,(
    ! [X0] :
      ( ~ v3_pre_topc(sK4(sK0,sK1,X0),sK0)
      | k1_enumset1(sK2,sK2,sK2) != X0
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X0,sK1) ) ),
    inference(global_subsumption,[],[f26,f25,f24,f119])).

fof(f119,plain,(
    ! [X0] :
      ( ~ v3_pre_topc(sK4(sK0,sK1,X0),sK0)
      | k1_enumset1(sK2,sK2,sK2) != X0
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X0,sK1)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_tex_2(sK1,sK0) ) ),
    inference(duplicate_literal_removal,[],[f117])).

fof(f117,plain,(
    ! [X0] :
      ( ~ v3_pre_topc(sK4(sK0,sK1,X0),sK0)
      | k1_enumset1(sK2,sK2,sK2) != X0
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X0,sK1)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X0,sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_tex_2(sK1,sK0) ) ),
    inference(resolution,[],[f94,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X2,X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f94,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK4(sK0,sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(sK4(sK0,sK1,X0),sK0)
      | k1_enumset1(sK2,sK2,sK2) != X0
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X0,sK1) ) ),
    inference(global_subsumption,[],[f26,f25,f24,f93])).

fof(f93,plain,(
    ! [X0] :
      ( k1_enumset1(sK2,sK2,sK2) != X0
      | ~ v3_pre_topc(sK4(sK0,sK1,X0),sK0)
      | ~ m1_subset_1(sK4(sK0,sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X0,sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_tex_2(sK1,sK0) ) ),
    inference(superposition,[],[f47,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(u1_struct_0(X0),X1,sK4(X0,X1,X2)) = X2
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X2,X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f47,plain,(
    ! [X3] :
      ( k9_subset_1(u1_struct_0(sK0),sK1,X3) != k1_enumset1(sK2,sK2,sK2)
      | ~ v3_pre_topc(X3,sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(definition_unfolding,[],[f21,f46])).

fof(f21,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X3,sK0)
      | k9_subset_1(u1_struct_0(sK0),sK1,X3) != k1_tarski(sK2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,X3) != k1_tarski(X2)
                  | ~ v3_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,X3) != k1_tarski(X2)
                  | ~ v3_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v2_tex_2(X1,X0)
             => ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ~ ( ! [X3] :
                          ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                         => ~ ( k9_subset_1(u1_struct_0(X0),X1,X3) = k1_tarski(X2)
                              & v3_pre_topc(X3,X0) ) )
                      & r2_hidden(X2,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tex_2(X1,X0)
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ~ ( k9_subset_1(u1_struct_0(X0),X1,X3) = k1_tarski(X2)
                            & v3_pre_topc(X3,X0) ) )
                    & r2_hidden(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_tex_2)).

fof(f24,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f14])).

fof(f25,plain,(
    v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f26,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f74,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f24,f71])).

fof(f59,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f23,f56])).

fof(f23,plain,(
    r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:49:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (11881)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.50  % (11881)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.51  % (11859)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  % (11874)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f165,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f59,f74,f138,f141,f156,f163])).
% 0.21/0.52  fof(f163,plain,(
% 0.21/0.52    ~spl6_5 | ~spl6_7 | spl6_10),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f157])).
% 0.21/0.52  fof(f157,plain,(
% 0.21/0.52    $false | (~spl6_5 | ~spl6_7 | spl6_10)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f132,f155,f90])).
% 0.21/0.52  fof(f90,plain,(
% 0.21/0.52    ( ! [X0] : (r1_tarski(X0,u1_struct_0(sK0)) | ~r1_tarski(X0,sK1)) ) | ~spl6_5),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f87])).
% 0.21/0.52  fof(f87,plain,(
% 0.21/0.52    ( ! [X0] : (r1_tarski(X0,u1_struct_0(sK0)) | ~r1_tarski(X0,sK1) | r1_tarski(X0,u1_struct_0(sK0))) ) | ~spl6_5),
% 0.21/0.52    inference(resolution,[],[f85,f39])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.52  fof(f85,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(sK5(X0,u1_struct_0(sK0)),X1) | r1_tarski(X0,u1_struct_0(sK0)) | ~r1_tarski(X1,sK1)) ) | ~spl6_5),
% 0.21/0.52    inference(resolution,[],[f83,f38])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  fof(f83,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_hidden(sK5(X0,u1_struct_0(sK0)),sK1) | r1_tarski(X0,u1_struct_0(sK0))) ) | ~spl6_5),
% 0.21/0.52    inference(resolution,[],[f77,f40])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  fof(f77,plain,(
% 0.21/0.52    ( ! [X0] : (r2_hidden(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,sK1)) ) | ~spl6_5),
% 0.21/0.52    inference(resolution,[],[f73,f37])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,axiom,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 0.21/0.52  fof(f73,plain,(
% 0.21/0.52    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl6_5),
% 0.21/0.52    inference(avatar_component_clause,[],[f71])).
% 0.21/0.52  fof(f71,plain,(
% 0.21/0.52    spl6_5 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.21/0.52  fof(f155,plain,(
% 0.21/0.52    ~r1_tarski(k1_enumset1(sK2,sK2,sK2),u1_struct_0(sK0)) | spl6_10),
% 0.21/0.52    inference(avatar_component_clause,[],[f153])).
% 0.21/0.52  fof(f153,plain,(
% 0.21/0.52    spl6_10 <=> r1_tarski(k1_enumset1(sK2,sK2,sK2),u1_struct_0(sK0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.21/0.52  fof(f132,plain,(
% 0.21/0.52    r1_tarski(k1_enumset1(sK2,sK2,sK2),sK1) | ~spl6_7),
% 0.21/0.52    inference(avatar_component_clause,[],[f131])).
% 0.21/0.52  fof(f131,plain,(
% 0.21/0.52    spl6_7 <=> r1_tarski(k1_enumset1(sK2,sK2,sK2),sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.21/0.52  fof(f156,plain,(
% 0.21/0.52    ~spl6_10 | spl6_8),
% 0.21/0.52    inference(avatar_split_clause,[],[f151,f135,f153])).
% 0.21/0.52  fof(f135,plain,(
% 0.21/0.52    spl6_8 <=> m1_subset_1(k1_enumset1(sK2,sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.21/0.52  fof(f151,plain,(
% 0.21/0.52    ~r1_tarski(k1_enumset1(sK2,sK2,sK2),u1_struct_0(sK0)) | spl6_8),
% 0.21/0.52    inference(resolution,[],[f137,f43])).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,axiom,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.52  fof(f137,plain,(
% 0.21/0.52    ~m1_subset_1(k1_enumset1(sK2,sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | spl6_8),
% 0.21/0.52    inference(avatar_component_clause,[],[f135])).
% 0.21/0.52  fof(f141,plain,(
% 0.21/0.52    ~spl6_2 | spl6_7),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f139])).
% 0.21/0.52  fof(f139,plain,(
% 0.21/0.52    $false | (~spl6_2 | spl6_7)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f58,f133,f49])).
% 0.21/0.52  fof(f49,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_tarski(k1_enumset1(X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f41,f46])).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f27,f35])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.21/0.52  fof(f133,plain,(
% 0.21/0.52    ~r1_tarski(k1_enumset1(sK2,sK2,sK2),sK1) | spl6_7),
% 0.21/0.52    inference(avatar_component_clause,[],[f131])).
% 0.21/0.52  fof(f58,plain,(
% 0.21/0.52    r2_hidden(sK2,sK1) | ~spl6_2),
% 0.21/0.52    inference(avatar_component_clause,[],[f56])).
% 0.21/0.52  fof(f56,plain,(
% 0.21/0.52    spl6_2 <=> r2_hidden(sK2,sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.21/0.52  fof(f138,plain,(
% 0.21/0.52    ~spl6_7 | ~spl6_8),
% 0.21/0.52    inference(avatar_split_clause,[],[f129,f135,f131])).
% 0.21/0.52  fof(f129,plain,(
% 0.21/0.52    ~m1_subset_1(k1_enumset1(sK2,sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(k1_enumset1(sK2,sK2,sK2),sK1)),
% 0.21/0.52    inference(equality_resolution,[],[f128])).
% 0.21/0.52  fof(f128,plain,(
% 0.21/0.52    ( ! [X0] : (k1_enumset1(sK2,sK2,sK2) != X0 | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,sK1)) )),
% 0.21/0.52    inference(global_subsumption,[],[f26,f25,f24,f127])).
% 0.21/0.52  fof(f127,plain,(
% 0.21/0.52    ( ! [X0] : (k1_enumset1(sK2,sK2,sK2) != X0 | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_tex_2(sK1,sK0)) )),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f126])).
% 0.21/0.52  fof(f126,plain,(
% 0.21/0.52    ( ! [X0] : (k1_enumset1(sK2,sK2,sK2) != X0 | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,sK1) | ~l1_pre_topc(sK0) | ~v2_tex_2(sK1,sK0)) )),
% 0.21/0.52    inference(resolution,[],[f120,f30])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (v3_pre_topc(sK4(X0,X1,X2),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X2,X1) | ~l1_pre_topc(X0) | ~v2_tex_2(X1,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(flattening,[],[f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((? [X3] : ((k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,axiom,(
% 0.21/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0))) & r1_tarski(X2,X1))))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tex_2)).
% 0.21/0.52  fof(f120,plain,(
% 0.21/0.52    ( ! [X0] : (~v3_pre_topc(sK4(sK0,sK1,X0),sK0) | k1_enumset1(sK2,sK2,sK2) != X0 | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,sK1)) )),
% 0.21/0.52    inference(global_subsumption,[],[f26,f25,f24,f119])).
% 0.21/0.52  fof(f119,plain,(
% 0.21/0.52    ( ! [X0] : (~v3_pre_topc(sK4(sK0,sK1,X0),sK0) | k1_enumset1(sK2,sK2,sK2) != X0 | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_tex_2(sK1,sK0)) )),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f117])).
% 0.21/0.52  fof(f117,plain,(
% 0.21/0.52    ( ! [X0] : (~v3_pre_topc(sK4(sK0,sK1,X0),sK0) | k1_enumset1(sK2,sK2,sK2) != X0 | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,sK1) | ~l1_pre_topc(sK0) | ~v2_tex_2(sK1,sK0)) )),
% 0.21/0.52    inference(resolution,[],[f94,f29])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X2,X1) | ~l1_pre_topc(X0) | ~v2_tex_2(X1,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f16])).
% 0.21/0.52  fof(f94,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_subset_1(sK4(sK0,sK1,X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(sK4(sK0,sK1,X0),sK0) | k1_enumset1(sK2,sK2,sK2) != X0 | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,sK1)) )),
% 0.21/0.52    inference(global_subsumption,[],[f26,f25,f24,f93])).
% 0.21/0.52  fof(f93,plain,(
% 0.21/0.52    ( ! [X0] : (k1_enumset1(sK2,sK2,sK2) != X0 | ~v3_pre_topc(sK4(sK0,sK1,X0),sK0) | ~m1_subset_1(sK4(sK0,sK1,X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,sK1) | ~l1_pre_topc(sK0) | ~v2_tex_2(sK1,sK0)) )),
% 0.21/0.52    inference(superposition,[],[f47,f31])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k9_subset_1(u1_struct_0(X0),X1,sK4(X0,X1,X2)) = X2 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X2,X1) | ~l1_pre_topc(X0) | ~v2_tex_2(X1,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f16])).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    ( ! [X3] : (k9_subset_1(u1_struct_0(sK0),sK1,X3) != k1_enumset1(sK2,sK2,sK2) | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.21/0.52    inference(definition_unfolding,[],[f21,f46])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X3,sK0) | k9_subset_1(u1_struct_0(sK0),sK1,X3) != k1_tarski(sK2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != k1_tarski(X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.21/0.52    inference(flattening,[],[f13])).
% 0.21/0.52  fof(f13,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : ((? [X2] : ((! [X3] : ((k9_subset_1(u1_struct_0(X0),X1,X3) != k1_tarski(X2) | ~v3_pre_topc(X3,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1)) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f12])).
% 0.21/0.52  fof(f12,negated_conjecture,(
% 0.21/0.52    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = k1_tarski(X2) & v3_pre_topc(X3,X0))) & r2_hidden(X2,X1))))))),
% 0.21/0.52    inference(negated_conjecture,[],[f11])).
% 0.21/0.52  fof(f11,conjecture,(
% 0.21/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = k1_tarski(X2) & v3_pre_topc(X3,X0))) & r2_hidden(X2,X1))))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_tex_2)).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.52    inference(cnf_transformation,[],[f14])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    v2_tex_2(sK1,sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f14])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    l1_pre_topc(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f14])).
% 0.21/0.52  fof(f74,plain,(
% 0.21/0.52    spl6_5),
% 0.21/0.52    inference(avatar_split_clause,[],[f24,f71])).
% 0.21/0.52  fof(f59,plain,(
% 0.21/0.52    spl6_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f23,f56])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    r2_hidden(sK2,sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f14])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (11881)------------------------------
% 0.21/0.52  % (11881)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (11881)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (11881)Memory used [KB]: 10874
% 0.21/0.52  % (11881)Time elapsed: 0.100 s
% 0.21/0.52  % (11881)------------------------------
% 0.21/0.52  % (11881)------------------------------
% 0.21/0.52  % (11858)Success in time 0.162 s
%------------------------------------------------------------------------------
