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
% DateTime   : Thu Dec  3 13:20:58 EST 2020

% Result     : Theorem 1.22s
% Output     : Refutation 1.22s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 169 expanded)
%              Number of leaves         :   18 (  52 expanded)
%              Depth                    :   16
%              Number of atoms          :  249 ( 737 expanded)
%              Number of equality atoms :   23 (  87 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f142,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f52,f62,f68,f73,f88,f93,f128,f131,f138,f141])).

fof(f141,plain,
    ( ~ spl6_9
    | spl6_15 ),
    inference(avatar_contradiction_clause,[],[f139])).

fof(f139,plain,
    ( $false
    | ~ spl6_9
    | spl6_15 ),
    inference(unit_resulting_resolution,[],[f92,f137,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_enumset1(X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f32,f37])).

fof(f37,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f23,f30])).

% (28181)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
fof(f30,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f23,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f137,plain,
    ( ~ r1_tarski(k1_enumset1(sK2,sK2,sK2),u1_struct_0(sK0))
    | spl6_15 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl6_15
  <=> r1_tarski(k1_enumset1(sK2,sK2,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f92,plain,
    ( r2_hidden(sK2,u1_struct_0(sK0))
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl6_9
  <=> r2_hidden(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f138,plain,
    ( ~ spl6_15
    | spl6_14 ),
    inference(avatar_split_clause,[],[f133,f125,f135])).

fof(f125,plain,
    ( spl6_14
  <=> m1_subset_1(k1_enumset1(sK2,sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f133,plain,
    ( ~ r1_tarski(k1_enumset1(sK2,sK2,sK2),u1_struct_0(sK0))
    | spl6_14 ),
    inference(resolution,[],[f127,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f127,plain,
    ( ~ m1_subset_1(k1_enumset1(sK2,sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl6_14 ),
    inference(avatar_component_clause,[],[f125])).

fof(f131,plain,
    ( ~ spl6_2
    | spl6_13 ),
    inference(avatar_contradiction_clause,[],[f129])).

fof(f129,plain,
    ( $false
    | ~ spl6_2
    | spl6_13 ),
    inference(unit_resulting_resolution,[],[f51,f123,f40])).

fof(f123,plain,
    ( ~ r1_tarski(k1_enumset1(sK2,sK2,sK2),sK1)
    | spl6_13 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl6_13
  <=> r1_tarski(k1_enumset1(sK2,sK2,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f51,plain,
    ( r2_hidden(sK2,sK1)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f49])).

fof(f49,plain,
    ( spl6_2
  <=> r2_hidden(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f128,plain,
    ( ~ spl6_13
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f119,f125,f121])).

fof(f119,plain,
    ( ~ m1_subset_1(k1_enumset1(sK2,sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k1_enumset1(sK2,sK2,sK2),sK1) ),
    inference(equality_resolution,[],[f118])).

fof(f118,plain,(
    ! [X0] :
      ( k1_enumset1(sK2,sK2,sK2) != X0
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X0,sK1) ) ),
    inference(global_subsumption,[],[f22,f21,f20,f117])).

fof(f117,plain,(
    ! [X0] :
      ( k1_enumset1(sK2,sK2,sK2) != X0
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X0,sK1)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_tex_2(sK1,sK0) ) ),
    inference(duplicate_literal_removal,[],[f116])).

fof(f116,plain,(
    ! [X0] :
      ( k1_enumset1(sK2,sK2,sK2) != X0
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X0,sK1)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X0,sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_tex_2(sK1,sK0) ) ),
    inference(resolution,[],[f114,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(sK4(X0,X1,X2),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X2,X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

fof(f12,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tex_2)).

fof(f114,plain,(
    ! [X0] :
      ( ~ v3_pre_topc(sK4(sK0,sK1,X0),sK0)
      | k1_enumset1(sK2,sK2,sK2) != X0
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X0,sK1) ) ),
    inference(global_subsumption,[],[f22,f21,f20,f113])).

fof(f113,plain,(
    ! [X0] :
      ( ~ v3_pre_topc(sK4(sK0,sK1,X0),sK0)
      | k1_enumset1(sK2,sK2,sK2) != X0
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X0,sK1)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_tex_2(sK1,sK0) ) ),
    inference(duplicate_literal_removal,[],[f111])).

fof(f111,plain,(
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
    inference(resolution,[],[f95,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X2,X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f95,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK4(sK0,sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(sK4(sK0,sK1,X0),sK0)
      | k1_enumset1(sK2,sK2,sK2) != X0
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X0,sK1) ) ),
    inference(global_subsumption,[],[f22,f21,f20,f94])).

fof(f94,plain,(
    ! [X0] :
      ( k1_enumset1(sK2,sK2,sK2) != X0
      | ~ v3_pre_topc(sK4(sK0,sK1,X0),sK0)
      | ~ m1_subset_1(sK4(sK0,sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X0,sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_tex_2(sK1,sK0) ) ),
    inference(superposition,[],[f38,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(u1_struct_0(X0),X1,sK4(X0,X1,X2)) = X2
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X2,X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f38,plain,(
    ! [X3] :
      ( k9_subset_1(u1_struct_0(sK0),sK1,X3) != k1_enumset1(sK2,sK2,sK2)
      | ~ v3_pre_topc(X3,sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(definition_unfolding,[],[f17,f37])).

fof(f17,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X3,sK0)
      | k9_subset_1(u1_struct_0(sK0),sK1,X3) != k1_tarski(sK2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
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
    inference(flattening,[],[f10])).

fof(f10,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
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
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_tex_2)).

fof(f20,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f11])).

fof(f21,plain,(
    v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f22,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f93,plain,
    ( spl6_9
    | spl6_8
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f74,f59,f85,f90])).

fof(f85,plain,
    ( spl6_8
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f59,plain,
    ( spl6_4
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f74,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | r2_hidden(sK2,u1_struct_0(sK0))
    | ~ spl6_4 ),
    inference(resolution,[],[f61,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f61,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f59])).

fof(f88,plain,
    ( spl6_5
    | ~ spl6_8
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f77,f70,f85,f65])).

fof(f65,plain,
    ( spl6_5
  <=> sP5(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f70,plain,
    ( spl6_6
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f77,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | sP5(sK1)
    | ~ spl6_6 ),
    inference(resolution,[],[f72,f41])).

fof(f41,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | sP5(X1) ) ),
    inference(cnf_transformation,[],[f41_D])).

fof(f41_D,plain,(
    ! [X1] :
      ( ! [X2] :
          ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
          | ~ v1_xboole_0(X2) )
    <=> ~ sP5(X1) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP5])])).

fof(f72,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f70])).

fof(f73,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f20,f70])).

fof(f68,plain,
    ( ~ spl6_5
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f63,f49,f65])).

fof(f63,plain,
    ( ~ sP5(sK1)
    | ~ spl6_2 ),
    inference(resolution,[],[f51,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ sP5(X1) ) ),
    inference(general_splitting,[],[f36,f41_D])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f62,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f18,f59])).

fof(f18,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f52,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f19,f49])).

fof(f19,plain,(
    r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:43:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.22/0.50  % (28164)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.50  % (28177)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.50  % (28169)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.50  % (28172)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.51  % (28172)Refutation not found, incomplete strategy% (28172)------------------------------
% 0.22/0.51  % (28172)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (28172)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (28172)Memory used [KB]: 10746
% 0.22/0.51  % (28172)Time elapsed: 0.098 s
% 0.22/0.51  % (28172)------------------------------
% 0.22/0.51  % (28172)------------------------------
% 0.22/0.51  % (28161)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.51  % (28159)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.22/0.51  % (28177)Refutation found. Thanks to Tanya!
% 1.22/0.51  % SZS status Theorem for theBenchmark
% 1.22/0.51  % SZS output start Proof for theBenchmark
% 1.22/0.51  fof(f142,plain,(
% 1.22/0.51    $false),
% 1.22/0.51    inference(avatar_sat_refutation,[],[f52,f62,f68,f73,f88,f93,f128,f131,f138,f141])).
% 1.22/0.52  fof(f141,plain,(
% 1.22/0.52    ~spl6_9 | spl6_15),
% 1.22/0.52    inference(avatar_contradiction_clause,[],[f139])).
% 1.22/0.52  fof(f139,plain,(
% 1.22/0.52    $false | (~spl6_9 | spl6_15)),
% 1.22/0.52    inference(unit_resulting_resolution,[],[f92,f137,f40])).
% 1.22/0.52  fof(f40,plain,(
% 1.22/0.52    ( ! [X0,X1] : (r1_tarski(k1_enumset1(X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.22/0.52    inference(definition_unfolding,[],[f32,f37])).
% 1.22/0.52  fof(f37,plain,(
% 1.22/0.52    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 1.22/0.52    inference(definition_unfolding,[],[f23,f30])).
% 1.22/0.52  % (28181)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.22/0.52  fof(f30,plain,(
% 1.22/0.52    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.22/0.52    inference(cnf_transformation,[],[f2])).
% 1.22/0.52  fof(f2,axiom,(
% 1.22/0.52    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.22/0.52  fof(f23,plain,(
% 1.22/0.52    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.22/0.52    inference(cnf_transformation,[],[f1])).
% 1.22/0.52  fof(f1,axiom,(
% 1.22/0.52    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.22/0.52  fof(f32,plain,(
% 1.22/0.52    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1)) )),
% 1.22/0.52    inference(cnf_transformation,[],[f3])).
% 1.22/0.52  fof(f3,axiom,(
% 1.22/0.52    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 1.22/0.52  fof(f137,plain,(
% 1.22/0.52    ~r1_tarski(k1_enumset1(sK2,sK2,sK2),u1_struct_0(sK0)) | spl6_15),
% 1.22/0.52    inference(avatar_component_clause,[],[f135])).
% 1.22/0.52  fof(f135,plain,(
% 1.22/0.52    spl6_15 <=> r1_tarski(k1_enumset1(sK2,sK2,sK2),u1_struct_0(sK0))),
% 1.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 1.22/0.52  fof(f92,plain,(
% 1.22/0.52    r2_hidden(sK2,u1_struct_0(sK0)) | ~spl6_9),
% 1.22/0.52    inference(avatar_component_clause,[],[f90])).
% 1.22/0.52  fof(f90,plain,(
% 1.22/0.52    spl6_9 <=> r2_hidden(sK2,u1_struct_0(sK0))),
% 1.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 1.22/0.52  fof(f138,plain,(
% 1.22/0.52    ~spl6_15 | spl6_14),
% 1.22/0.52    inference(avatar_split_clause,[],[f133,f125,f135])).
% 1.22/0.52  fof(f125,plain,(
% 1.22/0.52    spl6_14 <=> m1_subset_1(k1_enumset1(sK2,sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 1.22/0.52  fof(f133,plain,(
% 1.22/0.52    ~r1_tarski(k1_enumset1(sK2,sK2,sK2),u1_struct_0(sK0)) | spl6_14),
% 1.22/0.52    inference(resolution,[],[f127,f34])).
% 1.22/0.52  fof(f34,plain,(
% 1.22/0.52    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.22/0.52    inference(cnf_transformation,[],[f5])).
% 1.22/0.52  fof(f5,axiom,(
% 1.22/0.52    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.22/0.52  fof(f127,plain,(
% 1.22/0.52    ~m1_subset_1(k1_enumset1(sK2,sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | spl6_14),
% 1.22/0.52    inference(avatar_component_clause,[],[f125])).
% 1.22/0.52  fof(f131,plain,(
% 1.22/0.52    ~spl6_2 | spl6_13),
% 1.22/0.52    inference(avatar_contradiction_clause,[],[f129])).
% 1.22/0.52  fof(f129,plain,(
% 1.22/0.52    $false | (~spl6_2 | spl6_13)),
% 1.22/0.52    inference(unit_resulting_resolution,[],[f51,f123,f40])).
% 1.22/0.52  fof(f123,plain,(
% 1.22/0.52    ~r1_tarski(k1_enumset1(sK2,sK2,sK2),sK1) | spl6_13),
% 1.22/0.52    inference(avatar_component_clause,[],[f121])).
% 1.22/0.52  fof(f121,plain,(
% 1.22/0.52    spl6_13 <=> r1_tarski(k1_enumset1(sK2,sK2,sK2),sK1)),
% 1.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 1.22/0.52  fof(f51,plain,(
% 1.22/0.52    r2_hidden(sK2,sK1) | ~spl6_2),
% 1.22/0.52    inference(avatar_component_clause,[],[f49])).
% 1.22/0.52  fof(f49,plain,(
% 1.22/0.52    spl6_2 <=> r2_hidden(sK2,sK1)),
% 1.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.22/0.52  fof(f128,plain,(
% 1.22/0.52    ~spl6_13 | ~spl6_14),
% 1.22/0.52    inference(avatar_split_clause,[],[f119,f125,f121])).
% 1.22/0.52  fof(f119,plain,(
% 1.22/0.52    ~m1_subset_1(k1_enumset1(sK2,sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(k1_enumset1(sK2,sK2,sK2),sK1)),
% 1.22/0.52    inference(equality_resolution,[],[f118])).
% 1.22/0.52  fof(f118,plain,(
% 1.22/0.52    ( ! [X0] : (k1_enumset1(sK2,sK2,sK2) != X0 | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,sK1)) )),
% 1.22/0.52    inference(global_subsumption,[],[f22,f21,f20,f117])).
% 1.22/0.52  fof(f117,plain,(
% 1.22/0.52    ( ! [X0] : (k1_enumset1(sK2,sK2,sK2) != X0 | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_tex_2(sK1,sK0)) )),
% 1.22/0.52    inference(duplicate_literal_removal,[],[f116])).
% 1.22/0.52  fof(f116,plain,(
% 1.22/0.52    ( ! [X0] : (k1_enumset1(sK2,sK2,sK2) != X0 | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,sK1) | ~l1_pre_topc(sK0) | ~v2_tex_2(sK1,sK0)) )),
% 1.22/0.52    inference(resolution,[],[f114,f26])).
% 1.22/0.52  fof(f26,plain,(
% 1.22/0.52    ( ! [X2,X0,X1] : (v3_pre_topc(sK4(X0,X1,X2),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X2,X1) | ~l1_pre_topc(X0) | ~v2_tex_2(X1,X0)) )),
% 1.22/0.52    inference(cnf_transformation,[],[f13])).
% 1.22/0.52  fof(f13,plain,(
% 1.22/0.52    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.22/0.52    inference(flattening,[],[f12])).
% 1.22/0.52  fof(f12,plain,(
% 1.22/0.52    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((? [X3] : ((k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.22/0.52    inference(ennf_transformation,[],[f7])).
% 1.22/0.52  fof(f7,axiom,(
% 1.22/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0))) & r1_tarski(X2,X1))))))),
% 1.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tex_2)).
% 1.22/0.52  fof(f114,plain,(
% 1.22/0.52    ( ! [X0] : (~v3_pre_topc(sK4(sK0,sK1,X0),sK0) | k1_enumset1(sK2,sK2,sK2) != X0 | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,sK1)) )),
% 1.22/0.52    inference(global_subsumption,[],[f22,f21,f20,f113])).
% 1.22/0.52  fof(f113,plain,(
% 1.22/0.52    ( ! [X0] : (~v3_pre_topc(sK4(sK0,sK1,X0),sK0) | k1_enumset1(sK2,sK2,sK2) != X0 | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_tex_2(sK1,sK0)) )),
% 1.22/0.52    inference(duplicate_literal_removal,[],[f111])).
% 1.22/0.52  fof(f111,plain,(
% 1.22/0.52    ( ! [X0] : (~v3_pre_topc(sK4(sK0,sK1,X0),sK0) | k1_enumset1(sK2,sK2,sK2) != X0 | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,sK1) | ~l1_pre_topc(sK0) | ~v2_tex_2(sK1,sK0)) )),
% 1.22/0.52    inference(resolution,[],[f95,f25])).
% 1.22/0.52  fof(f25,plain,(
% 1.22/0.52    ( ! [X2,X0,X1] : (m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X2,X1) | ~l1_pre_topc(X0) | ~v2_tex_2(X1,X0)) )),
% 1.22/0.52    inference(cnf_transformation,[],[f13])).
% 1.22/0.52  fof(f95,plain,(
% 1.22/0.52    ( ! [X0] : (~m1_subset_1(sK4(sK0,sK1,X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(sK4(sK0,sK1,X0),sK0) | k1_enumset1(sK2,sK2,sK2) != X0 | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,sK1)) )),
% 1.22/0.52    inference(global_subsumption,[],[f22,f21,f20,f94])).
% 1.22/0.52  fof(f94,plain,(
% 1.22/0.52    ( ! [X0] : (k1_enumset1(sK2,sK2,sK2) != X0 | ~v3_pre_topc(sK4(sK0,sK1,X0),sK0) | ~m1_subset_1(sK4(sK0,sK1,X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,sK1) | ~l1_pre_topc(sK0) | ~v2_tex_2(sK1,sK0)) )),
% 1.22/0.52    inference(superposition,[],[f38,f27])).
% 1.22/0.52  fof(f27,plain,(
% 1.22/0.52    ( ! [X2,X0,X1] : (k9_subset_1(u1_struct_0(X0),X1,sK4(X0,X1,X2)) = X2 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X2,X1) | ~l1_pre_topc(X0) | ~v2_tex_2(X1,X0)) )),
% 1.22/0.52    inference(cnf_transformation,[],[f13])).
% 1.22/0.52  fof(f38,plain,(
% 1.22/0.52    ( ! [X3] : (k9_subset_1(u1_struct_0(sK0),sK1,X3) != k1_enumset1(sK2,sK2,sK2) | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 1.22/0.52    inference(definition_unfolding,[],[f17,f37])).
% 1.22/0.52  fof(f17,plain,(
% 1.22/0.52    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X3,sK0) | k9_subset_1(u1_struct_0(sK0),sK1,X3) != k1_tarski(sK2)) )),
% 1.22/0.52    inference(cnf_transformation,[],[f11])).
% 1.22/0.52  fof(f11,plain,(
% 1.22/0.52    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != k1_tarski(X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.22/0.52    inference(flattening,[],[f10])).
% 1.22/0.52  fof(f10,plain,(
% 1.22/0.52    ? [X0] : (? [X1] : ((? [X2] : ((! [X3] : ((k9_subset_1(u1_struct_0(X0),X1,X3) != k1_tarski(X2) | ~v3_pre_topc(X3,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1)) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.22/0.52    inference(ennf_transformation,[],[f9])).
% 1.22/0.52  fof(f9,negated_conjecture,(
% 1.22/0.52    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = k1_tarski(X2) & v3_pre_topc(X3,X0))) & r2_hidden(X2,X1))))))),
% 1.22/0.52    inference(negated_conjecture,[],[f8])).
% 1.22/0.52  fof(f8,conjecture,(
% 1.22/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = k1_tarski(X2) & v3_pre_topc(X3,X0))) & r2_hidden(X2,X1))))))),
% 1.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_tex_2)).
% 1.22/0.52  fof(f20,plain,(
% 1.22/0.52    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.22/0.52    inference(cnf_transformation,[],[f11])).
% 1.22/0.52  fof(f21,plain,(
% 1.22/0.52    v2_tex_2(sK1,sK0)),
% 1.22/0.52    inference(cnf_transformation,[],[f11])).
% 1.22/0.52  fof(f22,plain,(
% 1.22/0.52    l1_pre_topc(sK0)),
% 1.22/0.52    inference(cnf_transformation,[],[f11])).
% 1.22/0.52  fof(f93,plain,(
% 1.22/0.52    spl6_9 | spl6_8 | ~spl6_4),
% 1.22/0.52    inference(avatar_split_clause,[],[f74,f59,f85,f90])).
% 1.22/0.52  fof(f85,plain,(
% 1.22/0.52    spl6_8 <=> v1_xboole_0(u1_struct_0(sK0))),
% 1.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 1.22/0.52  fof(f59,plain,(
% 1.22/0.52    spl6_4 <=> m1_subset_1(sK2,u1_struct_0(sK0))),
% 1.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 1.22/0.52  fof(f74,plain,(
% 1.22/0.52    v1_xboole_0(u1_struct_0(sK0)) | r2_hidden(sK2,u1_struct_0(sK0)) | ~spl6_4),
% 1.22/0.52    inference(resolution,[],[f61,f31])).
% 1.22/0.52  fof(f31,plain,(
% 1.22/0.52    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 1.22/0.52    inference(cnf_transformation,[],[f15])).
% 1.22/0.52  fof(f15,plain,(
% 1.22/0.52    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.22/0.52    inference(flattening,[],[f14])).
% 1.22/0.52  fof(f14,plain,(
% 1.22/0.52    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.22/0.52    inference(ennf_transformation,[],[f4])).
% 1.22/0.52  fof(f4,axiom,(
% 1.22/0.52    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 1.22/0.52  fof(f61,plain,(
% 1.22/0.52    m1_subset_1(sK2,u1_struct_0(sK0)) | ~spl6_4),
% 1.22/0.52    inference(avatar_component_clause,[],[f59])).
% 1.22/0.52  fof(f88,plain,(
% 1.22/0.52    spl6_5 | ~spl6_8 | ~spl6_6),
% 1.22/0.52    inference(avatar_split_clause,[],[f77,f70,f85,f65])).
% 1.22/0.52  fof(f65,plain,(
% 1.22/0.52    spl6_5 <=> sP5(sK1)),
% 1.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 1.22/0.52  fof(f70,plain,(
% 1.22/0.52    spl6_6 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 1.22/0.52  fof(f77,plain,(
% 1.22/0.52    ~v1_xboole_0(u1_struct_0(sK0)) | sP5(sK1) | ~spl6_6),
% 1.22/0.52    inference(resolution,[],[f72,f41])).
% 1.22/0.52  fof(f41,plain,(
% 1.22/0.52    ( ! [X2,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2) | sP5(X1)) )),
% 1.22/0.52    inference(cnf_transformation,[],[f41_D])).
% 1.22/0.52  fof(f41_D,plain,(
% 1.22/0.52    ( ! [X1] : (( ! [X2] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2)) ) <=> ~sP5(X1)) )),
% 1.22/0.52    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP5])])).
% 1.22/0.52  fof(f72,plain,(
% 1.22/0.52    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl6_6),
% 1.22/0.52    inference(avatar_component_clause,[],[f70])).
% 1.22/0.52  fof(f73,plain,(
% 1.22/0.52    spl6_6),
% 1.22/0.52    inference(avatar_split_clause,[],[f20,f70])).
% 1.22/0.52  fof(f68,plain,(
% 1.22/0.52    ~spl6_5 | ~spl6_2),
% 1.22/0.52    inference(avatar_split_clause,[],[f63,f49,f65])).
% 1.22/0.52  fof(f63,plain,(
% 1.22/0.52    ~sP5(sK1) | ~spl6_2),
% 1.22/0.52    inference(resolution,[],[f51,f42])).
% 1.22/0.52  fof(f42,plain,(
% 1.22/0.52    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~sP5(X1)) )),
% 1.22/0.52    inference(general_splitting,[],[f36,f41_D])).
% 1.22/0.52  fof(f36,plain,(
% 1.22/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2)) )),
% 1.22/0.52    inference(cnf_transformation,[],[f16])).
% 1.22/0.52  fof(f16,plain,(
% 1.22/0.52    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.22/0.52    inference(ennf_transformation,[],[f6])).
% 1.22/0.52  fof(f6,axiom,(
% 1.22/0.52    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 1.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 1.22/0.52  fof(f62,plain,(
% 1.22/0.52    spl6_4),
% 1.22/0.52    inference(avatar_split_clause,[],[f18,f59])).
% 1.22/0.52  fof(f18,plain,(
% 1.22/0.52    m1_subset_1(sK2,u1_struct_0(sK0))),
% 1.22/0.52    inference(cnf_transformation,[],[f11])).
% 1.22/0.52  fof(f52,plain,(
% 1.22/0.52    spl6_2),
% 1.22/0.52    inference(avatar_split_clause,[],[f19,f49])).
% 1.22/0.52  fof(f19,plain,(
% 1.22/0.52    r2_hidden(sK2,sK1)),
% 1.22/0.52    inference(cnf_transformation,[],[f11])).
% 1.22/0.52  % SZS output end Proof for theBenchmark
% 1.22/0.52  % (28177)------------------------------
% 1.22/0.52  % (28177)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.22/0.52  % (28177)Termination reason: Refutation
% 1.22/0.52  
% 1.22/0.52  % (28177)Memory used [KB]: 10746
% 1.22/0.52  % (28177)Time elapsed: 0.061 s
% 1.22/0.52  % (28177)------------------------------
% 1.22/0.52  % (28177)------------------------------
% 1.22/0.52  % (28154)Success in time 0.161 s
%------------------------------------------------------------------------------
