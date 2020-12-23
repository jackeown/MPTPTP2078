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
% DateTime   : Thu Dec  3 13:21:28 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 221 expanded)
%              Number of leaves         :   29 ( 100 expanded)
%              Depth                    :   14
%              Number of atoms          :  394 (1004 expanded)
%              Number of equality atoms :   44 ( 131 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f346,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f63,f68,f73,f78,f83,f88,f93,f98,f119,f146,f158,f172,f184,f201,f230,f245,f345])).

fof(f345,plain,
    ( ~ spl5_18
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | spl5_8
    | ~ spl5_20
    | spl5_25 ),
    inference(avatar_split_clause,[],[f329,f242,f218,f95,f90,f85,f80,f75,f198])).

fof(f198,plain,
    ( spl5_18
  <=> m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f75,plain,
    ( spl5_4
  <=> v2_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f80,plain,
    ( spl5_5
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f85,plain,
    ( spl5_6
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f90,plain,
    ( spl5_7
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f95,plain,
    ( spl5_8
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f218,plain,
    ( spl5_20
  <=> r1_tarski(k2_tarski(sK2,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f242,plain,
    ( spl5_25
  <=> k2_tarski(sK2,sK2) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k2_tarski(sK2,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f329,plain,
    ( ~ m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | spl5_8
    | ~ spl5_20
    | spl5_25 ),
    inference(unit_resulting_resolution,[],[f244,f220,f150])).

fof(f150,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X0,sK1)
        | k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X0)) = X0 )
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | spl5_8 ),
    inference(subsumption_resolution,[],[f149,f97])).

fof(f97,plain,
    ( ~ v2_struct_0(sK0)
    | spl5_8 ),
    inference(avatar_component_clause,[],[f95])).

fof(f149,plain,
    ( ! [X0] :
        ( k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X0)) = X0
        | ~ r1_tarski(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_struct_0(sK0) )
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f148,f92])).

fof(f92,plain,
    ( v2_pre_topc(sK0)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f90])).

fof(f148,plain,
    ( ! [X0] :
        ( k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X0)) = X0
        | ~ r1_tarski(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f147,f87])).

fof(f87,plain,
    ( l1_pre_topc(sK0)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f85])).

fof(f147,plain,
    ( ! [X0] :
        ( k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X0)) = X0
        | ~ r1_tarski(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f133,f77])).

fof(f77,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f75])).

fof(f133,plain,
    ( ! [X0] :
        ( k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X0)) = X0
        | ~ r1_tarski(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(sK1,sK0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_5 ),
    inference(resolution,[],[f82,f44])).

fof(f44,plain,(
    ! [X0,X3,X1] :
      ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3
      | ~ r1_tarski(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f27,f28])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2
          & r1_tarski(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( sK3(X0,X1) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK3(X0,X1)))
        & r1_tarski(sK3(X0,X1),X1)
        & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
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
    inference(rectify,[],[f26])).

fof(f26,plain,(
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
    inference(nnf_transformation,[],[f14])).

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

% (1366)Termination reason: Refutation not found, incomplete strategy

fof(f82,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f80])).

% (1366)Memory used [KB]: 10746
fof(f220,plain,
    ( r1_tarski(k2_tarski(sK2,sK2),sK1)
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f218])).

% (1366)Time elapsed: 0.162 s
% (1366)------------------------------
% (1366)------------------------------
fof(f244,plain,
    ( k2_tarski(sK2,sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k2_tarski(sK2,sK2)))
    | spl5_25 ),
    inference(avatar_component_clause,[],[f242])).

fof(f245,plain,
    ( ~ spl5_25
    | spl5_1
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f240,f127,f60,f242])).

fof(f60,plain,
    ( spl5_1
  <=> k6_domain_1(u1_struct_0(sK0),sK2) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f127,plain,
    ( spl5_11
  <=> k6_domain_1(u1_struct_0(sK0),sK2) = k2_tarski(sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f240,plain,
    ( k2_tarski(sK2,sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k2_tarski(sK2,sK2)))
    | spl5_1
    | ~ spl5_11 ),
    inference(backward_demodulation,[],[f62,f129])).

fof(f129,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK2) = k2_tarski(sK2,sK2)
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f127])).

fof(f62,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f60])).

fof(f230,plain,
    ( spl5_20
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f215,f116,f218])).

fof(f116,plain,
    ( spl5_9
  <=> m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f215,plain,
    ( r1_tarski(k2_tarski(sK2,sK2),sK1)
    | ~ spl5_9 ),
    inference(resolution,[],[f118,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
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

fof(f118,plain,
    ( m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(sK1))
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f116])).

fof(f201,plain,
    ( spl5_18
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f193,f181,f198])).

fof(f181,plain,
    ( spl5_16
  <=> r2_hidden(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f193,plain,
    ( m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_16 ),
    inference(unit_resulting_resolution,[],[f183,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f48,f43])).

fof(f43,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

fof(f183,plain,
    ( r2_hidden(sK2,u1_struct_0(sK0))
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f181])).

fof(f184,plain,
    ( spl5_16
    | ~ spl5_2
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f174,f142,f65,f181])).

fof(f65,plain,
    ( spl5_2
  <=> r2_hidden(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f142,plain,
    ( spl5_12
  <=> r1_tarski(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f174,plain,
    ( r2_hidden(sK2,u1_struct_0(sK0))
    | ~ spl5_2
    | ~ spl5_12 ),
    inference(unit_resulting_resolution,[],[f67,f144,f50])).

fof(f50,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f31,f32])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f144,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f142])).

fof(f67,plain,
    ( r2_hidden(sK2,sK1)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f65])).

fof(f172,plain,
    ( spl5_11
    | ~ spl5_3
    | spl5_10 ),
    inference(avatar_split_clause,[],[f170,f123,f70,f127])).

fof(f70,plain,
    ( spl5_3
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f123,plain,
    ( spl5_10
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f170,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK2) = k2_tarski(sK2,sK2)
    | ~ spl5_3
    | spl5_10 ),
    inference(unit_resulting_resolution,[],[f72,f124,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k2_tarski(X1,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f49,f43])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
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

fof(f124,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | spl5_10 ),
    inference(avatar_component_clause,[],[f123])).

fof(f72,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f70])).

fof(f158,plain,
    ( spl5_12
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f139,f80,f142])).

fof(f139,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl5_5 ),
    inference(resolution,[],[f82,f53])).

fof(f146,plain,
    ( ~ spl5_10
    | ~ spl5_2
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f131,f80,f65,f123])).

fof(f131,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl5_2
    | ~ spl5_5 ),
    inference(unit_resulting_resolution,[],[f67,f82,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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

fof(f119,plain,
    ( spl5_9
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f111,f65,f116])).

fof(f111,plain,
    ( m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(sK1))
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f67,f57])).

fof(f98,plain,(
    ~ spl5_8 ),
    inference(avatar_split_clause,[],[f35,f95])).

fof(f35,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
    & r2_hidden(sK2,sK1)
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & v2_tex_2(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f24,f23,f22])).

fof(f22,plain,
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

fof(f23,plain,
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

fof(f24,plain,
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

fof(f93,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f36,f90])).

fof(f36,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f88,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f37,f85])).

fof(f37,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f83,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f38,f80])).

fof(f38,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f25])).

fof(f78,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f39,f75])).

fof(f39,plain,(
    v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f73,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f40,f70])).

fof(f40,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f25])).

fof(f68,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f41,f65])).

fof(f41,plain,(
    r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f63,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f42,f60])).

fof(f42,plain,(
    k6_domain_1(u1_struct_0(sK0),sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n012.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:34:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.56  % (1357)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.56  % (1356)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.56  % (1360)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.57  % (1366)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.57  % (1381)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.57  % (1381)Refutation found. Thanks to Tanya!
% 0.22/0.57  % SZS status Theorem for theBenchmark
% 0.22/0.57  % (1361)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.57  % (1364)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.58  % (1380)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.58  % (1376)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.58  % (1372)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.58  % (1369)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.59  % (1366)Refutation not found, incomplete strategy% (1366)------------------------------
% 0.22/0.59  % (1366)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.59  % SZS output start Proof for theBenchmark
% 0.22/0.59  fof(f346,plain,(
% 0.22/0.59    $false),
% 0.22/0.59    inference(avatar_sat_refutation,[],[f63,f68,f73,f78,f83,f88,f93,f98,f119,f146,f158,f172,f184,f201,f230,f245,f345])).
% 0.22/0.59  fof(f345,plain,(
% 0.22/0.59    ~spl5_18 | ~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_7 | spl5_8 | ~spl5_20 | spl5_25),
% 0.22/0.59    inference(avatar_split_clause,[],[f329,f242,f218,f95,f90,f85,f80,f75,f198])).
% 0.22/0.59  fof(f198,plain,(
% 0.22/0.59    spl5_18 <=> m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 0.22/0.59  fof(f75,plain,(
% 0.22/0.59    spl5_4 <=> v2_tex_2(sK1,sK0)),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.22/0.59  fof(f80,plain,(
% 0.22/0.59    spl5_5 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.22/0.59  fof(f85,plain,(
% 0.22/0.59    spl5_6 <=> l1_pre_topc(sK0)),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.22/0.59  fof(f90,plain,(
% 0.22/0.59    spl5_7 <=> v2_pre_topc(sK0)),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.22/0.59  fof(f95,plain,(
% 0.22/0.59    spl5_8 <=> v2_struct_0(sK0)),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.22/0.59  fof(f218,plain,(
% 0.22/0.59    spl5_20 <=> r1_tarski(k2_tarski(sK2,sK2),sK1)),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 0.22/0.59  fof(f242,plain,(
% 0.22/0.59    spl5_25 <=> k2_tarski(sK2,sK2) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k2_tarski(sK2,sK2)))),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).
% 0.22/0.59  fof(f329,plain,(
% 0.22/0.59    ~m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_7 | spl5_8 | ~spl5_20 | spl5_25)),
% 0.22/0.59    inference(unit_resulting_resolution,[],[f244,f220,f150])).
% 0.22/0.59  fof(f150,plain,(
% 0.22/0.59    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,sK1) | k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X0)) = X0) ) | (~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_7 | spl5_8)),
% 0.22/0.59    inference(subsumption_resolution,[],[f149,f97])).
% 0.22/0.59  fof(f97,plain,(
% 0.22/0.59    ~v2_struct_0(sK0) | spl5_8),
% 0.22/0.59    inference(avatar_component_clause,[],[f95])).
% 0.22/0.59  fof(f149,plain,(
% 0.22/0.59    ( ! [X0] : (k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X0)) = X0 | ~r1_tarski(X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0)) ) | (~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_7)),
% 0.22/0.59    inference(subsumption_resolution,[],[f148,f92])).
% 0.22/0.59  fof(f92,plain,(
% 0.22/0.59    v2_pre_topc(sK0) | ~spl5_7),
% 0.22/0.59    inference(avatar_component_clause,[],[f90])).
% 0.22/0.59  fof(f148,plain,(
% 0.22/0.59    ( ! [X0] : (k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X0)) = X0 | ~r1_tarski(X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl5_4 | ~spl5_5 | ~spl5_6)),
% 0.22/0.59    inference(subsumption_resolution,[],[f147,f87])).
% 0.22/0.59  fof(f87,plain,(
% 0.22/0.59    l1_pre_topc(sK0) | ~spl5_6),
% 0.22/0.59    inference(avatar_component_clause,[],[f85])).
% 0.22/0.59  fof(f147,plain,(
% 0.22/0.59    ( ! [X0] : (k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X0)) = X0 | ~r1_tarski(X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl5_4 | ~spl5_5)),
% 0.22/0.59    inference(subsumption_resolution,[],[f133,f77])).
% 0.22/0.59  fof(f77,plain,(
% 0.22/0.59    v2_tex_2(sK1,sK0) | ~spl5_4),
% 0.22/0.59    inference(avatar_component_clause,[],[f75])).
% 0.22/0.59  fof(f133,plain,(
% 0.22/0.59    ( ! [X0] : (k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X0)) = X0 | ~r1_tarski(X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl5_5),
% 0.22/0.59    inference(resolution,[],[f82,f44])).
% 0.22/0.59  fof(f44,plain,(
% 0.22/0.59    ( ! [X0,X3,X1] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f29])).
% 0.22/0.59  fof(f29,plain,(
% 0.22/0.59    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | (sK3(X0,X1) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK3(X0,X1))) & r1_tarski(sK3(X0,X1),X1) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f27,f28])).
% 0.22/0.59  fof(f28,plain,(
% 0.22/0.59    ! [X1,X0] : (? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (sK3(X0,X1) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK3(X0,X1))) & r1_tarski(sK3(X0,X1),X1) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.59    introduced(choice_axiom,[])).
% 0.22/0.59  fof(f27,plain,(
% 0.22/0.59    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.59    inference(rectify,[],[f26])).
% 0.22/0.59  fof(f26,plain,(
% 0.22/0.59    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.59    inference(nnf_transformation,[],[f14])).
% 0.22/0.59  fof(f14,plain,(
% 0.22/0.59    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.59    inference(flattening,[],[f13])).
% 0.22/0.59  fof(f13,plain,(
% 0.22/0.59    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.59    inference(ennf_transformation,[],[f8])).
% 0.22/0.59  fof(f8,axiom,(
% 0.22/0.59    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X2,X1) => k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2)))))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_tex_2)).
% 0.22/0.59  % (1366)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.59  
% 0.22/0.59  fof(f82,plain,(
% 0.22/0.59    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_5),
% 0.22/0.59    inference(avatar_component_clause,[],[f80])).
% 0.22/0.59  % (1366)Memory used [KB]: 10746
% 0.22/0.59  fof(f220,plain,(
% 0.22/0.59    r1_tarski(k2_tarski(sK2,sK2),sK1) | ~spl5_20),
% 0.22/0.59    inference(avatar_component_clause,[],[f218])).
% 0.22/0.59  % (1366)Time elapsed: 0.162 s
% 0.22/0.59  % (1366)------------------------------
% 0.22/0.59  % (1366)------------------------------
% 0.22/0.59  fof(f244,plain,(
% 0.22/0.59    k2_tarski(sK2,sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k2_tarski(sK2,sK2))) | spl5_25),
% 0.22/0.59    inference(avatar_component_clause,[],[f242])).
% 0.22/0.59  fof(f245,plain,(
% 0.22/0.59    ~spl5_25 | spl5_1 | ~spl5_11),
% 0.22/0.59    inference(avatar_split_clause,[],[f240,f127,f60,f242])).
% 0.22/0.59  fof(f60,plain,(
% 0.22/0.59    spl5_1 <=> k6_domain_1(u1_struct_0(sK0),sK2) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.22/0.59  fof(f127,plain,(
% 0.22/0.59    spl5_11 <=> k6_domain_1(u1_struct_0(sK0),sK2) = k2_tarski(sK2,sK2)),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.22/0.59  fof(f240,plain,(
% 0.22/0.59    k2_tarski(sK2,sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k2_tarski(sK2,sK2))) | (spl5_1 | ~spl5_11)),
% 0.22/0.59    inference(backward_demodulation,[],[f62,f129])).
% 0.22/0.59  fof(f129,plain,(
% 0.22/0.59    k6_domain_1(u1_struct_0(sK0),sK2) = k2_tarski(sK2,sK2) | ~spl5_11),
% 0.22/0.59    inference(avatar_component_clause,[],[f127])).
% 0.22/0.59  fof(f62,plain,(
% 0.22/0.59    k6_domain_1(u1_struct_0(sK0),sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) | spl5_1),
% 0.22/0.59    inference(avatar_component_clause,[],[f60])).
% 0.22/0.59  fof(f230,plain,(
% 0.22/0.59    spl5_20 | ~spl5_9),
% 0.22/0.59    inference(avatar_split_clause,[],[f215,f116,f218])).
% 0.22/0.59  fof(f116,plain,(
% 0.22/0.59    spl5_9 <=> m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(sK1))),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.22/0.59  fof(f215,plain,(
% 0.22/0.59    r1_tarski(k2_tarski(sK2,sK2),sK1) | ~spl5_9),
% 0.22/0.59    inference(resolution,[],[f118,f53])).
% 0.22/0.59  fof(f53,plain,(
% 0.22/0.59    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.22/0.59    inference(cnf_transformation,[],[f34])).
% 0.22/0.59  fof(f34,plain,(
% 0.22/0.59    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.22/0.59    inference(nnf_transformation,[],[f5])).
% 0.22/0.59  fof(f5,axiom,(
% 0.22/0.59    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.59  fof(f118,plain,(
% 0.22/0.59    m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(sK1)) | ~spl5_9),
% 0.22/0.59    inference(avatar_component_clause,[],[f116])).
% 0.22/0.59  fof(f201,plain,(
% 0.22/0.59    spl5_18 | ~spl5_16),
% 0.22/0.59    inference(avatar_split_clause,[],[f193,f181,f198])).
% 0.22/0.59  fof(f181,plain,(
% 0.22/0.59    spl5_16 <=> r2_hidden(sK2,u1_struct_0(sK0))),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.22/0.59  fof(f193,plain,(
% 0.22/0.59    m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_16),
% 0.22/0.59    inference(unit_resulting_resolution,[],[f183,f57])).
% 0.22/0.59  fof(f57,plain,(
% 0.22/0.59    ( ! [X0,X1] : (m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 0.22/0.59    inference(definition_unfolding,[],[f48,f43])).
% 0.22/0.59  fof(f43,plain,(
% 0.22/0.59    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f3])).
% 0.22/0.59  fof(f3,axiom,(
% 0.22/0.59    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.59  fof(f48,plain,(
% 0.22/0.59    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f15])).
% 0.22/0.59  fof(f15,plain,(
% 0.22/0.59    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 0.22/0.59    inference(ennf_transformation,[],[f4])).
% 0.22/0.59  fof(f4,axiom,(
% 0.22/0.59    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).
% 0.22/0.59  fof(f183,plain,(
% 0.22/0.59    r2_hidden(sK2,u1_struct_0(sK0)) | ~spl5_16),
% 0.22/0.59    inference(avatar_component_clause,[],[f181])).
% 0.22/0.59  fof(f184,plain,(
% 0.22/0.59    spl5_16 | ~spl5_2 | ~spl5_12),
% 0.22/0.59    inference(avatar_split_clause,[],[f174,f142,f65,f181])).
% 0.22/0.59  fof(f65,plain,(
% 0.22/0.59    spl5_2 <=> r2_hidden(sK2,sK1)),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.22/0.59  fof(f142,plain,(
% 0.22/0.59    spl5_12 <=> r1_tarski(sK1,u1_struct_0(sK0))),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.22/0.59  fof(f174,plain,(
% 0.22/0.59    r2_hidden(sK2,u1_struct_0(sK0)) | (~spl5_2 | ~spl5_12)),
% 0.22/0.59    inference(unit_resulting_resolution,[],[f67,f144,f50])).
% 0.22/0.59  fof(f50,plain,(
% 0.22/0.59    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f33])).
% 0.22/0.59  fof(f33,plain,(
% 0.22/0.59    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f31,f32])).
% 0.22/0.59  fof(f32,plain,(
% 0.22/0.59    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 0.22/0.59    introduced(choice_axiom,[])).
% 0.22/0.59  fof(f31,plain,(
% 0.22/0.59    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.59    inference(rectify,[],[f30])).
% 0.22/0.59  fof(f30,plain,(
% 0.22/0.59    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.59    inference(nnf_transformation,[],[f18])).
% 0.22/0.59  fof(f18,plain,(
% 0.22/0.59    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.22/0.59    inference(ennf_transformation,[],[f1])).
% 0.22/0.59  fof(f1,axiom,(
% 0.22/0.59    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.59  fof(f144,plain,(
% 0.22/0.59    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl5_12),
% 0.22/0.59    inference(avatar_component_clause,[],[f142])).
% 0.22/0.59  fof(f67,plain,(
% 0.22/0.59    r2_hidden(sK2,sK1) | ~spl5_2),
% 0.22/0.59    inference(avatar_component_clause,[],[f65])).
% 0.22/0.59  fof(f172,plain,(
% 0.22/0.59    spl5_11 | ~spl5_3 | spl5_10),
% 0.22/0.59    inference(avatar_split_clause,[],[f170,f123,f70,f127])).
% 0.22/0.59  fof(f70,plain,(
% 0.22/0.59    spl5_3 <=> m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.22/0.59  fof(f123,plain,(
% 0.22/0.59    spl5_10 <=> v1_xboole_0(u1_struct_0(sK0))),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.22/0.59  fof(f170,plain,(
% 0.22/0.59    k6_domain_1(u1_struct_0(sK0),sK2) = k2_tarski(sK2,sK2) | (~spl5_3 | spl5_10)),
% 0.22/0.59    inference(unit_resulting_resolution,[],[f72,f124,f58])).
% 0.22/0.59  fof(f58,plain,(
% 0.22/0.59    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k2_tarski(X1,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.22/0.59    inference(definition_unfolding,[],[f49,f43])).
% 0.22/0.59  fof(f49,plain,(
% 0.22/0.59    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f17])).
% 0.22/0.59  fof(f17,plain,(
% 0.22/0.59    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.22/0.59    inference(flattening,[],[f16])).
% 0.22/0.59  fof(f16,plain,(
% 0.22/0.59    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.22/0.59    inference(ennf_transformation,[],[f7])).
% 0.22/0.59  fof(f7,axiom,(
% 0.22/0.59    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.22/0.59  fof(f124,plain,(
% 0.22/0.59    ~v1_xboole_0(u1_struct_0(sK0)) | spl5_10),
% 0.22/0.59    inference(avatar_component_clause,[],[f123])).
% 0.22/0.59  fof(f72,plain,(
% 0.22/0.59    m1_subset_1(sK2,u1_struct_0(sK0)) | ~spl5_3),
% 0.22/0.59    inference(avatar_component_clause,[],[f70])).
% 0.22/0.59  fof(f158,plain,(
% 0.22/0.59    spl5_12 | ~spl5_5),
% 0.22/0.59    inference(avatar_split_clause,[],[f139,f80,f142])).
% 0.22/0.59  fof(f139,plain,(
% 0.22/0.59    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl5_5),
% 0.22/0.59    inference(resolution,[],[f82,f53])).
% 0.22/0.59  fof(f146,plain,(
% 0.22/0.59    ~spl5_10 | ~spl5_2 | ~spl5_5),
% 0.22/0.59    inference(avatar_split_clause,[],[f131,f80,f65,f123])).
% 0.22/0.59  fof(f131,plain,(
% 0.22/0.59    ~v1_xboole_0(u1_struct_0(sK0)) | (~spl5_2 | ~spl5_5)),
% 0.22/0.59    inference(unit_resulting_resolution,[],[f67,f82,f56])).
% 0.22/0.59  fof(f56,plain,(
% 0.22/0.59    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f21])).
% 0.22/0.59  fof(f21,plain,(
% 0.22/0.59    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.22/0.59    inference(ennf_transformation,[],[f6])).
% 0.22/0.59  fof(f6,axiom,(
% 0.22/0.59    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 0.22/0.59  fof(f119,plain,(
% 0.22/0.59    spl5_9 | ~spl5_2),
% 0.22/0.59    inference(avatar_split_clause,[],[f111,f65,f116])).
% 0.22/0.59  fof(f111,plain,(
% 0.22/0.59    m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(sK1)) | ~spl5_2),
% 0.22/0.59    inference(unit_resulting_resolution,[],[f67,f57])).
% 0.22/0.59  fof(f98,plain,(
% 0.22/0.59    ~spl5_8),
% 0.22/0.59    inference(avatar_split_clause,[],[f35,f95])).
% 0.22/0.59  fof(f35,plain,(
% 0.22/0.59    ~v2_struct_0(sK0)),
% 0.22/0.59    inference(cnf_transformation,[],[f25])).
% 0.22/0.59  fof(f25,plain,(
% 0.22/0.59    ((k6_domain_1(u1_struct_0(sK0),sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) & r2_hidden(sK2,sK1) & m1_subset_1(sK2,u1_struct_0(sK0))) & v2_tex_2(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.22/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f24,f23,f22])).
% 0.22/0.59  fof(f22,plain,(
% 0.22/0.59    ? [X0] : (? [X1] : (? [X2] : (k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (k6_domain_1(u1_struct_0(sK0),X2) != k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(sK0))) & v2_tex_2(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.22/0.59    introduced(choice_axiom,[])).
% 0.22/0.59  fof(f23,plain,(
% 0.22/0.59    ? [X1] : (? [X2] : (k6_domain_1(u1_struct_0(sK0),X2) != k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(sK0))) & v2_tex_2(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (k6_domain_1(u1_struct_0(sK0),X2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2))) & r2_hidden(X2,sK1) & m1_subset_1(X2,u1_struct_0(sK0))) & v2_tex_2(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.59    introduced(choice_axiom,[])).
% 0.22/0.59  fof(f24,plain,(
% 0.22/0.59    ? [X2] : (k6_domain_1(u1_struct_0(sK0),X2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2))) & r2_hidden(X2,sK1) & m1_subset_1(X2,u1_struct_0(sK0))) => (k6_domain_1(u1_struct_0(sK0),sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) & r2_hidden(sK2,sK1) & m1_subset_1(sK2,u1_struct_0(sK0)))),
% 0.22/0.59    introduced(choice_axiom,[])).
% 0.22/0.59  fof(f12,plain,(
% 0.22/0.59    ? [X0] : (? [X1] : (? [X2] : (k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.59    inference(flattening,[],[f11])).
% 0.22/0.59  fof(f11,plain,(
% 0.22/0.59    ? [X0] : (? [X1] : ((? [X2] : ((k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & r2_hidden(X2,X1)) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.59    inference(ennf_transformation,[],[f10])).
% 0.22/0.59  fof(f10,negated_conjecture,(
% 0.22/0.59    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,X1) => k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))))))))),
% 0.22/0.59    inference(negated_conjecture,[],[f9])).
% 0.22/0.59  fof(f9,conjecture,(
% 0.22/0.59    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,X1) => k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))))))))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_tex_2)).
% 0.22/0.59  fof(f93,plain,(
% 0.22/0.59    spl5_7),
% 0.22/0.59    inference(avatar_split_clause,[],[f36,f90])).
% 0.22/0.59  fof(f36,plain,(
% 0.22/0.59    v2_pre_topc(sK0)),
% 0.22/0.59    inference(cnf_transformation,[],[f25])).
% 0.22/0.59  fof(f88,plain,(
% 0.22/0.59    spl5_6),
% 0.22/0.59    inference(avatar_split_clause,[],[f37,f85])).
% 0.22/0.59  fof(f37,plain,(
% 0.22/0.59    l1_pre_topc(sK0)),
% 0.22/0.59    inference(cnf_transformation,[],[f25])).
% 0.22/0.59  fof(f83,plain,(
% 0.22/0.59    spl5_5),
% 0.22/0.59    inference(avatar_split_clause,[],[f38,f80])).
% 0.22/0.59  fof(f38,plain,(
% 0.22/0.59    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.59    inference(cnf_transformation,[],[f25])).
% 0.22/0.59  fof(f78,plain,(
% 0.22/0.59    spl5_4),
% 0.22/0.59    inference(avatar_split_clause,[],[f39,f75])).
% 0.22/0.59  fof(f39,plain,(
% 0.22/0.59    v2_tex_2(sK1,sK0)),
% 0.22/0.59    inference(cnf_transformation,[],[f25])).
% 0.22/0.59  fof(f73,plain,(
% 0.22/0.59    spl5_3),
% 0.22/0.59    inference(avatar_split_clause,[],[f40,f70])).
% 0.22/0.59  fof(f40,plain,(
% 0.22/0.59    m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.22/0.59    inference(cnf_transformation,[],[f25])).
% 0.22/0.59  fof(f68,plain,(
% 0.22/0.59    spl5_2),
% 0.22/0.59    inference(avatar_split_clause,[],[f41,f65])).
% 0.22/0.59  fof(f41,plain,(
% 0.22/0.59    r2_hidden(sK2,sK1)),
% 0.22/0.59    inference(cnf_transformation,[],[f25])).
% 0.22/0.59  fof(f63,plain,(
% 0.22/0.59    ~spl5_1),
% 0.22/0.59    inference(avatar_split_clause,[],[f42,f60])).
% 0.22/0.59  fof(f42,plain,(
% 0.22/0.59    k6_domain_1(u1_struct_0(sK0),sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))),
% 0.22/0.59    inference(cnf_transformation,[],[f25])).
% 0.22/0.59  % SZS output end Proof for theBenchmark
% 0.22/0.59  % (1381)------------------------------
% 0.22/0.59  % (1381)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.59  % (1381)Termination reason: Refutation
% 0.22/0.59  
% 0.22/0.59  % (1381)Memory used [KB]: 6396
% 0.22/0.59  % (1381)Time elapsed: 0.151 s
% 0.22/0.59  % (1381)------------------------------
% 0.22/0.59  % (1381)------------------------------
% 0.22/0.59  % (1353)Success in time 0.228 s
%------------------------------------------------------------------------------
