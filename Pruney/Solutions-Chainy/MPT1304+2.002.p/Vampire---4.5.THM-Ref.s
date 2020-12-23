%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:33 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 183 expanded)
%              Number of leaves         :   28 (  68 expanded)
%              Depth                    :   13
%              Number of atoms          :  331 ( 645 expanded)
%              Number of equality atoms :   24 (  51 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f329,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f77,f82,f87,f97,f110,f114,f121,f247,f265,f313,f319,f328])).

fof(f328,plain,(
    spl4_21 ),
    inference(avatar_contradiction_clause,[],[f325])).

fof(f325,plain,
    ( $false
    | spl4_21 ),
    inference(unit_resulting_resolution,[],[f71,f71,f312,f151])).

fof(f151,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(X2,k1_setfam_1(k2_tarski(X0,X3)))
      | r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f68,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_setfam_1(k2_tarski(X0,X2)),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f64,f65])).

fof(f65,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k3_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_xboole_1)).

fof(f312,plain,
    ( ~ r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK1)
    | spl4_21 ),
    inference(avatar_component_clause,[],[f310])).

fof(f310,plain,
    ( spl4_21
  <=> r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f71,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f319,plain,(
    spl4_20 ),
    inference(avatar_contradiction_clause,[],[f315])).

fof(f315,plain,
    ( $false
    | spl4_20 ),
    inference(unit_resulting_resolution,[],[f71,f71,f308,f63])).

fof(f308,plain,
    ( ~ r1_tarski(sK1,sK1)
    | spl4_20 ),
    inference(avatar_component_clause,[],[f306])).

fof(f306,plain,
    ( spl4_20
  <=> r1_tarski(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f313,plain,
    ( ~ spl4_20
    | ~ spl4_21
    | ~ spl4_8
    | spl4_15
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f303,f263,f244,f118,f310,f306])).

fof(f118,plain,
    ( spl4_8
  <=> r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f244,plain,
    ( spl4_15
  <=> v1_tops_2(k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,sK2))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f263,plain,
    ( spl4_16
  <=> ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | v1_tops_2(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f303,plain,
    ( ~ r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK1)
    | ~ r1_tarski(sK1,sK1)
    | ~ spl4_8
    | spl4_15
    | ~ spl4_16 ),
    inference(resolution,[],[f298,f246])).

fof(f246,plain,
    ( ~ v1_tops_2(k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,sK2))),sK0)
    | spl4_15 ),
    inference(avatar_component_clause,[],[f244])).

fof(f298,plain,
    ( ! [X0,X1] :
        ( v1_tops_2(k5_xboole_0(X0,X1),sK0)
        | ~ r1_tarski(X1,sK1)
        | ~ r1_tarski(X0,sK1) )
    | ~ spl4_8
    | ~ spl4_16 ),
    inference(resolution,[],[f296,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k5_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k5_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k5_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t110_xboole_1)).

fof(f296,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | v1_tops_2(X0,sK0) )
    | ~ spl4_8
    | ~ spl4_16 ),
    inference(duplicate_literal_removal,[],[f282])).

fof(f282,plain,
    ( ! [X0] :
        ( v1_tops_2(X0,sK0)
        | ~ r1_tarski(X0,sK1)
        | ~ r1_tarski(X0,sK1) )
    | ~ spl4_8
    | ~ spl4_16 ),
    inference(resolution,[],[f268,f139])).

fof(f139,plain,
    ( ! [X2] :
        ( r1_tarski(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X2,sK1) )
    | ~ spl4_8 ),
    inference(resolution,[],[f63,f120])).

fof(f120,plain,
    ( r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f118])).

fof(f268,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_tops_2(X0,sK0)
        | ~ r1_tarski(X0,sK1) )
    | ~ spl4_16 ),
    inference(resolution,[],[f264,f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f69,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f69,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK3(X0,X1),X0)
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( r1_tarski(sK3(X0,X1),X0)
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f39,f40])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK3(X0,X1),X0)
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( r1_tarski(sK3(X0,X1),X0)
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f264,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ r1_tarski(X0,sK1)
        | v1_tops_2(X0,sK0) )
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f263])).

fof(f265,plain,
    ( ~ spl4_1
    | spl4_16
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f259,f84,f79,f263,f74])).

fof(f74,plain,
    ( spl4_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f79,plain,
    ( spl4_2
  <=> v1_tops_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f84,plain,
    ( spl4_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f259,plain,
    ( ! [X0] :
        ( ~ v1_tops_2(sK1,sK0)
        | ~ r1_tarski(X0,sK1)
        | v1_tops_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ l1_pre_topc(sK0) )
    | ~ spl4_3 ),
    inference(resolution,[],[f50,f86])).

fof(f86,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f84])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ v1_tops_2(X2,X0)
      | ~ r1_tarski(X1,X2)
      | v1_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v1_tops_2(X1,X0)
              | ~ v1_tops_2(X2,X0)
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v1_tops_2(X1,X0)
              | ~ v1_tops_2(X2,X0)
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( ( v1_tops_2(X2,X0)
                  & r1_tarski(X1,X2) )
               => v1_tops_2(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_tops_2)).

fof(f247,plain,
    ( ~ spl4_3
    | ~ spl4_15
    | spl4_5 ),
    inference(avatar_split_clause,[],[f241,f94,f244,f84])).

fof(f94,plain,
    ( spl4_5
  <=> v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f241,plain,
    ( ~ v1_tops_2(k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,sK2))),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | spl4_5 ),
    inference(superposition,[],[f96,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f49,f66])).

fof(f66,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f61,f65])).

fof(f61,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f96,plain,
    ( ~ v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)
    | spl4_5 ),
    inference(avatar_component_clause,[],[f94])).

fof(f121,plain,
    ( spl4_8
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f115,f103,f118])).

fof(f103,plain,
    ( spl4_6
  <=> r2_hidden(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f115,plain,
    ( r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_6 ),
    inference(resolution,[],[f105,f70])).

fof(f70,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_zfmisc_1(X0))
      | r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f105,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f103])).

fof(f114,plain,(
    ~ spl4_7 ),
    inference(avatar_contradiction_clause,[],[f111])).

fof(f111,plain,
    ( $false
    | ~ spl4_7 ),
    inference(unit_resulting_resolution,[],[f57,f109])).

fof(f109,plain,
    ( v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl4_7
  <=> v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f57,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f110,plain,
    ( spl4_6
    | spl4_7
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f100,f84,f107,f103])).

fof(f100,plain,
    ( v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | r2_hidden(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl4_3 ),
    inference(resolution,[],[f51,f86])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
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
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f97,plain,(
    ~ spl4_5 ),
    inference(avatar_split_clause,[],[f48,f94])).

fof(f48,plain,(
    ~ v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,
    ( ~ v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)
    & v1_tops_2(sK1,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f36,f35,f34])).

fof(f34,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
                & v1_tops_2(X1,X0)
                & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X1,X2),sK0)
              & v1_tops_2(X1,sK0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X1,X2),sK0)
            & v1_tops_2(X1,sK0)
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
   => ( ? [X2] :
          ( ~ v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X2),sK0)
          & v1_tops_2(sK1,sK0)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
      & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X2] :
        ( ~ v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X2),sK0)
        & v1_tops_2(sK1,sK0)
        & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
   => ( ~ v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)
      & v1_tops_2(sK1,sK0)
      & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
              & v1_tops_2(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
              & v1_tops_2(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => ( v1_tops_2(X1,X0)
                 => v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( v1_tops_2(X1,X0)
               => v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_tops_2)).

fof(f87,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f45,f84])).

fof(f45,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f37])).

fof(f82,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f47,f79])).

fof(f47,plain,(
    v1_tops_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f77,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f44,f74])).

fof(f44,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f37])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:14:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (17530)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.50  % (17522)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.50  % (17507)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.51  % (17514)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.51  % (17513)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.51  % (17512)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.52  % (17511)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.52  % (17530)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f329,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(avatar_sat_refutation,[],[f77,f82,f87,f97,f110,f114,f121,f247,f265,f313,f319,f328])).
% 0.22/0.52  fof(f328,plain,(
% 0.22/0.52    spl4_21),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f325])).
% 0.22/0.52  fof(f325,plain,(
% 0.22/0.52    $false | spl4_21),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f71,f71,f312,f151])).
% 0.22/0.52  fof(f151,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (~r1_tarski(X2,k1_setfam_1(k2_tarski(X0,X3))) | r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.22/0.52    inference(resolution,[],[f68,f63])).
% 0.22/0.52  fof(f63,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f32])).
% 0.22/0.52  fof(f32,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.22/0.52    inference(flattening,[],[f31])).
% 0.22/0.52  fof(f31,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.22/0.52    inference(ennf_transformation,[],[f5])).
% 0.22/0.52  fof(f5,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.22/0.52  fof(f68,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (r1_tarski(k1_setfam_1(k2_tarski(X0,X2)),X1) | ~r1_tarski(X0,X1)) )),
% 0.22/0.52    inference(definition_unfolding,[],[f64,f65])).
% 0.22/0.52  fof(f65,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f15])).
% 0.22/0.52  fof(f15,axiom,(
% 0.22/0.52    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.22/0.52  fof(f64,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f33])).
% 0.22/0.52  fof(f33,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1))),
% 0.22/0.52    inference(ennf_transformation,[],[f3])).
% 0.22/0.52  fof(f3,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k3_xboole_0(X0,X2),X1))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_xboole_1)).
% 0.22/0.52  fof(f312,plain,(
% 0.22/0.52    ~r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK1) | spl4_21),
% 0.22/0.52    inference(avatar_component_clause,[],[f310])).
% 0.22/0.52  fof(f310,plain,(
% 0.22/0.52    spl4_21 <=> r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK1)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 0.22/0.52  fof(f71,plain,(
% 0.22/0.52    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.22/0.52    inference(equality_resolution,[],[f59])).
% 0.22/0.52  fof(f59,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.22/0.52    inference(cnf_transformation,[],[f43])).
% 0.22/0.52  fof(f43,plain,(
% 0.22/0.52    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.52    inference(flattening,[],[f42])).
% 0.22/0.52  fof(f42,plain,(
% 0.22/0.52    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.52    inference(nnf_transformation,[],[f1])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.52  fof(f319,plain,(
% 0.22/0.52    spl4_20),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f315])).
% 0.22/0.52  fof(f315,plain,(
% 0.22/0.52    $false | spl4_20),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f71,f71,f308,f63])).
% 0.22/0.52  fof(f308,plain,(
% 0.22/0.52    ~r1_tarski(sK1,sK1) | spl4_20),
% 0.22/0.52    inference(avatar_component_clause,[],[f306])).
% 0.22/0.52  fof(f306,plain,(
% 0.22/0.52    spl4_20 <=> r1_tarski(sK1,sK1)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 0.22/0.52  fof(f313,plain,(
% 0.22/0.52    ~spl4_20 | ~spl4_21 | ~spl4_8 | spl4_15 | ~spl4_16),
% 0.22/0.52    inference(avatar_split_clause,[],[f303,f263,f244,f118,f310,f306])).
% 0.22/0.52  fof(f118,plain,(
% 0.22/0.52    spl4_8 <=> r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.22/0.52  fof(f244,plain,(
% 0.22/0.52    spl4_15 <=> v1_tops_2(k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,sK2))),sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.22/0.52  fof(f263,plain,(
% 0.22/0.52    spl4_16 <=> ! [X0] : (~r1_tarski(X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v1_tops_2(X0,sK0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.22/0.52  fof(f303,plain,(
% 0.22/0.52    ~r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK1) | ~r1_tarski(sK1,sK1) | (~spl4_8 | spl4_15 | ~spl4_16)),
% 0.22/0.52    inference(resolution,[],[f298,f246])).
% 0.22/0.52  fof(f246,plain,(
% 0.22/0.52    ~v1_tops_2(k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,sK2))),sK0) | spl4_15),
% 0.22/0.52    inference(avatar_component_clause,[],[f244])).
% 0.22/0.52  fof(f298,plain,(
% 0.22/0.52    ( ! [X0,X1] : (v1_tops_2(k5_xboole_0(X0,X1),sK0) | ~r1_tarski(X1,sK1) | ~r1_tarski(X0,sK1)) ) | (~spl4_8 | ~spl4_16)),
% 0.22/0.52    inference(resolution,[],[f296,f62])).
% 0.22/0.52  fof(f62,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (r1_tarski(k5_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f30])).
% 0.22/0.52  fof(f30,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (r1_tarski(k5_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 0.22/0.52    inference(flattening,[],[f29])).
% 0.22/0.52  fof(f29,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (r1_tarski(k5_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 0.22/0.52    inference(ennf_transformation,[],[f4])).
% 0.22/0.52  fof(f4,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k5_xboole_0(X0,X2),X1))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t110_xboole_1)).
% 0.22/0.52  fof(f296,plain,(
% 0.22/0.52    ( ! [X0] : (~r1_tarski(X0,sK1) | v1_tops_2(X0,sK0)) ) | (~spl4_8 | ~spl4_16)),
% 0.22/0.52    inference(duplicate_literal_removal,[],[f282])).
% 0.22/0.52  fof(f282,plain,(
% 0.22/0.52    ( ! [X0] : (v1_tops_2(X0,sK0) | ~r1_tarski(X0,sK1) | ~r1_tarski(X0,sK1)) ) | (~spl4_8 | ~spl4_16)),
% 0.22/0.52    inference(resolution,[],[f268,f139])).
% 0.22/0.52  fof(f139,plain,(
% 0.22/0.52    ( ! [X2] : (r1_tarski(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X2,sK1)) ) | ~spl4_8),
% 0.22/0.52    inference(resolution,[],[f63,f120])).
% 0.22/0.52  fof(f120,plain,(
% 0.22/0.52    r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_8),
% 0.22/0.52    inference(avatar_component_clause,[],[f118])).
% 0.22/0.52  fof(f268,plain,(
% 0.22/0.52    ( ! [X0] : (~r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_tops_2(X0,sK0) | ~r1_tarski(X0,sK1)) ) | ~spl4_16),
% 0.22/0.52    inference(resolution,[],[f264,f98])).
% 0.22/0.52  fof(f98,plain,(
% 0.22/0.52    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.22/0.52    inference(resolution,[],[f69,f52])).
% 0.22/0.52  fof(f52,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f28])).
% 0.22/0.52  fof(f28,plain,(
% 0.22/0.52    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.22/0.52    inference(ennf_transformation,[],[f16])).
% 0.22/0.52  fof(f16,axiom,(
% 0.22/0.52    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).
% 0.22/0.52  fof(f69,plain,(
% 0.22/0.52    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 0.22/0.52    inference(equality_resolution,[],[f54])).
% 0.22/0.52  fof(f54,plain,(
% 0.22/0.52    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 0.22/0.52    inference(cnf_transformation,[],[f41])).
% 0.22/0.52  fof(f41,plain,(
% 0.22/0.52    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f39,f40])).
% 0.22/0.52  fof(f40,plain,(
% 0.22/0.52    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f39,plain,(
% 0.22/0.52    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.22/0.52    inference(rectify,[],[f38])).
% 0.22/0.52  fof(f38,plain,(
% 0.22/0.52    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.22/0.52    inference(nnf_transformation,[],[f12])).
% 0.22/0.52  fof(f12,axiom,(
% 0.22/0.52    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.22/0.52  fof(f264,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~r1_tarski(X0,sK1) | v1_tops_2(X0,sK0)) ) | ~spl4_16),
% 0.22/0.52    inference(avatar_component_clause,[],[f263])).
% 0.22/0.52  fof(f265,plain,(
% 0.22/0.52    ~spl4_1 | spl4_16 | ~spl4_2 | ~spl4_3),
% 0.22/0.52    inference(avatar_split_clause,[],[f259,f84,f79,f263,f74])).
% 0.22/0.52  fof(f74,plain,(
% 0.22/0.52    spl4_1 <=> l1_pre_topc(sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.52  fof(f79,plain,(
% 0.22/0.52    spl4_2 <=> v1_tops_2(sK1,sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.52  fof(f84,plain,(
% 0.22/0.52    spl4_3 <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.22/0.52  fof(f259,plain,(
% 0.22/0.52    ( ! [X0] : (~v1_tops_2(sK1,sK0) | ~r1_tarski(X0,sK1) | v1_tops_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~l1_pre_topc(sK0)) ) | ~spl4_3),
% 0.22/0.52    inference(resolution,[],[f50,f86])).
% 0.22/0.52  fof(f86,plain,(
% 0.22/0.52    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl4_3),
% 0.22/0.52    inference(avatar_component_clause,[],[f84])).
% 0.22/0.52  fof(f50,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_2(X2,X0) | ~r1_tarski(X1,X2) | v1_tops_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f25])).
% 0.22/0.52  fof(f25,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (! [X2] : (v1_tops_2(X1,X0) | ~v1_tops_2(X2,X0) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.22/0.52    inference(flattening,[],[f24])).
% 0.22/0.52  fof(f24,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (! [X2] : ((v1_tops_2(X1,X0) | (~v1_tops_2(X2,X0) | ~r1_tarski(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f18])).
% 0.22/0.52  fof(f18,axiom,(
% 0.22/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ((v1_tops_2(X2,X0) & r1_tarski(X1,X2)) => v1_tops_2(X1,X0)))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_tops_2)).
% 0.22/0.52  fof(f247,plain,(
% 0.22/0.52    ~spl4_3 | ~spl4_15 | spl4_5),
% 0.22/0.52    inference(avatar_split_clause,[],[f241,f94,f244,f84])).
% 0.22/0.52  fof(f94,plain,(
% 0.22/0.52    spl4_5 <=> v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.22/0.52  fof(f241,plain,(
% 0.22/0.52    ~v1_tops_2(k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,sK2))),sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | spl4_5),
% 0.22/0.52    inference(superposition,[],[f96,f67])).
% 0.22/0.52  fof(f67,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.52    inference(definition_unfolding,[],[f49,f66])).
% 0.22/0.52  fof(f66,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 0.22/0.52    inference(definition_unfolding,[],[f61,f65])).
% 0.22/0.52  fof(f61,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f2])).
% 0.22/0.52  fof(f2,axiom,(
% 0.22/0.52    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.22/0.52  fof(f49,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f23])).
% 0.22/0.52  fof(f23,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f14])).
% 0.22/0.52  fof(f14,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 0.22/0.52  fof(f96,plain,(
% 0.22/0.52    ~v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) | spl4_5),
% 0.22/0.52    inference(avatar_component_clause,[],[f94])).
% 0.22/0.52  fof(f121,plain,(
% 0.22/0.52    spl4_8 | ~spl4_6),
% 0.22/0.52    inference(avatar_split_clause,[],[f115,f103,f118])).
% 0.22/0.52  fof(f103,plain,(
% 0.22/0.52    spl4_6 <=> r2_hidden(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.22/0.52  fof(f115,plain,(
% 0.22/0.52    r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_6),
% 0.22/0.52    inference(resolution,[],[f105,f70])).
% 0.22/0.52  fof(f70,plain,(
% 0.22/0.52    ( ! [X0,X3] : (~r2_hidden(X3,k1_zfmisc_1(X0)) | r1_tarski(X3,X0)) )),
% 0.22/0.52    inference(equality_resolution,[],[f53])).
% 0.22/0.52  fof(f53,plain,(
% 0.22/0.52    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.22/0.52    inference(cnf_transformation,[],[f41])).
% 0.22/0.52  fof(f105,plain,(
% 0.22/0.52    r2_hidden(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl4_6),
% 0.22/0.52    inference(avatar_component_clause,[],[f103])).
% 0.22/0.52  fof(f114,plain,(
% 0.22/0.52    ~spl4_7),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f111])).
% 0.22/0.52  fof(f111,plain,(
% 0.22/0.52    $false | ~spl4_7),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f57,f109])).
% 0.22/0.52  fof(f109,plain,(
% 0.22/0.52    v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl4_7),
% 0.22/0.52    inference(avatar_component_clause,[],[f107])).
% 0.22/0.52  fof(f107,plain,(
% 0.22/0.52    spl4_7 <=> v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.22/0.52  fof(f57,plain,(
% 0.22/0.52    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f13])).
% 0.22/0.52  fof(f13,axiom,(
% 0.22/0.52    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).
% 0.22/0.52  fof(f110,plain,(
% 0.22/0.52    spl4_6 | spl4_7 | ~spl4_3),
% 0.22/0.52    inference(avatar_split_clause,[],[f100,f84,f107,f103])).
% 0.22/0.52  fof(f100,plain,(
% 0.22/0.52    v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | r2_hidden(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl4_3),
% 0.22/0.52    inference(resolution,[],[f51,f86])).
% 0.22/0.52  fof(f51,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f27])).
% 0.22/0.52  fof(f27,plain,(
% 0.22/0.52    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.22/0.52    inference(flattening,[],[f26])).
% 0.22/0.52  fof(f26,plain,(
% 0.22/0.52    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.22/0.52    inference(ennf_transformation,[],[f17])).
% 0.22/0.52  fof(f17,axiom,(
% 0.22/0.52    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.22/0.52  fof(f97,plain,(
% 0.22/0.52    ~spl4_5),
% 0.22/0.52    inference(avatar_split_clause,[],[f48,f94])).
% 0.22/0.52  fof(f48,plain,(
% 0.22/0.52    ~v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f37])).
% 0.22/0.52  fof(f37,plain,(
% 0.22/0.52    ((~v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) & v1_tops_2(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_pre_topc(sK0)),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f36,f35,f34])).
% 0.22/0.52  fof(f34,plain,(
% 0.22/0.52    ? [X0] : (? [X1] : (? [X2] : (~v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v1_tops_2(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X1,X2),sK0) & v1_tops_2(X1,sK0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_pre_topc(sK0))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f35,plain,(
% 0.22/0.52    ? [X1] : (? [X2] : (~v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X1,X2),sK0) & v1_tops_2(X1,sK0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) => (? [X2] : (~v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X2),sK0) & v1_tops_2(sK1,sK0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f36,plain,(
% 0.22/0.52    ? [X2] : (~v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X2),sK0) & v1_tops_2(sK1,sK0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) => (~v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) & v1_tops_2(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f22,plain,(
% 0.22/0.52    ? [X0] : (? [X1] : (? [X2] : (~v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v1_tops_2(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 0.22/0.52    inference(flattening,[],[f21])).
% 0.22/0.52  fof(f21,plain,(
% 0.22/0.52    ? [X0] : (? [X1] : (? [X2] : ((~v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v1_tops_2(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f20])).
% 0.22/0.52  fof(f20,negated_conjecture,(
% 0.22/0.52    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_2(X1,X0) => v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)))))),
% 0.22/0.52    inference(negated_conjecture,[],[f19])).
% 0.22/0.52  fof(f19,conjecture,(
% 0.22/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_2(X1,X0) => v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_tops_2)).
% 0.22/0.52  fof(f87,plain,(
% 0.22/0.52    spl4_3),
% 0.22/0.52    inference(avatar_split_clause,[],[f45,f84])).
% 0.22/0.52  fof(f45,plain,(
% 0.22/0.52    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.52    inference(cnf_transformation,[],[f37])).
% 0.22/0.52  fof(f82,plain,(
% 0.22/0.52    spl4_2),
% 0.22/0.52    inference(avatar_split_clause,[],[f47,f79])).
% 0.22/0.52  fof(f47,plain,(
% 0.22/0.52    v1_tops_2(sK1,sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f37])).
% 0.22/0.52  fof(f77,plain,(
% 0.22/0.52    spl4_1),
% 0.22/0.52    inference(avatar_split_clause,[],[f44,f74])).
% 0.22/0.52  fof(f44,plain,(
% 0.22/0.52    l1_pre_topc(sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f37])).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (17530)------------------------------
% 0.22/0.52  % (17530)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (17530)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (17530)Memory used [KB]: 10874
% 0.22/0.52  % (17530)Time elapsed: 0.062 s
% 0.22/0.52  % (17530)------------------------------
% 0.22/0.52  % (17530)------------------------------
% 0.22/0.52  % (17529)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.53  % (17506)Success in time 0.164 s
%------------------------------------------------------------------------------
