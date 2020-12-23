%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1316+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:43 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 190 expanded)
%              Number of leaves         :   18 (  70 expanded)
%              Depth                    :   14
%              Number of atoms          :  349 ( 710 expanded)
%              Number of equality atoms :   11 (  42 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f120,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f34,f38,f42,f47,f51,f55,f63,f67,f71,f91,f95,f99,f105,f119])).

fof(f119,plain,
    ( ~ spl5_1
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_8
    | ~ spl5_10
    | spl5_11
    | ~ spl5_12
    | ~ spl5_13 ),
    inference(avatar_contradiction_clause,[],[f118])).

fof(f118,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_8
    | ~ spl5_10
    | spl5_11
    | ~ spl5_12
    | ~ spl5_13 ),
    inference(subsumption_resolution,[],[f117,f94])).

fof(f94,plain,
    ( ~ v3_pre_topc(sK4(sK2,sK1),sK2)
    | spl5_11 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl5_11
  <=> v3_pre_topc(sK4(sK2,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f117,plain,
    ( v3_pre_topc(sK4(sK2,sK1),sK2)
    | ~ spl5_1
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_8
    | ~ spl5_10
    | ~ spl5_12
    | ~ spl5_13 ),
    inference(subsumption_resolution,[],[f115,f46])).

fof(f46,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f45])).

fof(f45,plain,
    ( spl5_4
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f115,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v3_pre_topc(sK4(sK2,sK1),sK2)
    | ~ spl5_1
    | ~ spl5_5
    | ~ spl5_8
    | ~ spl5_10
    | ~ spl5_12
    | ~ spl5_13 ),
    inference(resolution,[],[f110,f98])).

fof(f98,plain,
    ( m1_subset_1(sK4(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl5_12
  <=> m1_subset_1(sK4(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f110,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK4(sK2,sK1),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_pre_topc(X0,sK0)
        | v3_pre_topc(sK4(sK2,sK1),X0) )
    | ~ spl5_1
    | ~ spl5_5
    | ~ spl5_8
    | ~ spl5_10
    | ~ spl5_13 ),
    inference(subsumption_resolution,[],[f109,f108])).

fof(f108,plain,
    ( v3_pre_topc(sK4(sK2,sK1),sK0)
    | ~ spl5_1
    | ~ spl5_5
    | ~ spl5_8
    | ~ spl5_10
    | ~ spl5_13 ),
    inference(subsumption_resolution,[],[f106,f90])).

fof(f90,plain,
    ( r2_hidden(sK4(sK2,sK1),sK1)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl5_10
  <=> r2_hidden(sK4(sK2,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f106,plain,
    ( ~ r2_hidden(sK4(sK2,sK1),sK1)
    | v3_pre_topc(sK4(sK2,sK1),sK0)
    | ~ spl5_1
    | ~ spl5_5
    | ~ spl5_8
    | ~ spl5_13 ),
    inference(resolution,[],[f104,f77])).

fof(f77,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X0,sK1)
        | v3_pre_topc(X0,sK0) )
    | ~ spl5_1
    | ~ spl5_5
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f76,f50])).

fof(f50,plain,
    ( v1_tops_2(sK1,sK0)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f49])).

fof(f49,plain,
    ( spl5_5
  <=> v1_tops_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f76,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X0,sK1)
        | v3_pre_topc(X0,sK0)
        | ~ v1_tops_2(sK1,sK0) )
    | ~ spl5_1
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f72,f33])).

fof(f33,plain,
    ( l1_pre_topc(sK0)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f32])).

fof(f32,plain,
    ( spl5_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f72,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X0,sK1)
        | v3_pre_topc(X0,sK0)
        | ~ v1_tops_2(sK1,sK0) )
    | ~ spl5_8 ),
    inference(resolution,[],[f66,f23])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X2,X1)
      | v3_pre_topc(X2,X0)
      | ~ v1_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r2_hidden(X2,X1)
                 => v3_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_2)).

fof(f66,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl5_8
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f104,plain,
    ( m1_subset_1(sK4(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl5_13
  <=> m1_subset_1(sK4(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f109,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | ~ v3_pre_topc(sK4(sK2,sK1),sK0)
        | ~ m1_subset_1(sK4(sK2,sK1),k1_zfmisc_1(u1_struct_0(X0)))
        | v3_pre_topc(sK4(sK2,sK1),X0) )
    | ~ spl5_1
    | ~ spl5_13 ),
    inference(subsumption_resolution,[],[f107,f33])).

fof(f107,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ v3_pre_topc(sK4(sK2,sK1),sK0)
        | ~ m1_subset_1(sK4(sK2,sK1),k1_zfmisc_1(u1_struct_0(X0)))
        | v3_pre_topc(sK4(sK2,sK1),X0) )
    | ~ spl5_13 ),
    inference(resolution,[],[f104,f29])).

fof(f29,plain,(
    ! [X2,X0,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | v3_pre_topc(X3,X2) ) ),
    inference(equality_resolution,[],[f22])).

fof(f22,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X2,X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | X1 != X3
      | v3_pre_topc(X3,X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v3_pre_topc(X3,X2)
                  | X1 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v3_pre_topc(X3,X2)
                  | X1 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( v3_pre_topc(X1,X0)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
                   => ( X1 = X3
                     => v3_pre_topc(X3,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_tops_2)).

fof(f105,plain,
    ( spl5_13
    | ~ spl5_1
    | ~ spl5_4
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f101,f97,f45,f32,f103])).

fof(f101,plain,
    ( m1_subset_1(sK4(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_1
    | ~ spl5_4
    | ~ spl5_12 ),
    inference(resolution,[],[f59,f98])).

fof(f59,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
        | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_1
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f57,f33])).

fof(f57,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
        | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_4 ),
    inference(resolution,[],[f46,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_pre_topc)).

fof(f99,plain,
    ( spl5_12
    | spl5_6
    | ~ spl5_7
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f83,f69,f61,f53,f97])).

fof(f53,plain,
    ( spl5_6
  <=> v1_tops_2(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f61,plain,
    ( spl5_7
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f69,plain,
    ( spl5_9
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f83,plain,
    ( m1_subset_1(sK4(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK2)))
    | spl5_6
    | ~ spl5_7
    | ~ spl5_9 ),
    inference(subsumption_resolution,[],[f82,f54])).

fof(f54,plain,
    ( ~ v1_tops_2(sK1,sK2)
    | spl5_6 ),
    inference(avatar_component_clause,[],[f53])).

fof(f82,plain,
    ( m1_subset_1(sK4(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_tops_2(sK1,sK2)
    | ~ spl5_7
    | ~ spl5_9 ),
    inference(subsumption_resolution,[],[f79,f62])).

fof(f62,plain,
    ( l1_pre_topc(sK2)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f61])).

fof(f79,plain,
    ( ~ l1_pre_topc(sK2)
    | m1_subset_1(sK4(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_tops_2(sK1,sK2)
    | ~ spl5_9 ),
    inference(resolution,[],[f70,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v1_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f70,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f69])).

fof(f95,plain,
    ( ~ spl5_11
    | spl5_6
    | ~ spl5_7
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f87,f69,f61,f53,f93])).

fof(f87,plain,
    ( ~ v3_pre_topc(sK4(sK2,sK1),sK2)
    | spl5_6
    | ~ spl5_7
    | ~ spl5_9 ),
    inference(subsumption_resolution,[],[f86,f54])).

fof(f86,plain,
    ( ~ v3_pre_topc(sK4(sK2,sK1),sK2)
    | v1_tops_2(sK1,sK2)
    | ~ spl5_7
    | ~ spl5_9 ),
    inference(subsumption_resolution,[],[f81,f62])).

fof(f81,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ v3_pre_topc(sK4(sK2,sK1),sK2)
    | v1_tops_2(sK1,sK2)
    | ~ spl5_9 ),
    inference(resolution,[],[f70,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | ~ v3_pre_topc(sK4(X0,X1),X0)
      | v1_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f91,plain,
    ( spl5_10
    | spl5_6
    | ~ spl5_7
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f85,f69,f61,f53,f89])).

fof(f85,plain,
    ( r2_hidden(sK4(sK2,sK1),sK1)
    | spl5_6
    | ~ spl5_7
    | ~ spl5_9 ),
    inference(subsumption_resolution,[],[f84,f54])).

fof(f84,plain,
    ( r2_hidden(sK4(sK2,sK1),sK1)
    | v1_tops_2(sK1,sK2)
    | ~ spl5_7
    | ~ spl5_9 ),
    inference(subsumption_resolution,[],[f80,f62])).

fof(f80,plain,
    ( ~ l1_pre_topc(sK2)
    | r2_hidden(sK4(sK2,sK1),sK1)
    | v1_tops_2(sK1,sK2)
    | ~ spl5_9 ),
    inference(resolution,[],[f70,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | r2_hidden(sK4(X0,X1),X1)
      | v1_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f71,plain,(
    spl5_9 ),
    inference(avatar_split_clause,[],[f30,f69])).

fof(f30,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
    inference(forward_demodulation,[],[f15,f16])).

fof(f16,plain,(
    sK1 = sK3 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v1_tops_2(X3,X2)
                  & X1 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) )
              & v1_tops_2(X1,X0)
              & m1_pre_topc(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v1_tops_2(X3,X2)
                  & X1 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) )
              & v1_tops_2(X1,X0)
              & m1_pre_topc(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ! [X2] :
                ( m1_pre_topc(X2,X0)
               => ( v1_tops_2(X1,X0)
                 => ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
                     => ( X1 = X3
                       => v1_tops_2(X3,X2) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( v1_tops_2(X1,X0)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
                   => ( X1 = X3
                     => v1_tops_2(X3,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tops_2)).

fof(f15,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f8])).

fof(f67,plain,(
    spl5_8 ),
    inference(avatar_split_clause,[],[f20,f65])).

fof(f20,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f8])).

fof(f63,plain,
    ( spl5_7
    | ~ spl5_1
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f58,f45,f32,f61])).

fof(f58,plain,
    ( l1_pre_topc(sK2)
    | ~ spl5_1
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f56,f33])).

fof(f56,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK2)
    | ~ spl5_4 ),
    inference(resolution,[],[f46,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f55,plain,
    ( ~ spl5_6
    | ~ spl5_2
    | spl5_3 ),
    inference(avatar_split_clause,[],[f43,f40,f36,f53])).

fof(f36,plain,
    ( spl5_2
  <=> sK1 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f40,plain,
    ( spl5_3
  <=> v1_tops_2(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f43,plain,
    ( ~ v1_tops_2(sK1,sK2)
    | ~ spl5_2
    | spl5_3 ),
    inference(forward_demodulation,[],[f41,f37])).

fof(f37,plain,
    ( sK1 = sK3
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f36])).

fof(f41,plain,
    ( ~ v1_tops_2(sK3,sK2)
    | spl5_3 ),
    inference(avatar_component_clause,[],[f40])).

fof(f51,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f19,f49])).

fof(f19,plain,(
    v1_tops_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f47,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f18,f45])).

fof(f18,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f42,plain,(
    ~ spl5_3 ),
    inference(avatar_split_clause,[],[f17,f40])).

fof(f17,plain,(
    ~ v1_tops_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f8])).

fof(f38,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f16,f36])).

fof(f34,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f21,f32])).

fof(f21,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f8])).

%------------------------------------------------------------------------------
