%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:49 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 187 expanded)
%              Number of leaves         :   18 (  68 expanded)
%              Depth                    :   14
%              Number of atoms          :  342 ( 697 expanded)
%              Number of equality atoms :   11 (  42 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f121,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f35,f39,f43,f48,f52,f56,f62,f66,f70,f90,f94,f99,f106,f120])).

fof(f120,plain,
    ( ~ spl5_1
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_8
    | ~ spl5_10
    | spl5_11
    | ~ spl5_12
    | ~ spl5_13 ),
    inference(avatar_contradiction_clause,[],[f119])).

fof(f119,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_8
    | ~ spl5_10
    | spl5_11
    | ~ spl5_12
    | ~ spl5_13 ),
    inference(subsumption_resolution,[],[f118,f93])).

fof(f93,plain,
    ( ~ v4_pre_topc(sK4(sK2,sK1),sK2)
    | spl5_11 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl5_11
  <=> v4_pre_topc(sK4(sK2,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f118,plain,
    ( v4_pre_topc(sK4(sK2,sK1),sK2)
    | ~ spl5_1
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_8
    | ~ spl5_10
    | ~ spl5_12
    | ~ spl5_13 ),
    inference(subsumption_resolution,[],[f116,f47])).

fof(f47,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f46])).

fof(f46,plain,
    ( spl5_4
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f116,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v4_pre_topc(sK4(sK2,sK1),sK2)
    | ~ spl5_1
    | ~ spl5_5
    | ~ spl5_8
    | ~ spl5_10
    | ~ spl5_12
    | ~ spl5_13 ),
    inference(resolution,[],[f111,f98])).

fof(f98,plain,
    ( m1_subset_1(sK4(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl5_12
  <=> m1_subset_1(sK4(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f111,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK4(sK2,sK1),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_pre_topc(X0,sK0)
        | v4_pre_topc(sK4(sK2,sK1),X0) )
    | ~ spl5_1
    | ~ spl5_5
    | ~ spl5_8
    | ~ spl5_10
    | ~ spl5_13 ),
    inference(subsumption_resolution,[],[f110,f109])).

fof(f109,plain,
    ( v4_pre_topc(sK4(sK2,sK1),sK0)
    | ~ spl5_1
    | ~ spl5_5
    | ~ spl5_8
    | ~ spl5_10
    | ~ spl5_13 ),
    inference(subsumption_resolution,[],[f107,f89])).

fof(f89,plain,
    ( r2_hidden(sK4(sK2,sK1),sK1)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl5_10
  <=> r2_hidden(sK4(sK2,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f107,plain,
    ( ~ r2_hidden(sK4(sK2,sK1),sK1)
    | v4_pre_topc(sK4(sK2,sK1),sK0)
    | ~ spl5_1
    | ~ spl5_5
    | ~ spl5_8
    | ~ spl5_13 ),
    inference(resolution,[],[f105,f76])).

fof(f76,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X0,sK1)
        | v4_pre_topc(X0,sK0) )
    | ~ spl5_1
    | ~ spl5_5
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f75,f51])).

fof(f51,plain,
    ( v2_tops_2(sK1,sK0)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl5_5
  <=> v2_tops_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f75,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X0,sK1)
        | v4_pre_topc(X0,sK0)
        | ~ v2_tops_2(sK1,sK0) )
    | ~ spl5_1
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f71,f34])).

fof(f34,plain,
    ( l1_pre_topc(sK0)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f33])).

fof(f33,plain,
    ( spl5_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f71,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X0,sK1)
        | v4_pre_topc(X0,sK0)
        | ~ v2_tops_2(sK1,sK0) )
    | ~ spl5_8 ),
    inference(resolution,[],[f65,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X2,X1)
      | v4_pre_topc(X2,X0)
      | ~ v2_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_2(X1,X0)
          <=> ! [X2] :
                ( v4_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_2(X1,X0)
          <=> ! [X2] :
                ( v4_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v2_tops_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r2_hidden(X2,X1)
                 => v4_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_2)).

fof(f65,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl5_8
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f105,plain,
    ( m1_subset_1(sK4(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl5_13
  <=> m1_subset_1(sK4(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f110,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | ~ v4_pre_topc(sK4(sK2,sK1),sK0)
        | ~ m1_subset_1(sK4(sK2,sK1),k1_zfmisc_1(u1_struct_0(X0)))
        | v4_pre_topc(sK4(sK2,sK1),X0) )
    | ~ spl5_1
    | ~ spl5_13 ),
    inference(subsumption_resolution,[],[f108,f34])).

fof(f108,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ v4_pre_topc(sK4(sK2,sK1),sK0)
        | ~ m1_subset_1(sK4(sK2,sK1),k1_zfmisc_1(u1_struct_0(X0)))
        | v4_pre_topc(sK4(sK2,sK1),X0) )
    | ~ spl5_13 ),
    inference(resolution,[],[f105,f30])).

fof(f30,plain,(
    ! [X2,X0,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ v4_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | v4_pre_topc(X3,X2) ) ),
    inference(equality_resolution,[],[f23])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X2,X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | X1 != X3
      | v4_pre_topc(X3,X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v4_pre_topc(X3,X2)
                  | X1 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              | ~ v4_pre_topc(X1,X0)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v4_pre_topc(X3,X2)
                  | X1 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              | ~ v4_pre_topc(X1,X0)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( v4_pre_topc(X1,X0)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
                   => ( X1 = X3
                     => v4_pre_topc(X3,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_tops_2)).

fof(f106,plain,
    ( spl5_13
    | ~ spl5_8
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f101,f88,f64,f104])).

fof(f101,plain,
    ( m1_subset_1(sK4(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_8
    | ~ spl5_10 ),
    inference(resolution,[],[f95,f65])).

fof(f95,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(X0))
        | m1_subset_1(sK4(sK2,sK1),X0) )
    | ~ spl5_10 ),
    inference(resolution,[],[f89,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f99,plain,
    ( spl5_12
    | spl5_6
    | ~ spl5_7
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f82,f68,f60,f54,f97])).

fof(f54,plain,
    ( spl5_6
  <=> v2_tops_2(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f60,plain,
    ( spl5_7
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f68,plain,
    ( spl5_9
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f82,plain,
    ( m1_subset_1(sK4(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK2)))
    | spl5_6
    | ~ spl5_7
    | ~ spl5_9 ),
    inference(subsumption_resolution,[],[f81,f55])).

fof(f55,plain,
    ( ~ v2_tops_2(sK1,sK2)
    | spl5_6 ),
    inference(avatar_component_clause,[],[f54])).

fof(f81,plain,
    ( m1_subset_1(sK4(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_tops_2(sK1,sK2)
    | ~ spl5_7
    | ~ spl5_9 ),
    inference(subsumption_resolution,[],[f78,f61])).

fof(f61,plain,
    ( l1_pre_topc(sK2)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f60])).

fof(f78,plain,
    ( ~ l1_pre_topc(sK2)
    | m1_subset_1(sK4(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_tops_2(sK1,sK2)
    | ~ spl5_9 ),
    inference(resolution,[],[f69,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f69,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f68])).

fof(f94,plain,
    ( ~ spl5_11
    | spl5_6
    | ~ spl5_7
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f86,f68,f60,f54,f92])).

fof(f86,plain,
    ( ~ v4_pre_topc(sK4(sK2,sK1),sK2)
    | spl5_6
    | ~ spl5_7
    | ~ spl5_9 ),
    inference(subsumption_resolution,[],[f85,f55])).

fof(f85,plain,
    ( ~ v4_pre_topc(sK4(sK2,sK1),sK2)
    | v2_tops_2(sK1,sK2)
    | ~ spl5_7
    | ~ spl5_9 ),
    inference(subsumption_resolution,[],[f80,f61])).

fof(f80,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ v4_pre_topc(sK4(sK2,sK1),sK2)
    | v2_tops_2(sK1,sK2)
    | ~ spl5_9 ),
    inference(resolution,[],[f69,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(sK4(X0,X1),X0)
      | v2_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f90,plain,
    ( spl5_10
    | spl5_6
    | ~ spl5_7
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f84,f68,f60,f54,f88])).

fof(f84,plain,
    ( r2_hidden(sK4(sK2,sK1),sK1)
    | spl5_6
    | ~ spl5_7
    | ~ spl5_9 ),
    inference(subsumption_resolution,[],[f83,f55])).

fof(f83,plain,
    ( r2_hidden(sK4(sK2,sK1),sK1)
    | v2_tops_2(sK1,sK2)
    | ~ spl5_7
    | ~ spl5_9 ),
    inference(subsumption_resolution,[],[f79,f61])).

fof(f79,plain,
    ( ~ l1_pre_topc(sK2)
    | r2_hidden(sK4(sK2,sK1),sK1)
    | v2_tops_2(sK1,sK2)
    | ~ spl5_9 ),
    inference(resolution,[],[f69,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | r2_hidden(sK4(X0,X1),X1)
      | v2_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f70,plain,(
    spl5_9 ),
    inference(avatar_split_clause,[],[f31,f68])).

fof(f31,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
    inference(forward_demodulation,[],[f16,f17])).

fof(f17,plain,(
    sK1 = sK3 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v2_tops_2(X3,X2)
                  & X1 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) )
              & v2_tops_2(X1,X0)
              & m1_pre_topc(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v2_tops_2(X3,X2)
                  & X1 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) )
              & v2_tops_2(X1,X0)
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
               => ( v2_tops_2(X1,X0)
                 => ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
                     => ( X1 = X3
                       => v2_tops_2(X3,X2) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( v2_tops_2(X1,X0)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
                   => ( X1 = X3
                     => v2_tops_2(X3,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_tops_2)).

fof(f16,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f8])).

fof(f66,plain,(
    spl5_8 ),
    inference(avatar_split_clause,[],[f21,f64])).

fof(f21,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f8])).

fof(f62,plain,
    ( spl5_7
    | ~ spl5_1
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f58,f46,f33,f60])).

fof(f58,plain,
    ( l1_pre_topc(sK2)
    | ~ spl5_1
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f57,f34])).

fof(f57,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK2)
    | ~ spl5_4 ),
    inference(resolution,[],[f47,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
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

fof(f56,plain,
    ( ~ spl5_6
    | ~ spl5_2
    | spl5_3 ),
    inference(avatar_split_clause,[],[f44,f41,f37,f54])).

fof(f37,plain,
    ( spl5_2
  <=> sK1 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f41,plain,
    ( spl5_3
  <=> v2_tops_2(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f44,plain,
    ( ~ v2_tops_2(sK1,sK2)
    | ~ spl5_2
    | spl5_3 ),
    inference(forward_demodulation,[],[f42,f38])).

fof(f38,plain,
    ( sK1 = sK3
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f37])).

fof(f42,plain,
    ( ~ v2_tops_2(sK3,sK2)
    | spl5_3 ),
    inference(avatar_component_clause,[],[f41])).

fof(f52,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f20,f50])).

fof(f20,plain,(
    v2_tops_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f48,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f19,f46])).

fof(f19,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f43,plain,(
    ~ spl5_3 ),
    inference(avatar_split_clause,[],[f18,f41])).

fof(f18,plain,(
    ~ v2_tops_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f8])).

fof(f39,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f17,f37])).

fof(f35,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f22,f33])).

fof(f22,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:45:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.44  % (21591)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.47  % (21584)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.47  % (21584)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f121,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(avatar_sat_refutation,[],[f35,f39,f43,f48,f52,f56,f62,f66,f70,f90,f94,f99,f106,f120])).
% 0.20/0.47  fof(f120,plain,(
% 0.20/0.47    ~spl5_1 | ~spl5_4 | ~spl5_5 | ~spl5_8 | ~spl5_10 | spl5_11 | ~spl5_12 | ~spl5_13),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f119])).
% 0.20/0.47  fof(f119,plain,(
% 0.20/0.47    $false | (~spl5_1 | ~spl5_4 | ~spl5_5 | ~spl5_8 | ~spl5_10 | spl5_11 | ~spl5_12 | ~spl5_13)),
% 0.20/0.47    inference(subsumption_resolution,[],[f118,f93])).
% 0.20/0.47  fof(f93,plain,(
% 0.20/0.47    ~v4_pre_topc(sK4(sK2,sK1),sK2) | spl5_11),
% 0.20/0.47    inference(avatar_component_clause,[],[f92])).
% 0.20/0.47  fof(f92,plain,(
% 0.20/0.47    spl5_11 <=> v4_pre_topc(sK4(sK2,sK1),sK2)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.20/0.47  fof(f118,plain,(
% 0.20/0.47    v4_pre_topc(sK4(sK2,sK1),sK2) | (~spl5_1 | ~spl5_4 | ~spl5_5 | ~spl5_8 | ~spl5_10 | ~spl5_12 | ~spl5_13)),
% 0.20/0.47    inference(subsumption_resolution,[],[f116,f47])).
% 0.20/0.47  fof(f47,plain,(
% 0.20/0.47    m1_pre_topc(sK2,sK0) | ~spl5_4),
% 0.20/0.47    inference(avatar_component_clause,[],[f46])).
% 0.20/0.47  fof(f46,plain,(
% 0.20/0.47    spl5_4 <=> m1_pre_topc(sK2,sK0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.20/0.47  fof(f116,plain,(
% 0.20/0.47    ~m1_pre_topc(sK2,sK0) | v4_pre_topc(sK4(sK2,sK1),sK2) | (~spl5_1 | ~spl5_5 | ~spl5_8 | ~spl5_10 | ~spl5_12 | ~spl5_13)),
% 0.20/0.47    inference(resolution,[],[f111,f98])).
% 0.20/0.47  fof(f98,plain,(
% 0.20/0.47    m1_subset_1(sK4(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK2))) | ~spl5_12),
% 0.20/0.47    inference(avatar_component_clause,[],[f97])).
% 0.20/0.47  fof(f97,plain,(
% 0.20/0.47    spl5_12 <=> m1_subset_1(sK4(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.20/0.47  fof(f111,plain,(
% 0.20/0.47    ( ! [X0] : (~m1_subset_1(sK4(sK2,sK1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X0,sK0) | v4_pre_topc(sK4(sK2,sK1),X0)) ) | (~spl5_1 | ~spl5_5 | ~spl5_8 | ~spl5_10 | ~spl5_13)),
% 0.20/0.47    inference(subsumption_resolution,[],[f110,f109])).
% 0.20/0.47  fof(f109,plain,(
% 0.20/0.47    v4_pre_topc(sK4(sK2,sK1),sK0) | (~spl5_1 | ~spl5_5 | ~spl5_8 | ~spl5_10 | ~spl5_13)),
% 0.20/0.47    inference(subsumption_resolution,[],[f107,f89])).
% 0.20/0.47  fof(f89,plain,(
% 0.20/0.47    r2_hidden(sK4(sK2,sK1),sK1) | ~spl5_10),
% 0.20/0.47    inference(avatar_component_clause,[],[f88])).
% 0.20/0.47  fof(f88,plain,(
% 0.20/0.47    spl5_10 <=> r2_hidden(sK4(sK2,sK1),sK1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.20/0.47  fof(f107,plain,(
% 0.20/0.47    ~r2_hidden(sK4(sK2,sK1),sK1) | v4_pre_topc(sK4(sK2,sK1),sK0) | (~spl5_1 | ~spl5_5 | ~spl5_8 | ~spl5_13)),
% 0.20/0.47    inference(resolution,[],[f105,f76])).
% 0.20/0.47  fof(f76,plain,(
% 0.20/0.47    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X0,sK1) | v4_pre_topc(X0,sK0)) ) | (~spl5_1 | ~spl5_5 | ~spl5_8)),
% 0.20/0.47    inference(subsumption_resolution,[],[f75,f51])).
% 0.20/0.47  fof(f51,plain,(
% 0.20/0.47    v2_tops_2(sK1,sK0) | ~spl5_5),
% 0.20/0.47    inference(avatar_component_clause,[],[f50])).
% 0.20/0.47  fof(f50,plain,(
% 0.20/0.47    spl5_5 <=> v2_tops_2(sK1,sK0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.20/0.47  fof(f75,plain,(
% 0.20/0.47    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X0,sK1) | v4_pre_topc(X0,sK0) | ~v2_tops_2(sK1,sK0)) ) | (~spl5_1 | ~spl5_8)),
% 0.20/0.47    inference(subsumption_resolution,[],[f71,f34])).
% 0.20/0.47  fof(f34,plain,(
% 0.20/0.47    l1_pre_topc(sK0) | ~spl5_1),
% 0.20/0.47    inference(avatar_component_clause,[],[f33])).
% 0.20/0.47  fof(f33,plain,(
% 0.20/0.47    spl5_1 <=> l1_pre_topc(sK0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.20/0.47  fof(f71,plain,(
% 0.20/0.47    ( ! [X0] : (~l1_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X0,sK1) | v4_pre_topc(X0,sK0) | ~v2_tops_2(sK1,sK0)) ) | ~spl5_8),
% 0.20/0.47    inference(resolution,[],[f65,f24])).
% 0.20/0.47  fof(f24,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X2,X1) | v4_pre_topc(X2,X0) | ~v2_tops_2(X1,X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f12])).
% 0.20/0.47  fof(f12,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : ((v2_tops_2(X1,X0) <=> ! [X2] : (v4_pre_topc(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.20/0.47    inference(flattening,[],[f11])).
% 0.20/0.47  fof(f11,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : ((v2_tops_2(X1,X0) <=> ! [X2] : ((v4_pre_topc(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f3])).
% 0.20/0.47  fof(f3,axiom,(
% 0.20/0.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v2_tops_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X2,X1) => v4_pre_topc(X2,X0))))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_2)).
% 0.20/0.47  fof(f65,plain,(
% 0.20/0.47    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl5_8),
% 0.20/0.47    inference(avatar_component_clause,[],[f64])).
% 0.20/0.47  fof(f64,plain,(
% 0.20/0.47    spl5_8 <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.20/0.47  fof(f105,plain,(
% 0.20/0.47    m1_subset_1(sK4(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_13),
% 0.20/0.47    inference(avatar_component_clause,[],[f104])).
% 0.20/0.47  fof(f104,plain,(
% 0.20/0.47    spl5_13 <=> m1_subset_1(sK4(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.20/0.47  fof(f110,plain,(
% 0.20/0.47    ( ! [X0] : (~m1_pre_topc(X0,sK0) | ~v4_pre_topc(sK4(sK2,sK1),sK0) | ~m1_subset_1(sK4(sK2,sK1),k1_zfmisc_1(u1_struct_0(X0))) | v4_pre_topc(sK4(sK2,sK1),X0)) ) | (~spl5_1 | ~spl5_13)),
% 0.20/0.47    inference(subsumption_resolution,[],[f108,f34])).
% 0.20/0.47  fof(f108,plain,(
% 0.20/0.47    ( ! [X0] : (~l1_pre_topc(sK0) | ~m1_pre_topc(X0,sK0) | ~v4_pre_topc(sK4(sK2,sK1),sK0) | ~m1_subset_1(sK4(sK2,sK1),k1_zfmisc_1(u1_struct_0(X0))) | v4_pre_topc(sK4(sK2,sK1),X0)) ) | ~spl5_13),
% 0.20/0.47    inference(resolution,[],[f105,f30])).
% 0.20/0.47  fof(f30,plain,(
% 0.20/0.47    ( ! [X2,X0,X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~m1_pre_topc(X2,X0) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | v4_pre_topc(X3,X2)) )),
% 0.20/0.47    inference(equality_resolution,[],[f23])).
% 0.20/0.47  fof(f23,plain,(
% 0.20/0.47    ( ! [X2,X0,X3,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X2,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | X1 != X3 | v4_pre_topc(X3,X2)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f10])).
% 0.20/0.47  fof(f10,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (v4_pre_topc(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) | ~v4_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.47    inference(flattening,[],[f9])).
% 0.20/0.47  fof(f9,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : ((v4_pre_topc(X3,X2) | X1 != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) | ~v4_pre_topc(X1,X0)) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f4])).
% 0.20/0.47  fof(f4,axiom,(
% 0.20/0.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_pre_topc(X2,X0) => (v4_pre_topc(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) => (X1 = X3 => v4_pre_topc(X3,X2)))))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_tops_2)).
% 0.20/0.47  fof(f106,plain,(
% 0.20/0.47    spl5_13 | ~spl5_8 | ~spl5_10),
% 0.20/0.47    inference(avatar_split_clause,[],[f101,f88,f64,f104])).
% 0.20/0.47  fof(f101,plain,(
% 0.20/0.47    m1_subset_1(sK4(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl5_8 | ~spl5_10)),
% 0.20/0.47    inference(resolution,[],[f95,f65])).
% 0.20/0.47  fof(f95,plain,(
% 0.20/0.47    ( ! [X0] : (~m1_subset_1(sK1,k1_zfmisc_1(X0)) | m1_subset_1(sK4(sK2,sK1),X0)) ) | ~spl5_10),
% 0.20/0.47    inference(resolution,[],[f89,f29])).
% 0.20/0.47  fof(f29,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f15])).
% 0.20/0.47  fof(f15,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.20/0.47    inference(flattening,[],[f14])).
% 0.20/0.47  fof(f14,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.20/0.47    inference(ennf_transformation,[],[f1])).
% 0.20/0.47  fof(f1,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 0.20/0.47  fof(f99,plain,(
% 0.20/0.47    spl5_12 | spl5_6 | ~spl5_7 | ~spl5_9),
% 0.20/0.47    inference(avatar_split_clause,[],[f82,f68,f60,f54,f97])).
% 0.20/0.47  fof(f54,plain,(
% 0.20/0.47    spl5_6 <=> v2_tops_2(sK1,sK2)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.20/0.47  fof(f60,plain,(
% 0.20/0.47    spl5_7 <=> l1_pre_topc(sK2)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.20/0.47  fof(f68,plain,(
% 0.20/0.47    spl5_9 <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.20/0.47  fof(f82,plain,(
% 0.20/0.47    m1_subset_1(sK4(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK2))) | (spl5_6 | ~spl5_7 | ~spl5_9)),
% 0.20/0.47    inference(subsumption_resolution,[],[f81,f55])).
% 0.20/0.47  fof(f55,plain,(
% 0.20/0.47    ~v2_tops_2(sK1,sK2) | spl5_6),
% 0.20/0.47    inference(avatar_component_clause,[],[f54])).
% 0.20/0.47  fof(f81,plain,(
% 0.20/0.47    m1_subset_1(sK4(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK2))) | v2_tops_2(sK1,sK2) | (~spl5_7 | ~spl5_9)),
% 0.20/0.47    inference(subsumption_resolution,[],[f78,f61])).
% 0.20/0.47  fof(f61,plain,(
% 0.20/0.47    l1_pre_topc(sK2) | ~spl5_7),
% 0.20/0.47    inference(avatar_component_clause,[],[f60])).
% 0.20/0.47  fof(f78,plain,(
% 0.20/0.47    ~l1_pre_topc(sK2) | m1_subset_1(sK4(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK2))) | v2_tops_2(sK1,sK2) | ~spl5_9),
% 0.20/0.47    inference(resolution,[],[f69,f25])).
% 0.20/0.47  fof(f25,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | v2_tops_2(X1,X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f12])).
% 0.20/0.47  fof(f69,plain,(
% 0.20/0.47    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) | ~spl5_9),
% 0.20/0.47    inference(avatar_component_clause,[],[f68])).
% 0.20/0.47  fof(f94,plain,(
% 0.20/0.47    ~spl5_11 | spl5_6 | ~spl5_7 | ~spl5_9),
% 0.20/0.47    inference(avatar_split_clause,[],[f86,f68,f60,f54,f92])).
% 0.20/0.47  fof(f86,plain,(
% 0.20/0.47    ~v4_pre_topc(sK4(sK2,sK1),sK2) | (spl5_6 | ~spl5_7 | ~spl5_9)),
% 0.20/0.47    inference(subsumption_resolution,[],[f85,f55])).
% 0.20/0.47  fof(f85,plain,(
% 0.20/0.47    ~v4_pre_topc(sK4(sK2,sK1),sK2) | v2_tops_2(sK1,sK2) | (~spl5_7 | ~spl5_9)),
% 0.20/0.47    inference(subsumption_resolution,[],[f80,f61])).
% 0.20/0.47  fof(f80,plain,(
% 0.20/0.47    ~l1_pre_topc(sK2) | ~v4_pre_topc(sK4(sK2,sK1),sK2) | v2_tops_2(sK1,sK2) | ~spl5_9),
% 0.20/0.47    inference(resolution,[],[f69,f27])).
% 0.20/0.47  fof(f27,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v4_pre_topc(sK4(X0,X1),X0) | v2_tops_2(X1,X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f12])).
% 0.20/0.47  fof(f90,plain,(
% 0.20/0.47    spl5_10 | spl5_6 | ~spl5_7 | ~spl5_9),
% 0.20/0.47    inference(avatar_split_clause,[],[f84,f68,f60,f54,f88])).
% 0.20/0.47  fof(f84,plain,(
% 0.20/0.47    r2_hidden(sK4(sK2,sK1),sK1) | (spl5_6 | ~spl5_7 | ~spl5_9)),
% 0.20/0.47    inference(subsumption_resolution,[],[f83,f55])).
% 0.20/0.47  fof(f83,plain,(
% 0.20/0.47    r2_hidden(sK4(sK2,sK1),sK1) | v2_tops_2(sK1,sK2) | (~spl5_7 | ~spl5_9)),
% 0.20/0.47    inference(subsumption_resolution,[],[f79,f61])).
% 0.20/0.47  fof(f79,plain,(
% 0.20/0.47    ~l1_pre_topc(sK2) | r2_hidden(sK4(sK2,sK1),sK1) | v2_tops_2(sK1,sK2) | ~spl5_9),
% 0.20/0.47    inference(resolution,[],[f69,f26])).
% 0.20/0.47  fof(f26,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | r2_hidden(sK4(X0,X1),X1) | v2_tops_2(X1,X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f12])).
% 0.20/0.47  fof(f70,plain,(
% 0.20/0.47    spl5_9),
% 0.20/0.47    inference(avatar_split_clause,[],[f31,f68])).
% 0.20/0.47  fof(f31,plain,(
% 0.20/0.47    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))),
% 0.20/0.47    inference(forward_demodulation,[],[f16,f17])).
% 0.20/0.47  fof(f17,plain,(
% 0.20/0.47    sK1 = sK3),
% 0.20/0.47    inference(cnf_transformation,[],[f8])).
% 0.20/0.47  fof(f8,plain,(
% 0.20/0.47    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~v2_tops_2(X3,X2) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))) & v2_tops_2(X1,X0) & m1_pre_topc(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 0.20/0.47    inference(flattening,[],[f7])).
% 0.20/0.47  fof(f7,plain,(
% 0.20/0.47    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : ((~v2_tops_2(X3,X2) & X1 = X3) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))) & v2_tops_2(X1,X0)) & m1_pre_topc(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f6])).
% 0.20/0.47  fof(f6,negated_conjecture,(
% 0.20/0.47    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_pre_topc(X2,X0) => (v2_tops_2(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) => (X1 = X3 => v2_tops_2(X3,X2)))))))),
% 0.20/0.47    inference(negated_conjecture,[],[f5])).
% 0.20/0.47  fof(f5,conjecture,(
% 0.20/0.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_pre_topc(X2,X0) => (v2_tops_2(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) => (X1 = X3 => v2_tops_2(X3,X2)))))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_tops_2)).
% 0.20/0.47  fof(f16,plain,(
% 0.20/0.47    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))),
% 0.20/0.47    inference(cnf_transformation,[],[f8])).
% 0.20/0.47  fof(f66,plain,(
% 0.20/0.47    spl5_8),
% 0.20/0.47    inference(avatar_split_clause,[],[f21,f64])).
% 0.20/0.47  fof(f21,plain,(
% 0.20/0.47    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.47    inference(cnf_transformation,[],[f8])).
% 0.20/0.47  fof(f62,plain,(
% 0.20/0.47    spl5_7 | ~spl5_1 | ~spl5_4),
% 0.20/0.47    inference(avatar_split_clause,[],[f58,f46,f33,f60])).
% 0.20/0.47  fof(f58,plain,(
% 0.20/0.47    l1_pre_topc(sK2) | (~spl5_1 | ~spl5_4)),
% 0.20/0.47    inference(subsumption_resolution,[],[f57,f34])).
% 0.20/0.47  fof(f57,plain,(
% 0.20/0.47    ~l1_pre_topc(sK0) | l1_pre_topc(sK2) | ~spl5_4),
% 0.20/0.47    inference(resolution,[],[f47,f28])).
% 0.20/0.47  fof(f28,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | l1_pre_topc(X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f13])).
% 0.20/0.47  fof(f13,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f2])).
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.20/0.47  fof(f56,plain,(
% 0.20/0.47    ~spl5_6 | ~spl5_2 | spl5_3),
% 0.20/0.47    inference(avatar_split_clause,[],[f44,f41,f37,f54])).
% 0.20/0.47  fof(f37,plain,(
% 0.20/0.47    spl5_2 <=> sK1 = sK3),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.20/0.47  fof(f41,plain,(
% 0.20/0.47    spl5_3 <=> v2_tops_2(sK3,sK2)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.20/0.47  fof(f44,plain,(
% 0.20/0.47    ~v2_tops_2(sK1,sK2) | (~spl5_2 | spl5_3)),
% 0.20/0.47    inference(forward_demodulation,[],[f42,f38])).
% 0.20/0.47  fof(f38,plain,(
% 0.20/0.47    sK1 = sK3 | ~spl5_2),
% 0.20/0.47    inference(avatar_component_clause,[],[f37])).
% 0.20/0.47  fof(f42,plain,(
% 0.20/0.47    ~v2_tops_2(sK3,sK2) | spl5_3),
% 0.20/0.47    inference(avatar_component_clause,[],[f41])).
% 0.20/0.47  fof(f52,plain,(
% 0.20/0.47    spl5_5),
% 0.20/0.47    inference(avatar_split_clause,[],[f20,f50])).
% 0.20/0.47  fof(f20,plain,(
% 0.20/0.47    v2_tops_2(sK1,sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f8])).
% 0.20/0.47  fof(f48,plain,(
% 0.20/0.47    spl5_4),
% 0.20/0.47    inference(avatar_split_clause,[],[f19,f46])).
% 0.20/0.47  fof(f19,plain,(
% 0.20/0.47    m1_pre_topc(sK2,sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f8])).
% 0.20/0.47  fof(f43,plain,(
% 0.20/0.47    ~spl5_3),
% 0.20/0.47    inference(avatar_split_clause,[],[f18,f41])).
% 0.20/0.47  fof(f18,plain,(
% 0.20/0.47    ~v2_tops_2(sK3,sK2)),
% 0.20/0.47    inference(cnf_transformation,[],[f8])).
% 0.20/0.47  fof(f39,plain,(
% 0.20/0.47    spl5_2),
% 0.20/0.47    inference(avatar_split_clause,[],[f17,f37])).
% 0.20/0.47  fof(f35,plain,(
% 0.20/0.47    spl5_1),
% 0.20/0.47    inference(avatar_split_clause,[],[f22,f33])).
% 0.20/0.47  fof(f22,plain,(
% 0.20/0.47    l1_pre_topc(sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f8])).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (21584)------------------------------
% 0.20/0.47  % (21584)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (21584)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (21584)Memory used [KB]: 6140
% 0.20/0.47  % (21584)Time elapsed: 0.063 s
% 0.20/0.47  % (21584)------------------------------
% 0.20/0.47  % (21584)------------------------------
% 0.20/0.47  % (21583)Success in time 0.116 s
%------------------------------------------------------------------------------
