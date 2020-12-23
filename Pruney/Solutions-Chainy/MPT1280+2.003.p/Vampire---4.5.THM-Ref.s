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
% DateTime   : Thu Dec  3 13:12:54 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 133 expanded)
%              Number of leaves         :   19 (  56 expanded)
%              Depth                    :   10
%              Number of atoms          :  237 ( 413 expanded)
%              Number of equality atoms :   43 (  79 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f121,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f41,f46,f51,f56,f64,f71,f76,f90,f101,f111,f119])).

fof(f119,plain,
    ( ~ spl2_1
    | ~ spl2_3
    | spl2_4
    | ~ spl2_11 ),
    inference(avatar_contradiction_clause,[],[f118])).

fof(f118,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_3
    | spl2_4
    | ~ spl2_11 ),
    inference(subsumption_resolution,[],[f117,f55])).

fof(f55,plain,
    ( k2_tops_1(sK0,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | spl2_4 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl2_4
  <=> k2_tops_1(sK0,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f117,plain,
    ( k2_tops_1(sK0,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_11 ),
    inference(subsumption_resolution,[],[f116,f50])).

fof(f50,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f48])).

fof(f48,plain,
    ( spl2_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f116,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_tops_1(sK0,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | ~ spl2_1
    | ~ spl2_11 ),
    inference(subsumption_resolution,[],[f113,f40])).

fof(f40,plain,
    ( l1_pre_topc(sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f38])).

fof(f38,plain,
    ( spl2_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f113,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_tops_1(sK0,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | ~ spl2_11 ),
    inference(resolution,[],[f110,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_tops_1(X1,X0),k2_tops_1(X1,k1_tops_1(X1,X0)))
      | ~ l1_pre_topc(X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | k2_tops_1(X1,X0) = k2_tops_1(X1,k1_tops_1(X1,X0)) ) ),
    inference(resolution,[],[f27,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_tops_1(X0,k1_tops_1(X0,X1)),k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,k1_tops_1(X0,X1)),k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k2_tops_1(X0,k1_tops_1(X0,X1)),k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_tops_1)).

fof(f110,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),k2_tops_1(sK0,k1_tops_1(sK0,sK1)))
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl2_11
  <=> r1_tarski(k2_tops_1(sK0,sK1),k2_tops_1(sK0,k1_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f111,plain,
    ( spl2_11
    | ~ spl2_1
    | ~ spl2_7
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f106,f98,f73,f38,f108])).

fof(f73,plain,
    ( spl2_7
  <=> sK1 = k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f98,plain,
    ( spl2_10
  <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f106,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),k2_tops_1(sK0,k1_tops_1(sK0,sK1)))
    | ~ spl2_1
    | ~ spl2_7
    | ~ spl2_10 ),
    inference(subsumption_resolution,[],[f82,f100])).

fof(f100,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f98])).

fof(f82,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),k2_tops_1(sK0,k1_tops_1(sK0,sK1)))
    | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_1
    | ~ spl2_7 ),
    inference(subsumption_resolution,[],[f80,f40])).

fof(f80,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),k2_tops_1(sK0,k1_tops_1(sK0,sK1)))
    | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_7 ),
    inference(superposition,[],[f26,f75])).

fof(f75,plain,
    ( sK1 = k2_pre_topc(sK0,k1_tops_1(sK0,sK1))
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f73])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_tops_1(X0,k2_pre_topc(X0,X1)),k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,k2_pre_topc(X0,X1)),k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k2_tops_1(X0,k2_pre_topc(X0,X1)),k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_tops_1)).

fof(f101,plain,
    ( spl2_10
    | ~ spl2_3
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f92,f87,f48,f98])).

fof(f87,plain,
    ( spl2_8
  <=> k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f92,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_3
    | ~ spl2_8 ),
    inference(subsumption_resolution,[],[f91,f50])).

fof(f91,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_8 ),
    inference(superposition,[],[f34,f89])).

fof(f89,plain,
    ( k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f87])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_subset_1)).

fof(f90,plain,
    ( spl2_8
    | ~ spl2_3
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f77,f69,f48,f87])).

fof(f69,plain,
    ( spl2_6
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_tops_1(sK0,X0) = k7_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f77,plain,
    ( k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_6 ),
    inference(resolution,[],[f70,f50])).

fof(f70,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_tops_1(sK0,X0) = k7_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) )
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f69])).

fof(f76,plain,
    ( spl2_7
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f67,f62,f48,f43,f73])).

fof(f43,plain,
    ( spl2_2
  <=> v5_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f62,plain,
    ( spl2_5
  <=> ! [X0] :
        ( ~ v5_tops_1(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_pre_topc(sK0,k1_tops_1(sK0,X0)) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f67,plain,
    ( sK1 = k2_pre_topc(sK0,k1_tops_1(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f66,f50])).

fof(f66,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | sK1 = k2_pre_topc(sK0,k1_tops_1(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_5 ),
    inference(resolution,[],[f63,f45])).

fof(f45,plain,
    ( v5_tops_1(sK1,sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f43])).

fof(f63,plain,
    ( ! [X0] :
        ( ~ v5_tops_1(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_pre_topc(sK0,k1_tops_1(sK0,X0)) = X0 )
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f62])).

fof(f71,plain,
    ( spl2_6
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f65,f38,f69])).

fof(f65,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_tops_1(sK0,X0) = k7_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) )
    | ~ spl2_1 ),
    inference(resolution,[],[f28,f40])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).

fof(f64,plain,
    ( spl2_5
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f60,f38,f62])).

fof(f60,plain,
    ( ! [X0] :
        ( ~ v5_tops_1(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_pre_topc(sK0,k1_tops_1(sK0,X0)) = X0 )
    | ~ spl2_1 ),
    inference(resolution,[],[f29,f40])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v5_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_tops_1(X1,X0)
              | k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1 )
            & ( k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1
              | ~ v5_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_tops_1(X1,X0)
          <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v5_tops_1(X1,X0)
          <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tops_1)).

fof(f56,plain,(
    ~ spl2_4 ),
    inference(avatar_split_clause,[],[f25,f53])).

fof(f25,plain,(
    k2_tops_1(sK0,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( k2_tops_1(sK0,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    & v5_tops_1(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f17,f16])).

fof(f16,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k2_tops_1(X0,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1)
            & v5_tops_1(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( k2_tops_1(sK0,k1_tops_1(sK0,X1)) != k2_tops_1(sK0,X1)
          & v5_tops_1(X1,sK0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X1] :
        ( k2_tops_1(sK0,k1_tops_1(sK0,X1)) != k2_tops_1(sK0,X1)
        & v5_tops_1(X1,sK0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( k2_tops_1(sK0,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
      & v5_tops_1(sK1,sK0)
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_tops_1(X0,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1)
          & v5_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_tops_1(X0,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1)
          & v5_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v5_tops_1(X1,X0)
             => k2_tops_1(X0,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v5_tops_1(X1,X0)
           => k2_tops_1(X0,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_tops_1)).

fof(f51,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f23,f48])).

fof(f23,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f46,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f24,f43])).

fof(f24,plain,(
    v5_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f18])).

% (28230)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
fof(f41,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f22,f38])).

fof(f22,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:25:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (28244)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.51  % (28227)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.51  % (28237)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.51  % (28245)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.51  % (28229)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.51  % (28227)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f121,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(avatar_sat_refutation,[],[f41,f46,f51,f56,f64,f71,f76,f90,f101,f111,f119])).
% 0.22/0.51  fof(f119,plain,(
% 0.22/0.51    ~spl2_1 | ~spl2_3 | spl2_4 | ~spl2_11),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f118])).
% 0.22/0.51  fof(f118,plain,(
% 0.22/0.51    $false | (~spl2_1 | ~spl2_3 | spl2_4 | ~spl2_11)),
% 0.22/0.51    inference(subsumption_resolution,[],[f117,f55])).
% 0.22/0.51  fof(f55,plain,(
% 0.22/0.51    k2_tops_1(sK0,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) | spl2_4),
% 0.22/0.51    inference(avatar_component_clause,[],[f53])).
% 0.22/0.51  fof(f53,plain,(
% 0.22/0.51    spl2_4 <=> k2_tops_1(sK0,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.22/0.51  fof(f117,plain,(
% 0.22/0.51    k2_tops_1(sK0,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) | (~spl2_1 | ~spl2_3 | ~spl2_11)),
% 0.22/0.51    inference(subsumption_resolution,[],[f116,f50])).
% 0.22/0.51  fof(f50,plain,(
% 0.22/0.51    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_3),
% 0.22/0.51    inference(avatar_component_clause,[],[f48])).
% 0.22/0.51  fof(f48,plain,(
% 0.22/0.51    spl2_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.22/0.51  fof(f116,plain,(
% 0.22/0.51    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | k2_tops_1(sK0,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) | (~spl2_1 | ~spl2_11)),
% 0.22/0.51    inference(subsumption_resolution,[],[f113,f40])).
% 0.22/0.51  fof(f40,plain,(
% 0.22/0.51    l1_pre_topc(sK0) | ~spl2_1),
% 0.22/0.51    inference(avatar_component_clause,[],[f38])).
% 0.22/0.51  fof(f38,plain,(
% 0.22/0.51    spl2_1 <=> l1_pre_topc(sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.51  fof(f113,plain,(
% 0.22/0.51    ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | k2_tops_1(sK0,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) | ~spl2_11),
% 0.22/0.51    inference(resolution,[],[f110,f59])).
% 0.22/0.51  fof(f59,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r1_tarski(k2_tops_1(X1,X0),k2_tops_1(X1,k1_tops_1(X1,X0))) | ~l1_pre_topc(X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | k2_tops_1(X1,X0) = k2_tops_1(X1,k1_tops_1(X1,X0))) )),
% 0.22/0.51    inference(resolution,[],[f27,f33])).
% 0.22/0.51  fof(f33,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.22/0.51    inference(cnf_transformation,[],[f21])).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.51    inference(flattening,[],[f20])).
% 0.22/0.51  fof(f20,plain,(
% 0.22/0.51    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.51    inference(nnf_transformation,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r1_tarski(k2_tops_1(X0,k1_tops_1(X0,X1)),k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f12])).
% 0.22/0.51  fof(f12,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (r1_tarski(k2_tops_1(X0,k1_tops_1(X0,X1)),k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f4])).
% 0.22/0.51  fof(f4,axiom,(
% 0.22/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k2_tops_1(X0,k1_tops_1(X0,X1)),k2_tops_1(X0,X1))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_tops_1)).
% 0.22/0.51  fof(f110,plain,(
% 0.22/0.51    r1_tarski(k2_tops_1(sK0,sK1),k2_tops_1(sK0,k1_tops_1(sK0,sK1))) | ~spl2_11),
% 0.22/0.51    inference(avatar_component_clause,[],[f108])).
% 0.22/0.51  fof(f108,plain,(
% 0.22/0.51    spl2_11 <=> r1_tarski(k2_tops_1(sK0,sK1),k2_tops_1(sK0,k1_tops_1(sK0,sK1)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.22/0.51  fof(f111,plain,(
% 0.22/0.51    spl2_11 | ~spl2_1 | ~spl2_7 | ~spl2_10),
% 0.22/0.51    inference(avatar_split_clause,[],[f106,f98,f73,f38,f108])).
% 0.22/0.51  fof(f73,plain,(
% 0.22/0.51    spl2_7 <=> sK1 = k2_pre_topc(sK0,k1_tops_1(sK0,sK1))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.22/0.51  fof(f98,plain,(
% 0.22/0.51    spl2_10 <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.22/0.51  fof(f106,plain,(
% 0.22/0.51    r1_tarski(k2_tops_1(sK0,sK1),k2_tops_1(sK0,k1_tops_1(sK0,sK1))) | (~spl2_1 | ~spl2_7 | ~spl2_10)),
% 0.22/0.51    inference(subsumption_resolution,[],[f82,f100])).
% 0.22/0.51  fof(f100,plain,(
% 0.22/0.51    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_10),
% 0.22/0.51    inference(avatar_component_clause,[],[f98])).
% 0.22/0.51  fof(f82,plain,(
% 0.22/0.51    r1_tarski(k2_tops_1(sK0,sK1),k2_tops_1(sK0,k1_tops_1(sK0,sK1))) | ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_1 | ~spl2_7)),
% 0.22/0.51    inference(subsumption_resolution,[],[f80,f40])).
% 0.22/0.51  fof(f80,plain,(
% 0.22/0.51    r1_tarski(k2_tops_1(sK0,sK1),k2_tops_1(sK0,k1_tops_1(sK0,sK1))) | ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl2_7),
% 0.22/0.51    inference(superposition,[],[f26,f75])).
% 0.22/0.51  fof(f75,plain,(
% 0.22/0.51    sK1 = k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) | ~spl2_7),
% 0.22/0.51    inference(avatar_component_clause,[],[f73])).
% 0.22/0.51  fof(f26,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r1_tarski(k2_tops_1(X0,k2_pre_topc(X0,X1)),k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f11])).
% 0.22/0.51  fof(f11,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (r1_tarski(k2_tops_1(X0,k2_pre_topc(X0,X1)),k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f5])).
% 0.22/0.51  fof(f5,axiom,(
% 0.22/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k2_tops_1(X0,k2_pre_topc(X0,X1)),k2_tops_1(X0,X1))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_tops_1)).
% 0.22/0.51  fof(f101,plain,(
% 0.22/0.51    spl2_10 | ~spl2_3 | ~spl2_8),
% 0.22/0.51    inference(avatar_split_clause,[],[f92,f87,f48,f98])).
% 0.22/0.51  fof(f87,plain,(
% 0.22/0.51    spl2_8 <=> k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.22/0.51  fof(f92,plain,(
% 0.22/0.51    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_3 | ~spl2_8)),
% 0.22/0.51    inference(subsumption_resolution,[],[f91,f50])).
% 0.22/0.51  fof(f91,plain,(
% 0.22/0.51    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_8),
% 0.22/0.51    inference(superposition,[],[f34,f89])).
% 0.22/0.51  fof(f89,plain,(
% 0.22/0.51    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | ~spl2_8),
% 0.22/0.51    inference(avatar_component_clause,[],[f87])).
% 0.22/0.51  fof(f34,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f15])).
% 0.22/0.51  fof(f15,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f2])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_subset_1)).
% 0.22/0.51  fof(f90,plain,(
% 0.22/0.51    spl2_8 | ~spl2_3 | ~spl2_6),
% 0.22/0.51    inference(avatar_split_clause,[],[f77,f69,f48,f87])).
% 0.22/0.51  fof(f69,plain,(
% 0.22/0.51    spl2_6 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_tops_1(sK0,X0) = k7_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.22/0.51  fof(f77,plain,(
% 0.22/0.51    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | (~spl2_3 | ~spl2_6)),
% 0.22/0.51    inference(resolution,[],[f70,f50])).
% 0.22/0.51  fof(f70,plain,(
% 0.22/0.51    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_tops_1(sK0,X0) = k7_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0))) ) | ~spl2_6),
% 0.22/0.51    inference(avatar_component_clause,[],[f69])).
% 0.22/0.51  fof(f76,plain,(
% 0.22/0.51    spl2_7 | ~spl2_2 | ~spl2_3 | ~spl2_5),
% 0.22/0.51    inference(avatar_split_clause,[],[f67,f62,f48,f43,f73])).
% 0.22/0.51  fof(f43,plain,(
% 0.22/0.51    spl2_2 <=> v5_tops_1(sK1,sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.51  fof(f62,plain,(
% 0.22/0.51    spl2_5 <=> ! [X0] : (~v5_tops_1(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,k1_tops_1(sK0,X0)) = X0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.22/0.51  fof(f67,plain,(
% 0.22/0.51    sK1 = k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) | (~spl2_2 | ~spl2_3 | ~spl2_5)),
% 0.22/0.51    inference(subsumption_resolution,[],[f66,f50])).
% 0.22/0.51  fof(f66,plain,(
% 0.22/0.51    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | sK1 = k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) | (~spl2_2 | ~spl2_5)),
% 0.22/0.51    inference(resolution,[],[f63,f45])).
% 0.22/0.51  fof(f45,plain,(
% 0.22/0.51    v5_tops_1(sK1,sK0) | ~spl2_2),
% 0.22/0.51    inference(avatar_component_clause,[],[f43])).
% 0.22/0.51  fof(f63,plain,(
% 0.22/0.51    ( ! [X0] : (~v5_tops_1(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,k1_tops_1(sK0,X0)) = X0) ) | ~spl2_5),
% 0.22/0.51    inference(avatar_component_clause,[],[f62])).
% 0.22/0.51  fof(f71,plain,(
% 0.22/0.51    spl2_6 | ~spl2_1),
% 0.22/0.51    inference(avatar_split_clause,[],[f65,f38,f69])).
% 0.22/0.51  fof(f65,plain,(
% 0.22/0.51    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_tops_1(sK0,X0) = k7_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0))) ) | ~spl2_1),
% 0.22/0.51    inference(resolution,[],[f28,f40])).
% 0.22/0.51  fof(f28,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f13])).
% 0.22/0.51  fof(f13,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f6])).
% 0.22/0.51  fof(f6,axiom,(
% 0.22/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).
% 0.22/0.51  fof(f64,plain,(
% 0.22/0.51    spl2_5 | ~spl2_1),
% 0.22/0.51    inference(avatar_split_clause,[],[f60,f38,f62])).
% 0.22/0.51  fof(f60,plain,(
% 0.22/0.51    ( ! [X0] : (~v5_tops_1(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,k1_tops_1(sK0,X0)) = X0) ) | ~spl2_1),
% 0.22/0.51    inference(resolution,[],[f29,f40])).
% 0.22/0.51  fof(f29,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v5_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1) )),
% 0.22/0.51    inference(cnf_transformation,[],[f19])).
% 0.22/0.51  fof(f19,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (((v5_tops_1(X1,X0) | k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1) & (k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 | ~v5_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(nnf_transformation,[],[f14])).
% 0.22/0.51  fof(f14,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : ((v5_tops_1(X1,X0) <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f3])).
% 0.22/0.51  fof(f3,axiom,(
% 0.22/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v5_tops_1(X1,X0) <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tops_1)).
% 0.22/0.51  fof(f56,plain,(
% 0.22/0.51    ~spl2_4),
% 0.22/0.51    inference(avatar_split_clause,[],[f25,f53])).
% 0.22/0.51  fof(f25,plain,(
% 0.22/0.51    k2_tops_1(sK0,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)),
% 0.22/0.51    inference(cnf_transformation,[],[f18])).
% 0.22/0.51  fof(f18,plain,(
% 0.22/0.51    (k2_tops_1(sK0,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) & v5_tops_1(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f17,f16])).
% 0.22/0.51  fof(f16,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (k2_tops_1(X0,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) & v5_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (k2_tops_1(sK0,k1_tops_1(sK0,X1)) != k2_tops_1(sK0,X1) & v5_tops_1(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f17,plain,(
% 0.22/0.51    ? [X1] : (k2_tops_1(sK0,k1_tops_1(sK0,X1)) != k2_tops_1(sK0,X1) & v5_tops_1(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (k2_tops_1(sK0,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) & v5_tops_1(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f10,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (k2_tops_1(X0,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) & v5_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.22/0.51    inference(flattening,[],[f9])).
% 0.22/0.51  fof(f9,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : ((k2_tops_1(X0,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) & v5_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f8])).
% 0.22/0.51  fof(f8,negated_conjecture,(
% 0.22/0.51    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v5_tops_1(X1,X0) => k2_tops_1(X0,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 0.22/0.51    inference(negated_conjecture,[],[f7])).
% 0.22/0.51  fof(f7,conjecture,(
% 0.22/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v5_tops_1(X1,X0) => k2_tops_1(X0,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_tops_1)).
% 0.22/0.51  fof(f51,plain,(
% 0.22/0.51    spl2_3),
% 0.22/0.51    inference(avatar_split_clause,[],[f23,f48])).
% 0.22/0.51  fof(f23,plain,(
% 0.22/0.51    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.51    inference(cnf_transformation,[],[f18])).
% 0.22/0.51  fof(f46,plain,(
% 0.22/0.51    spl2_2),
% 0.22/0.51    inference(avatar_split_clause,[],[f24,f43])).
% 0.22/0.51  fof(f24,plain,(
% 0.22/0.51    v5_tops_1(sK1,sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f18])).
% 0.22/0.51  % (28230)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.51  fof(f41,plain,(
% 0.22/0.51    spl2_1),
% 0.22/0.51    inference(avatar_split_clause,[],[f22,f38])).
% 0.22/0.51  fof(f22,plain,(
% 0.22/0.51    l1_pre_topc(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f18])).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (28227)------------------------------
% 0.22/0.51  % (28227)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (28227)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (28227)Memory used [KB]: 6140
% 0.22/0.51  % (28227)Time elapsed: 0.096 s
% 0.22/0.51  % (28227)------------------------------
% 0.22/0.51  % (28227)------------------------------
% 0.22/0.51  % (28249)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.51  % (28216)Success in time 0.143 s
%------------------------------------------------------------------------------
