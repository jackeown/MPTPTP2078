%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:50 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 148 expanded)
%              Number of leaves         :   26 (  71 expanded)
%              Depth                    :    6
%              Number of atoms          :  272 ( 469 expanded)
%              Number of equality atoms :   17 (  25 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f481,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f37,f42,f47,f52,f56,f60,f64,f72,f80,f84,f103,f118,f139,f180,f401,f425,f468])).

fof(f468,plain,
    ( ~ spl3_2
    | spl3_21
    | ~ spl3_68 ),
    inference(avatar_contradiction_clause,[],[f467])).

fof(f467,plain,
    ( $false
    | ~ spl3_2
    | spl3_21
    | ~ spl3_68 ),
    inference(subsumption_resolution,[],[f463,f41])).

fof(f41,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f39])).

fof(f39,plain,
    ( spl3_2
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f463,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_21
    | ~ spl3_68 ),
    inference(resolution,[],[f424,f138])).

fof(f138,plain,
    ( ~ r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK2)
    | spl3_21 ),
    inference(avatar_component_clause,[],[f136])).

fof(f136,plain,
    ( spl3_21
  <=> r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f424,plain,
    ( ! [X1] :
        ( r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,X1),X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl3_68 ),
    inference(avatar_component_clause,[],[f423])).

fof(f423,plain,
    ( spl3_68
  <=> ! [X1] :
        ( r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,X1),X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_68])])).

fof(f425,plain,
    ( spl3_68
    | ~ spl3_3
    | ~ spl3_28
    | ~ spl3_64 ),
    inference(avatar_split_clause,[],[f421,f399,f178,f44,f423])).

fof(f44,plain,
    ( spl3_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f178,plain,
    ( spl3_28
  <=> ! [X1] : k9_subset_1(u1_struct_0(sK0),X1,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f399,plain,
    ( spl3_64
  <=> ! [X1,X0,X2] :
        ( r1_tarski(k9_subset_1(X0,X1,X2),X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_64])])).

fof(f421,plain,
    ( ! [X1] :
        ( r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,X1),X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl3_3
    | ~ spl3_28
    | ~ spl3_64 ),
    inference(subsumption_resolution,[],[f405,f46])).

fof(f46,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f44])).

fof(f405,plain,
    ( ! [X1] :
        ( r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,X1),X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl3_28
    | ~ spl3_64 ),
    inference(superposition,[],[f400,f179])).

fof(f179,plain,
    ( ! [X1] : k9_subset_1(u1_struct_0(sK0),X1,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,X1)
    | ~ spl3_28 ),
    inference(avatar_component_clause,[],[f178])).

% (25169)lrs+1004_5:4_aac=none:add=large:afp=100000:afq=1.4:anc=all_dependent:bd=off:cond=fast:gsp=input_only:gs=on:gsem=off:lma=on:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sp=occurrence:updr=off:uhcvi=on_99 on theBenchmark
fof(f400,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(k9_subset_1(X0,X1,X2),X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
    | ~ spl3_64 ),
    inference(avatar_component_clause,[],[f399])).

fof(f401,plain,
    ( spl3_64
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f397,f78,f62,f58,f399])).

fof(f58,plain,
    ( spl3_6
  <=> ! [X1,X0,X2] :
        ( r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f62,plain,
    ( spl3_7
  <=> ! [X1,X0,X2] :
        ( r1_tarski(X1,X2)
        | ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f78,plain,
    ( spl3_11
  <=> ! [X1,X0,X2] :
        ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f397,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(k9_subset_1(X0,X1,X2),X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_11 ),
    inference(subsumption_resolution,[],[f396,f79])).

fof(f79,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f78])).

fof(f396,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(k9_subset_1(X0,X1,X2),X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | ~ m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(duplicate_literal_removal,[],[f395])).

fof(f395,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(k9_subset_1(X0,X1,X2),X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | ~ m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(resolution,[],[f63,f59])).

fof(f59,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f58])).

fof(f63,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
        | r1_tarski(X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f62])).

fof(f180,plain,
    ( spl3_28
    | ~ spl3_3
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f170,f82,f44,f178])).

fof(f82,plain,
    ( spl3_12
  <=> ! [X1,X0,X2] :
        ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f170,plain,
    ( ! [X1] : k9_subset_1(u1_struct_0(sK0),X1,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,X1)
    | ~ spl3_3
    | ~ spl3_12 ),
    inference(resolution,[],[f83,f46])).

fof(f83,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) )
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f82])).

fof(f139,plain,
    ( ~ spl3_21
    | spl3_15
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f133,f115,f100,f136])).

fof(f100,plain,
    ( spl3_15
  <=> r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),u1_struct_0(k1_pre_topc(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f115,plain,
    ( spl3_17
  <=> sK2 = u1_struct_0(k1_pre_topc(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f133,plain,
    ( ~ r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK2)
    | spl3_15
    | ~ spl3_17 ),
    inference(backward_demodulation,[],[f102,f117])).

fof(f117,plain,
    ( sK2 = u1_struct_0(k1_pre_topc(sK0,sK2))
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f115])).

fof(f102,plain,
    ( ~ r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),u1_struct_0(k1_pre_topc(sK0,sK2)))
    | spl3_15 ),
    inference(avatar_component_clause,[],[f100])).

fof(f118,plain,
    ( spl3_17
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f113,f54,f49,f39,f115])).

fof(f49,plain,
    ( spl3_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f54,plain,
    ( spl3_5
  <=> ! [X1,X0] :
        ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f113,plain,
    ( sK2 = u1_struct_0(k1_pre_topc(sK0,sK2))
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f109,f51])).

fof(f51,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f49])).

fof(f109,plain,
    ( sK2 = u1_struct_0(k1_pre_topc(sK0,sK2))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_2
    | ~ spl3_5 ),
    inference(resolution,[],[f55,f41])).

fof(f55,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | u1_struct_0(k1_pre_topc(X0,X1)) = X1
        | ~ l1_pre_topc(X0) )
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f54])).

fof(f103,plain,
    ( ~ spl3_15
    | spl3_1
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f98,f70,f34,f100])).

fof(f34,plain,
    ( spl3_1
  <=> m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f70,plain,
    ( spl3_9
  <=> ! [X1,X0] :
        ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f98,plain,
    ( ~ r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),u1_struct_0(k1_pre_topc(sK0,sK2)))
    | spl3_1
    | ~ spl3_9 ),
    inference(resolution,[],[f36,f71])).

fof(f71,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f70])).

fof(f36,plain,
    ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK2))))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f34])).

fof(f84,plain,(
    spl3_12 ),
    inference(avatar_split_clause,[],[f32,f82])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

fof(f80,plain,(
    spl3_11 ),
    inference(avatar_split_clause,[],[f31,f78])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(f72,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f30,f70])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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

fof(f64,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f28,f62])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_tarski(X1,X2)
              | ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
            & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
              | ~ r1_tarski(X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).

fof(f60,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f26,f58])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2)))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_subset_1)).

fof(f56,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f25,f54])).

fof(f25,plain,(
    ! [X0,X1] :
      ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => u1_struct_0(k1_pre_topc(X0,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_pre_topc)).

fof(f52,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f21,f49])).

fof(f21,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK2))))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f17,f16,f15])).

fof(f15,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ m1_subset_1(k9_subset_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X2))))
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),X1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,X2))))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),X1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,X2))))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,X2))))
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X2] :
        ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,X2))))
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK2))))
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ m1_subset_1(k9_subset_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X2))))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => m1_subset_1(k9_subset_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X2)))) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => m1_subset_1(k9_subset_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X2)))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_tops_2)).

fof(f47,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f22,f44])).

fof(f22,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f42,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f23,f39])).

fof(f23,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f37,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f24,f34])).

fof(f24,plain,(
    ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK2)))) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n009.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:54:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.42  % (25172)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.21/0.43  % (25170)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.21/0.44  % (25176)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.21/0.44  % (25175)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.21/0.44  % (25167)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.21/0.45  % (25176)Refutation found. Thanks to Tanya!
% 0.21/0.45  % SZS status Theorem for theBenchmark
% 0.21/0.45  % SZS output start Proof for theBenchmark
% 0.21/0.45  fof(f481,plain,(
% 0.21/0.45    $false),
% 0.21/0.45    inference(avatar_sat_refutation,[],[f37,f42,f47,f52,f56,f60,f64,f72,f80,f84,f103,f118,f139,f180,f401,f425,f468])).
% 0.21/0.45  fof(f468,plain,(
% 0.21/0.45    ~spl3_2 | spl3_21 | ~spl3_68),
% 0.21/0.45    inference(avatar_contradiction_clause,[],[f467])).
% 0.21/0.45  fof(f467,plain,(
% 0.21/0.45    $false | (~spl3_2 | spl3_21 | ~spl3_68)),
% 0.21/0.45    inference(subsumption_resolution,[],[f463,f41])).
% 0.21/0.45  fof(f41,plain,(
% 0.21/0.45    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_2),
% 0.21/0.45    inference(avatar_component_clause,[],[f39])).
% 0.21/0.45  fof(f39,plain,(
% 0.21/0.45    spl3_2 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.45  fof(f463,plain,(
% 0.21/0.45    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | (spl3_21 | ~spl3_68)),
% 0.21/0.45    inference(resolution,[],[f424,f138])).
% 0.21/0.45  fof(f138,plain,(
% 0.21/0.45    ~r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK2) | spl3_21),
% 0.21/0.45    inference(avatar_component_clause,[],[f136])).
% 0.21/0.45  fof(f136,plain,(
% 0.21/0.45    spl3_21 <=> r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK2)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.21/0.45  fof(f424,plain,(
% 0.21/0.45    ( ! [X1] : (r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl3_68),
% 0.21/0.45    inference(avatar_component_clause,[],[f423])).
% 0.21/0.45  fof(f423,plain,(
% 0.21/0.45    spl3_68 <=> ! [X1] : (r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_68])])).
% 0.21/0.45  fof(f425,plain,(
% 0.21/0.45    spl3_68 | ~spl3_3 | ~spl3_28 | ~spl3_64),
% 0.21/0.45    inference(avatar_split_clause,[],[f421,f399,f178,f44,f423])).
% 0.21/0.45  fof(f44,plain,(
% 0.21/0.45    spl3_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.45  fof(f178,plain,(
% 0.21/0.45    spl3_28 <=> ! [X1] : k9_subset_1(u1_struct_0(sK0),X1,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,X1)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 0.21/0.45  fof(f399,plain,(
% 0.21/0.45    spl3_64 <=> ! [X1,X0,X2] : (r1_tarski(k9_subset_1(X0,X1,X2),X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_64])])).
% 0.21/0.45  fof(f421,plain,(
% 0.21/0.45    ( ! [X1] : (r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl3_3 | ~spl3_28 | ~spl3_64)),
% 0.21/0.45    inference(subsumption_resolution,[],[f405,f46])).
% 0.21/0.45  fof(f46,plain,(
% 0.21/0.45    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_3),
% 0.21/0.45    inference(avatar_component_clause,[],[f44])).
% 0.21/0.45  fof(f405,plain,(
% 0.21/0.45    ( ! [X1] : (r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl3_28 | ~spl3_64)),
% 0.21/0.45    inference(superposition,[],[f400,f179])).
% 0.21/0.45  fof(f179,plain,(
% 0.21/0.45    ( ! [X1] : (k9_subset_1(u1_struct_0(sK0),X1,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,X1)) ) | ~spl3_28),
% 0.21/0.45    inference(avatar_component_clause,[],[f178])).
% 0.21/0.45  % (25169)lrs+1004_5:4_aac=none:add=large:afp=100000:afq=1.4:anc=all_dependent:bd=off:cond=fast:gsp=input_only:gs=on:gsem=off:lma=on:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sp=occurrence:updr=off:uhcvi=on_99 on theBenchmark
% 0.21/0.45  fof(f400,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (r1_tarski(k9_subset_1(X0,X1,X2),X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) ) | ~spl3_64),
% 0.21/0.45    inference(avatar_component_clause,[],[f399])).
% 0.21/0.45  fof(f401,plain,(
% 0.21/0.45    spl3_64 | ~spl3_6 | ~spl3_7 | ~spl3_11),
% 0.21/0.45    inference(avatar_split_clause,[],[f397,f78,f62,f58,f399])).
% 0.21/0.45  fof(f58,plain,(
% 0.21/0.45    spl3_6 <=> ! [X1,X0,X2] : (r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.45  fof(f62,plain,(
% 0.21/0.45    spl3_7 <=> ! [X1,X0,X2] : (r1_tarski(X1,X2) | ~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.45  fof(f78,plain,(
% 0.21/0.45    spl3_11 <=> ! [X1,X0,X2] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.45  fof(f397,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (r1_tarski(k9_subset_1(X0,X1,X2),X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) ) | (~spl3_6 | ~spl3_7 | ~spl3_11)),
% 0.21/0.45    inference(subsumption_resolution,[],[f396,f79])).
% 0.21/0.45  fof(f79,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) ) | ~spl3_11),
% 0.21/0.45    inference(avatar_component_clause,[],[f78])).
% 0.21/0.45  fof(f396,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (r1_tarski(k9_subset_1(X0,X1,X2),X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) ) | (~spl3_6 | ~spl3_7)),
% 0.21/0.45    inference(duplicate_literal_removal,[],[f395])).
% 0.21/0.45  fof(f395,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (r1_tarski(k9_subset_1(X0,X1,X2),X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | (~spl3_6 | ~spl3_7)),
% 0.21/0.45    inference(resolution,[],[f63,f59])).
% 0.21/0.45  fof(f59,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl3_6),
% 0.21/0.45    inference(avatar_component_clause,[],[f58])).
% 0.21/0.45  fof(f63,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl3_7),
% 0.21/0.45    inference(avatar_component_clause,[],[f62])).
% 0.21/0.45  fof(f180,plain,(
% 0.21/0.45    spl3_28 | ~spl3_3 | ~spl3_12),
% 0.21/0.45    inference(avatar_split_clause,[],[f170,f82,f44,f178])).
% 0.21/0.45  fof(f82,plain,(
% 0.21/0.45    spl3_12 <=> ! [X1,X0,X2] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.45  fof(f170,plain,(
% 0.21/0.45    ( ! [X1] : (k9_subset_1(u1_struct_0(sK0),X1,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,X1)) ) | (~spl3_3 | ~spl3_12)),
% 0.21/0.45    inference(resolution,[],[f83,f46])).
% 0.21/0.45  fof(f83,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)) ) | ~spl3_12),
% 0.21/0.45    inference(avatar_component_clause,[],[f82])).
% 0.21/0.45  fof(f139,plain,(
% 0.21/0.45    ~spl3_21 | spl3_15 | ~spl3_17),
% 0.21/0.45    inference(avatar_split_clause,[],[f133,f115,f100,f136])).
% 0.21/0.45  fof(f100,plain,(
% 0.21/0.45    spl3_15 <=> r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),u1_struct_0(k1_pre_topc(sK0,sK2)))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.21/0.45  fof(f115,plain,(
% 0.21/0.45    spl3_17 <=> sK2 = u1_struct_0(k1_pre_topc(sK0,sK2))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.21/0.45  fof(f133,plain,(
% 0.21/0.45    ~r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK2) | (spl3_15 | ~spl3_17)),
% 0.21/0.45    inference(backward_demodulation,[],[f102,f117])).
% 0.21/0.45  fof(f117,plain,(
% 0.21/0.45    sK2 = u1_struct_0(k1_pre_topc(sK0,sK2)) | ~spl3_17),
% 0.21/0.45    inference(avatar_component_clause,[],[f115])).
% 0.21/0.45  fof(f102,plain,(
% 0.21/0.45    ~r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),u1_struct_0(k1_pre_topc(sK0,sK2))) | spl3_15),
% 0.21/0.45    inference(avatar_component_clause,[],[f100])).
% 0.21/0.45  fof(f118,plain,(
% 0.21/0.45    spl3_17 | ~spl3_2 | ~spl3_4 | ~spl3_5),
% 0.21/0.45    inference(avatar_split_clause,[],[f113,f54,f49,f39,f115])).
% 0.21/0.45  fof(f49,plain,(
% 0.21/0.45    spl3_4 <=> l1_pre_topc(sK0)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.45  fof(f54,plain,(
% 0.21/0.45    spl3_5 <=> ! [X1,X0] : (u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.45  fof(f113,plain,(
% 0.21/0.45    sK2 = u1_struct_0(k1_pre_topc(sK0,sK2)) | (~spl3_2 | ~spl3_4 | ~spl3_5)),
% 0.21/0.45    inference(subsumption_resolution,[],[f109,f51])).
% 0.21/0.45  fof(f51,plain,(
% 0.21/0.45    l1_pre_topc(sK0) | ~spl3_4),
% 0.21/0.45    inference(avatar_component_clause,[],[f49])).
% 0.21/0.45  fof(f109,plain,(
% 0.21/0.45    sK2 = u1_struct_0(k1_pre_topc(sK0,sK2)) | ~l1_pre_topc(sK0) | (~spl3_2 | ~spl3_5)),
% 0.21/0.45    inference(resolution,[],[f55,f41])).
% 0.21/0.45  fof(f55,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~l1_pre_topc(X0)) ) | ~spl3_5),
% 0.21/0.45    inference(avatar_component_clause,[],[f54])).
% 0.21/0.45  fof(f103,plain,(
% 0.21/0.45    ~spl3_15 | spl3_1 | ~spl3_9),
% 0.21/0.45    inference(avatar_split_clause,[],[f98,f70,f34,f100])).
% 0.21/0.45  fof(f34,plain,(
% 0.21/0.45    spl3_1 <=> m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK2))))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.45  fof(f70,plain,(
% 0.21/0.45    spl3_9 <=> ! [X1,X0] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.45  fof(f98,plain,(
% 0.21/0.45    ~r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),u1_struct_0(k1_pre_topc(sK0,sK2))) | (spl3_1 | ~spl3_9)),
% 0.21/0.45    inference(resolution,[],[f36,f71])).
% 0.21/0.45  fof(f71,plain,(
% 0.21/0.45    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) ) | ~spl3_9),
% 0.21/0.45    inference(avatar_component_clause,[],[f70])).
% 0.21/0.45  fof(f36,plain,(
% 0.21/0.45    ~m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK2)))) | spl3_1),
% 0.21/0.45    inference(avatar_component_clause,[],[f34])).
% 0.21/0.45  fof(f84,plain,(
% 0.21/0.45    spl3_12),
% 0.21/0.45    inference(avatar_split_clause,[],[f32,f82])).
% 0.21/0.45  fof(f32,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f14])).
% 0.21/0.45  fof(f14,plain,(
% 0.21/0.45    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.21/0.45    inference(ennf_transformation,[],[f1])).
% 0.21/0.45  fof(f1,axiom,(
% 0.21/0.45    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k9_subset_1)).
% 0.21/0.45  fof(f80,plain,(
% 0.21/0.45    spl3_11),
% 0.21/0.45    inference(avatar_split_clause,[],[f31,f78])).
% 0.21/0.45  fof(f31,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f13])).
% 0.21/0.45  fof(f13,plain,(
% 0.21/0.45    ! [X0,X1,X2] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.21/0.45    inference(ennf_transformation,[],[f2])).
% 0.21/0.45  fof(f2,axiom,(
% 0.21/0.45    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).
% 0.21/0.45  fof(f72,plain,(
% 0.21/0.45    spl3_9),
% 0.21/0.45    inference(avatar_split_clause,[],[f30,f70])).
% 0.21/0.45  fof(f30,plain,(
% 0.21/0.45    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f20])).
% 0.21/0.45  fof(f20,plain,(
% 0.21/0.45    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.45    inference(nnf_transformation,[],[f5])).
% 0.21/0.45  fof(f5,axiom,(
% 0.21/0.45    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.45  fof(f64,plain,(
% 0.21/0.45    spl3_7),
% 0.21/0.45    inference(avatar_split_clause,[],[f28,f62])).
% 0.21/0.45  fof(f28,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | ~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f19])).
% 0.21/0.45  fof(f19,plain,(
% 0.21/0.45    ! [X0,X1] : (! [X2] : (((r1_tarski(X1,X2) | ~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.45    inference(nnf_transformation,[],[f12])).
% 0.21/0.45  fof(f12,plain,(
% 0.21/0.45    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.45    inference(ennf_transformation,[],[f3])).
% 0.21/0.45  fof(f3,axiom,(
% 0.21/0.45    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).
% 0.21/0.45  fof(f60,plain,(
% 0.21/0.45    spl3_6),
% 0.21/0.45    inference(avatar_split_clause,[],[f26,f58])).
% 0.21/0.45  fof(f26,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f11])).
% 0.21/0.45  fof(f11,plain,(
% 0.21/0.45    ! [X0,X1] : (! [X2] : (r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.45    inference(ennf_transformation,[],[f4])).
% 0.21/0.45  fof(f4,axiom,(
% 0.21/0.45    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2)))))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_subset_1)).
% 0.21/0.45  fof(f56,plain,(
% 0.21/0.45    spl3_5),
% 0.21/0.45    inference(avatar_split_clause,[],[f25,f54])).
% 0.21/0.45  fof(f25,plain,(
% 0.21/0.45    ( ! [X0,X1] : (u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f10])).
% 0.21/0.45  fof(f10,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : (u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.45    inference(ennf_transformation,[],[f6])).
% 0.21/0.45  fof(f6,axiom,(
% 0.21/0.45    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => u1_struct_0(k1_pre_topc(X0,X1)) = X1))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_pre_topc)).
% 0.21/0.45  fof(f52,plain,(
% 0.21/0.45    spl3_4),
% 0.21/0.45    inference(avatar_split_clause,[],[f21,f49])).
% 0.21/0.45  fof(f21,plain,(
% 0.21/0.45    l1_pre_topc(sK0)),
% 0.21/0.45    inference(cnf_transformation,[],[f18])).
% 0.21/0.45  fof(f18,plain,(
% 0.21/0.45    ((~m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK2)))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 0.21/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f17,f16,f15])).
% 0.21/0.45  fof(f15,plain,(
% 0.21/0.45    ? [X0] : (? [X1] : (? [X2] : (~m1_subset_1(k9_subset_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X2)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~m1_subset_1(k9_subset_1(u1_struct_0(sK0),X1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,X2)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f16,plain,(
% 0.21/0.45    ? [X1] : (? [X2] : (~m1_subset_1(k9_subset_1(u1_struct_0(sK0),X1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,X2)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (~m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,X2)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f17,plain,(
% 0.21/0.45    ? [X2] : (~m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,X2)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (~m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK2)))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f9,plain,(
% 0.21/0.45    ? [X0] : (? [X1] : (? [X2] : (~m1_subset_1(k9_subset_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X2)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.21/0.45    inference(ennf_transformation,[],[f8])).
% 0.21/0.45  fof(f8,negated_conjecture,(
% 0.21/0.45    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => m1_subset_1(k9_subset_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X2)))))))),
% 0.21/0.45    inference(negated_conjecture,[],[f7])).
% 0.21/0.45  fof(f7,conjecture,(
% 0.21/0.45    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => m1_subset_1(k9_subset_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X2)))))))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_tops_2)).
% 0.21/0.45  fof(f47,plain,(
% 0.21/0.45    spl3_3),
% 0.21/0.45    inference(avatar_split_clause,[],[f22,f44])).
% 0.21/0.45  fof(f22,plain,(
% 0.21/0.45    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.45    inference(cnf_transformation,[],[f18])).
% 0.21/0.45  fof(f42,plain,(
% 0.21/0.45    spl3_2),
% 0.21/0.45    inference(avatar_split_clause,[],[f23,f39])).
% 0.21/0.45  fof(f23,plain,(
% 0.21/0.45    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.45    inference(cnf_transformation,[],[f18])).
% 0.21/0.45  fof(f37,plain,(
% 0.21/0.45    ~spl3_1),
% 0.21/0.45    inference(avatar_split_clause,[],[f24,f34])).
% 0.21/0.45  fof(f24,plain,(
% 0.21/0.45    ~m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK2))))),
% 0.21/0.45    inference(cnf_transformation,[],[f18])).
% 0.21/0.45  % SZS output end Proof for theBenchmark
% 0.21/0.45  % (25176)------------------------------
% 0.21/0.45  % (25176)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.45  % (25176)Termination reason: Refutation
% 0.21/0.45  
% 0.21/0.45  % (25176)Memory used [KB]: 6396
% 0.21/0.45  % (25176)Time elapsed: 0.039 s
% 0.21/0.45  % (25176)------------------------------
% 0.21/0.45  % (25176)------------------------------
% 0.21/0.45  % (25165)Success in time 0.091 s
%------------------------------------------------------------------------------
