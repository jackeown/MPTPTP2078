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
% DateTime   : Thu Dec  3 13:13:40 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 111 expanded)
%              Number of leaves         :   17 (  45 expanded)
%              Depth                    :    6
%              Number of atoms          :  208 ( 342 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f98,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f29,f34,f39,f44,f56,f61,f67,f72,f81,f84,f90,f93])).

fof(f93,plain,
    ( spl3_6
    | ~ spl3_12 ),
    inference(avatar_contradiction_clause,[],[f91])).

fof(f91,plain,
    ( $false
    | spl3_6
    | ~ spl3_12 ),
    inference(resolution,[],[f89,f55])).

fof(f55,plain,
    ( ~ v2_tops_2(k4_xboole_0(sK1,sK2),sK0)
    | spl3_6 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl3_6
  <=> v2_tops_2(k4_xboole_0(sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f89,plain,
    ( ! [X0] : v2_tops_2(k4_xboole_0(sK1,X0),sK0)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl3_12
  <=> ! [X0] : v2_tops_2(k4_xboole_0(sK1,X0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f90,plain,
    ( spl3_12
    | ~ spl3_2
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f86,f79,f31,f88])).

fof(f31,plain,
    ( spl3_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f79,plain,
    ( spl3_11
  <=> ! [X1,X0] :
        ( v2_tops_2(k4_xboole_0(sK1,X0),sK0)
        | ~ r1_tarski(k4_xboole_0(sK1,X0),X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f86,plain,
    ( ! [X0] : v2_tops_2(k4_xboole_0(sK1,X0),sK0)
    | ~ spl3_2
    | ~ spl3_11 ),
    inference(subsumption_resolution,[],[f85,f33])).

fof(f33,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f31])).

fof(f85,plain,
    ( ! [X0] :
        ( v2_tops_2(k4_xboole_0(sK1,X0),sK0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
    | ~ spl3_11 ),
    inference(resolution,[],[f80,f23])).

fof(f23,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f80,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k4_xboole_0(sK1,X0),X1)
        | v2_tops_2(k4_xboole_0(sK1,X0),sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f79])).

fof(f84,plain,
    ( ~ spl3_1
    | spl3_10 ),
    inference(avatar_contradiction_clause,[],[f83])).

fof(f83,plain,
    ( $false
    | ~ spl3_1
    | spl3_10 ),
    inference(subsumption_resolution,[],[f82,f28])).

fof(f28,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f26])).

fof(f26,plain,
    ( spl3_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f82,plain,
    ( ~ l1_pre_topc(sK0)
    | spl3_10 ),
    inference(resolution,[],[f77,f21])).

fof(f21,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f77,plain,
    ( ~ l1_struct_0(sK0)
    | spl3_10 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl3_10
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f81,plain,
    ( ~ spl3_10
    | spl3_11
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f73,f70,f79,f75])).

fof(f70,plain,
    ( spl3_9
  <=> ! [X0] :
        ( ~ m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | v2_tops_2(k4_xboole_0(sK1,X0),sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f73,plain,
    ( ! [X0,X1] :
        ( v2_tops_2(k4_xboole_0(sK1,X0),sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ r1_tarski(k4_xboole_0(sK1,X0),X1)
        | ~ l1_struct_0(sK0) )
    | ~ spl3_9 ),
    inference(resolution,[],[f71,f20])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ r1_tarski(X2,X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
              | ~ r1_tarski(X2,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( r1_tarski(X2,X1)
             => m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_tops_2)).

fof(f71,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | v2_tops_2(k4_xboole_0(sK1,X0),sK0) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f70])).

fof(f72,plain,
    ( spl3_9
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f68,f65,f70])).

fof(f65,plain,
    ( spl3_8
  <=> ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | v2_tops_2(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f68,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | v2_tops_2(k4_xboole_0(sK1,X0),sK0) )
    | ~ spl3_8 ),
    inference(resolution,[],[f66,f23])).

fof(f66,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | v2_tops_2(X0,sK0) )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f65])).

fof(f67,plain,
    ( spl3_8
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f63,f59,f41,f31,f65])).

fof(f41,plain,
    ( spl3_4
  <=> v2_tops_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f59,plain,
    ( spl3_7
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ r1_tarski(X0,X1)
        | ~ v2_tops_2(X1,sK0)
        | v2_tops_2(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f63,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | v2_tops_2(X0,sK0) )
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f62,f33])).

fof(f62,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ r1_tarski(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | v2_tops_2(X0,sK0) )
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(resolution,[],[f60,f43])).

fof(f43,plain,
    ( v2_tops_2(sK1,sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f41])).

fof(f60,plain,
    ( ! [X0,X1] :
        ( ~ v2_tops_2(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | v2_tops_2(X0,sK0) )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f59])).

fof(f61,plain,
    ( spl3_7
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f57,f26,f59])).

fof(f57,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ r1_tarski(X0,X1)
        | ~ v2_tops_2(X1,sK0)
        | v2_tops_2(X0,sK0) )
    | ~ spl3_1 ),
    inference(resolution,[],[f22,f28])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ r1_tarski(X1,X2)
      | ~ v2_tops_2(X2,X0)
      | v2_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_tops_2(X1,X0)
              | ~ v2_tops_2(X2,X0)
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_tops_2(X1,X0)
              | ~ v2_tops_2(X2,X0)
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( ( v2_tops_2(X2,X0)
                  & r1_tarski(X1,X2) )
               => v2_tops_2(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_tops_2)).

fof(f56,plain,
    ( ~ spl3_6
    | ~ spl3_2
    | spl3_3 ),
    inference(avatar_split_clause,[],[f51,f36,f31,f53])).

fof(f36,plain,
    ( spl3_3
  <=> v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f51,plain,
    ( ~ v2_tops_2(k4_xboole_0(sK1,sK2),sK0)
    | ~ spl3_2
    | spl3_3 ),
    inference(subsumption_resolution,[],[f50,f33])).

fof(f50,plain,
    ( ~ v2_tops_2(k4_xboole_0(sK1,sK2),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | spl3_3 ),
    inference(superposition,[],[f38,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f38,plain,
    ( ~ v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f36])).

fof(f44,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f16,f41])).

fof(f16,plain,(
    v2_tops_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
              & v2_tops_2(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
              & v2_tops_2(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => ( v2_tops_2(X1,X0)
                 => v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( v2_tops_2(X1,X0)
               => v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_tops_2)).

fof(f39,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f17,f36])).

fof(f17,plain,(
    ~ v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f34,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f18,f31])).

fof(f18,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f9])).

fof(f29,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f19,f26])).

fof(f19,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:22:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.41  % (24348)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.19/0.41  % (24348)Refutation found. Thanks to Tanya!
% 0.19/0.41  % SZS status Theorem for theBenchmark
% 0.19/0.41  % SZS output start Proof for theBenchmark
% 0.19/0.41  fof(f98,plain,(
% 0.19/0.41    $false),
% 0.19/0.41    inference(avatar_sat_refutation,[],[f29,f34,f39,f44,f56,f61,f67,f72,f81,f84,f90,f93])).
% 0.19/0.41  fof(f93,plain,(
% 0.19/0.41    spl3_6 | ~spl3_12),
% 0.19/0.41    inference(avatar_contradiction_clause,[],[f91])).
% 0.19/0.41  fof(f91,plain,(
% 0.19/0.41    $false | (spl3_6 | ~spl3_12)),
% 0.19/0.41    inference(resolution,[],[f89,f55])).
% 0.19/0.41  fof(f55,plain,(
% 0.19/0.41    ~v2_tops_2(k4_xboole_0(sK1,sK2),sK0) | spl3_6),
% 0.19/0.41    inference(avatar_component_clause,[],[f53])).
% 0.19/0.41  fof(f53,plain,(
% 0.19/0.41    spl3_6 <=> v2_tops_2(k4_xboole_0(sK1,sK2),sK0)),
% 0.19/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.19/0.41  fof(f89,plain,(
% 0.19/0.41    ( ! [X0] : (v2_tops_2(k4_xboole_0(sK1,X0),sK0)) ) | ~spl3_12),
% 0.19/0.41    inference(avatar_component_clause,[],[f88])).
% 0.19/0.41  fof(f88,plain,(
% 0.19/0.41    spl3_12 <=> ! [X0] : v2_tops_2(k4_xboole_0(sK1,X0),sK0)),
% 0.19/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.19/0.41  fof(f90,plain,(
% 0.19/0.41    spl3_12 | ~spl3_2 | ~spl3_11),
% 0.19/0.41    inference(avatar_split_clause,[],[f86,f79,f31,f88])).
% 0.19/0.41  fof(f31,plain,(
% 0.19/0.41    spl3_2 <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.19/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.19/0.41  fof(f79,plain,(
% 0.19/0.41    spl3_11 <=> ! [X1,X0] : (v2_tops_2(k4_xboole_0(sK1,X0),sK0) | ~r1_tarski(k4_xboole_0(sK1,X0),X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))),
% 0.19/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.19/0.41  fof(f86,plain,(
% 0.19/0.41    ( ! [X0] : (v2_tops_2(k4_xboole_0(sK1,X0),sK0)) ) | (~spl3_2 | ~spl3_11)),
% 0.19/0.41    inference(subsumption_resolution,[],[f85,f33])).
% 0.19/0.41  fof(f33,plain,(
% 0.19/0.41    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl3_2),
% 0.19/0.41    inference(avatar_component_clause,[],[f31])).
% 0.19/0.41  fof(f85,plain,(
% 0.19/0.41    ( ! [X0] : (v2_tops_2(k4_xboole_0(sK1,X0),sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) ) | ~spl3_11),
% 0.19/0.41    inference(resolution,[],[f80,f23])).
% 0.19/0.41  fof(f23,plain,(
% 0.19/0.41    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.19/0.41    inference(cnf_transformation,[],[f1])).
% 0.19/0.41  fof(f1,axiom,(
% 0.19/0.41    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.19/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.19/0.41  fof(f80,plain,(
% 0.19/0.41    ( ! [X0,X1] : (~r1_tarski(k4_xboole_0(sK1,X0),X1) | v2_tops_2(k4_xboole_0(sK1,X0),sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) ) | ~spl3_11),
% 0.19/0.41    inference(avatar_component_clause,[],[f79])).
% 0.19/0.41  fof(f84,plain,(
% 0.19/0.41    ~spl3_1 | spl3_10),
% 0.19/0.41    inference(avatar_contradiction_clause,[],[f83])).
% 0.19/0.41  fof(f83,plain,(
% 0.19/0.41    $false | (~spl3_1 | spl3_10)),
% 0.19/0.41    inference(subsumption_resolution,[],[f82,f28])).
% 0.19/0.41  fof(f28,plain,(
% 0.19/0.41    l1_pre_topc(sK0) | ~spl3_1),
% 0.19/0.41    inference(avatar_component_clause,[],[f26])).
% 0.19/0.41  fof(f26,plain,(
% 0.19/0.41    spl3_1 <=> l1_pre_topc(sK0)),
% 0.19/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.19/0.41  fof(f82,plain,(
% 0.19/0.41    ~l1_pre_topc(sK0) | spl3_10),
% 0.19/0.41    inference(resolution,[],[f77,f21])).
% 0.19/0.41  fof(f21,plain,(
% 0.19/0.41    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.19/0.41    inference(cnf_transformation,[],[f11])).
% 0.19/0.41  fof(f11,plain,(
% 0.19/0.41    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.19/0.41    inference(ennf_transformation,[],[f3])).
% 0.19/0.41  fof(f3,axiom,(
% 0.19/0.41    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.19/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.19/0.41  fof(f77,plain,(
% 0.19/0.41    ~l1_struct_0(sK0) | spl3_10),
% 0.19/0.41    inference(avatar_component_clause,[],[f75])).
% 0.19/0.41  fof(f75,plain,(
% 0.19/0.41    spl3_10 <=> l1_struct_0(sK0)),
% 0.19/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.19/0.41  fof(f81,plain,(
% 0.19/0.41    ~spl3_10 | spl3_11 | ~spl3_9),
% 0.19/0.41    inference(avatar_split_clause,[],[f73,f70,f79,f75])).
% 0.19/0.41  fof(f70,plain,(
% 0.19/0.41    spl3_9 <=> ! [X0] : (~m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_2(k4_xboole_0(sK1,X0),sK0))),
% 0.19/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.19/0.41  fof(f73,plain,(
% 0.19/0.41    ( ! [X0,X1] : (v2_tops_2(k4_xboole_0(sK1,X0),sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~r1_tarski(k4_xboole_0(sK1,X0),X1) | ~l1_struct_0(sK0)) ) | ~spl3_9),
% 0.19/0.41    inference(resolution,[],[f71,f20])).
% 0.19/0.41  fof(f20,plain,(
% 0.19/0.41    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~l1_struct_0(X0)) )),
% 0.19/0.41    inference(cnf_transformation,[],[f10])).
% 0.19/0.41  fof(f10,plain,(
% 0.19/0.41    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_struct_0(X0))),
% 0.19/0.41    inference(ennf_transformation,[],[f5])).
% 0.19/0.41  fof(f5,axiom,(
% 0.19/0.41    ! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (r1_tarski(X2,X1) => m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))))),
% 0.19/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_tops_2)).
% 0.19/0.41  fof(f71,plain,(
% 0.19/0.41    ( ! [X0] : (~m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_2(k4_xboole_0(sK1,X0),sK0)) ) | ~spl3_9),
% 0.19/0.41    inference(avatar_component_clause,[],[f70])).
% 0.19/0.41  fof(f72,plain,(
% 0.19/0.41    spl3_9 | ~spl3_8),
% 0.19/0.41    inference(avatar_split_clause,[],[f68,f65,f70])).
% 0.19/0.41  fof(f65,plain,(
% 0.19/0.41    spl3_8 <=> ! [X0] : (~r1_tarski(X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_2(X0,sK0))),
% 0.19/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.19/0.41  fof(f68,plain,(
% 0.19/0.41    ( ! [X0] : (~m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_2(k4_xboole_0(sK1,X0),sK0)) ) | ~spl3_8),
% 0.19/0.41    inference(resolution,[],[f66,f23])).
% 0.19/0.41  fof(f66,plain,(
% 0.19/0.41    ( ! [X0] : (~r1_tarski(X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_2(X0,sK0)) ) | ~spl3_8),
% 0.19/0.41    inference(avatar_component_clause,[],[f65])).
% 0.19/0.41  fof(f67,plain,(
% 0.19/0.41    spl3_8 | ~spl3_2 | ~spl3_4 | ~spl3_7),
% 0.19/0.41    inference(avatar_split_clause,[],[f63,f59,f41,f31,f65])).
% 0.19/0.42  fof(f41,plain,(
% 0.19/0.42    spl3_4 <=> v2_tops_2(sK1,sK0)),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.19/0.42  fof(f59,plain,(
% 0.19/0.42    spl3_7 <=> ! [X1,X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~r1_tarski(X0,X1) | ~v2_tops_2(X1,sK0) | v2_tops_2(X0,sK0))),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.19/0.42  fof(f63,plain,(
% 0.19/0.42    ( ! [X0] : (~r1_tarski(X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_2(X0,sK0)) ) | (~spl3_2 | ~spl3_4 | ~spl3_7)),
% 0.19/0.42    inference(subsumption_resolution,[],[f62,f33])).
% 0.19/0.42  fof(f62,plain,(
% 0.19/0.42    ( ! [X0] : (~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~r1_tarski(X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_2(X0,sK0)) ) | (~spl3_4 | ~spl3_7)),
% 0.19/0.42    inference(resolution,[],[f60,f43])).
% 0.19/0.42  fof(f43,plain,(
% 0.19/0.42    v2_tops_2(sK1,sK0) | ~spl3_4),
% 0.19/0.42    inference(avatar_component_clause,[],[f41])).
% 0.19/0.42  fof(f60,plain,(
% 0.19/0.42    ( ! [X0,X1] : (~v2_tops_2(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_2(X0,sK0)) ) | ~spl3_7),
% 0.19/0.42    inference(avatar_component_clause,[],[f59])).
% 0.19/0.42  fof(f61,plain,(
% 0.19/0.42    spl3_7 | ~spl3_1),
% 0.19/0.42    inference(avatar_split_clause,[],[f57,f26,f59])).
% 0.19/0.42  fof(f57,plain,(
% 0.19/0.42    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~r1_tarski(X0,X1) | ~v2_tops_2(X1,sK0) | v2_tops_2(X0,sK0)) ) | ~spl3_1),
% 0.19/0.42    inference(resolution,[],[f22,f28])).
% 0.19/0.42  fof(f22,plain,(
% 0.19/0.42    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X1,X2) | ~v2_tops_2(X2,X0) | v2_tops_2(X1,X0)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f13])).
% 0.19/0.42  fof(f13,plain,(
% 0.19/0.42    ! [X0] : (! [X1] : (! [X2] : (v2_tops_2(X1,X0) | ~v2_tops_2(X2,X0) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.19/0.42    inference(flattening,[],[f12])).
% 0.19/0.42  fof(f12,plain,(
% 0.19/0.42    ! [X0] : (! [X1] : (! [X2] : ((v2_tops_2(X1,X0) | (~v2_tops_2(X2,X0) | ~r1_tarski(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.19/0.42    inference(ennf_transformation,[],[f4])).
% 0.19/0.42  fof(f4,axiom,(
% 0.19/0.42    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ((v2_tops_2(X2,X0) & r1_tarski(X1,X2)) => v2_tops_2(X1,X0)))))),
% 0.19/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_tops_2)).
% 0.19/0.42  fof(f56,plain,(
% 0.19/0.42    ~spl3_6 | ~spl3_2 | spl3_3),
% 0.19/0.42    inference(avatar_split_clause,[],[f51,f36,f31,f53])).
% 0.19/0.42  fof(f36,plain,(
% 0.19/0.42    spl3_3 <=> v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.19/0.42  fof(f51,plain,(
% 0.19/0.42    ~v2_tops_2(k4_xboole_0(sK1,sK2),sK0) | (~spl3_2 | spl3_3)),
% 0.19/0.42    inference(subsumption_resolution,[],[f50,f33])).
% 0.19/0.42  fof(f50,plain,(
% 0.19/0.42    ~v2_tops_2(k4_xboole_0(sK1,sK2),sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | spl3_3),
% 0.19/0.42    inference(superposition,[],[f38,f24])).
% 0.19/0.42  fof(f24,plain,(
% 0.19/0.42    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.19/0.42    inference(cnf_transformation,[],[f14])).
% 0.19/0.42  fof(f14,plain,(
% 0.19/0.42    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.42    inference(ennf_transformation,[],[f2])).
% 0.19/0.42  fof(f2,axiom,(
% 0.19/0.42    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 0.19/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 0.19/0.42  fof(f38,plain,(
% 0.19/0.42    ~v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) | spl3_3),
% 0.19/0.42    inference(avatar_component_clause,[],[f36])).
% 0.19/0.42  fof(f44,plain,(
% 0.19/0.42    spl3_4),
% 0.19/0.42    inference(avatar_split_clause,[],[f16,f41])).
% 0.19/0.42  fof(f16,plain,(
% 0.19/0.42    v2_tops_2(sK1,sK0)),
% 0.19/0.42    inference(cnf_transformation,[],[f9])).
% 0.19/0.42  fof(f9,plain,(
% 0.19/0.42    ? [X0] : (? [X1] : (? [X2] : (~v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v2_tops_2(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 0.19/0.42    inference(flattening,[],[f8])).
% 0.19/0.42  fof(f8,plain,(
% 0.19/0.42    ? [X0] : (? [X1] : (? [X2] : ((~v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v2_tops_2(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 0.19/0.42    inference(ennf_transformation,[],[f7])).
% 0.19/0.42  fof(f7,negated_conjecture,(
% 0.19/0.42    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v2_tops_2(X1,X0) => v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)))))),
% 0.19/0.42    inference(negated_conjecture,[],[f6])).
% 0.19/0.42  fof(f6,conjecture,(
% 0.19/0.42    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v2_tops_2(X1,X0) => v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)))))),
% 0.19/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_tops_2)).
% 0.19/0.42  fof(f39,plain,(
% 0.19/0.42    ~spl3_3),
% 0.19/0.42    inference(avatar_split_clause,[],[f17,f36])).
% 0.19/0.42  fof(f17,plain,(
% 0.19/0.42    ~v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)),
% 0.19/0.42    inference(cnf_transformation,[],[f9])).
% 0.19/0.42  fof(f34,plain,(
% 0.19/0.42    spl3_2),
% 0.19/0.42    inference(avatar_split_clause,[],[f18,f31])).
% 0.19/0.42  fof(f18,plain,(
% 0.19/0.42    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.19/0.42    inference(cnf_transformation,[],[f9])).
% 0.19/0.42  fof(f29,plain,(
% 0.19/0.42    spl3_1),
% 0.19/0.42    inference(avatar_split_clause,[],[f19,f26])).
% 0.19/0.42  fof(f19,plain,(
% 0.19/0.42    l1_pre_topc(sK0)),
% 0.19/0.42    inference(cnf_transformation,[],[f9])).
% 0.19/0.42  % SZS output end Proof for theBenchmark
% 0.19/0.42  % (24348)------------------------------
% 0.19/0.42  % (24348)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.42  % (24348)Termination reason: Refutation
% 0.19/0.42  
% 0.19/0.42  % (24348)Memory used [KB]: 10618
% 0.19/0.42  % (24348)Time elapsed: 0.008 s
% 0.19/0.42  % (24348)------------------------------
% 0.19/0.42  % (24348)------------------------------
% 0.19/0.42  % (24354)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.19/0.42  % (24342)Success in time 0.067 s
%------------------------------------------------------------------------------
