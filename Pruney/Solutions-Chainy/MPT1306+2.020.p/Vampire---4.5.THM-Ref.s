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
% DateTime   : Thu Dec  3 13:13:38 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 119 expanded)
%              Number of leaves         :   18 (  48 expanded)
%              Depth                    :    6
%              Number of atoms          :  206 ( 354 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f213,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f30,f35,f40,f45,f50,f57,f62,f68,f87,f113,f134,f173,f212])).

fof(f212,plain,
    ( ~ spl3_2
    | spl3_22 ),
    inference(avatar_contradiction_clause,[],[f211])).

fof(f211,plain,
    ( $false
    | ~ spl3_2
    | spl3_22 ),
    inference(subsumption_resolution,[],[f206,f34])).

fof(f34,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f32])).

fof(f32,plain,
    ( spl3_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f206,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | spl3_22 ),
    inference(resolution,[],[f172,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f172,plain,
    ( ~ r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_22 ),
    inference(avatar_component_clause,[],[f170])).

fof(f170,plain,
    ( spl3_22
  <=> r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f173,plain,
    ( ~ spl3_22
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f166,f132,f170])).

fof(f132,plain,
    ( spl3_18
  <=> ! [X0] :
        ( ~ r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(k3_xboole_0(sK1,sK2),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f166,plain,
    ( ~ r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_18 ),
    inference(resolution,[],[f133,f21])).

fof(f21,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f133,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k3_xboole_0(sK1,sK2),X0)
        | ~ r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f132])).

fof(f134,plain,
    ( spl3_18
    | spl3_15 ),
    inference(avatar_split_clause,[],[f129,f110,f132])).

fof(f110,plain,
    ( spl3_15
  <=> r1_tarski(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f129,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(k3_xboole_0(sK1,sK2),X0) )
    | spl3_15 ),
    inference(resolution,[],[f112,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f112,plain,
    ( ~ r1_tarski(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_15 ),
    inference(avatar_component_clause,[],[f110])).

fof(f113,plain,
    ( ~ spl3_15
    | spl3_11 ),
    inference(avatar_split_clause,[],[f108,f84,f110])).

fof(f84,plain,
    ( spl3_11
  <=> m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f108,plain,
    ( ~ r1_tarski(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_11 ),
    inference(resolution,[],[f86,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f86,plain,
    ( ~ m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | spl3_11 ),
    inference(avatar_component_clause,[],[f84])).

fof(f87,plain,
    ( ~ spl3_11
    | spl3_6
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f82,f66,f54,f84])).

fof(f54,plain,
    ( spl3_6
  <=> v2_tops_2(k3_xboole_0(sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f66,plain,
    ( spl3_8
  <=> ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | v2_tops_2(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f82,plain,
    ( ~ m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | spl3_6
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f70,f21])).

fof(f70,plain,
    ( ~ m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ r1_tarski(k3_xboole_0(sK1,sK2),sK1)
    | spl3_6
    | ~ spl3_8 ),
    inference(resolution,[],[f67,f56])).

fof(f56,plain,
    ( ~ v2_tops_2(k3_xboole_0(sK1,sK2),sK0)
    | spl3_6 ),
    inference(avatar_component_clause,[],[f54])).

fof(f67,plain,
    ( ! [X0] :
        ( v2_tops_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ r1_tarski(X0,sK1) )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f66])).

fof(f68,plain,
    ( spl3_8
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f64,f60,f42,f32,f66])).

fof(f42,plain,
    ( spl3_4
  <=> v2_tops_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f60,plain,
    ( spl3_7
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ r1_tarski(X0,X1)
        | ~ v2_tops_2(X1,sK0)
        | v2_tops_2(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f64,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | v2_tops_2(X0,sK0) )
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f63,f34])).

fof(f63,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ r1_tarski(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | v2_tops_2(X0,sK0) )
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(resolution,[],[f61,f44])).

fof(f44,plain,
    ( v2_tops_2(sK1,sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f42])).

fof(f61,plain,
    ( ! [X0,X1] :
        ( ~ v2_tops_2(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | v2_tops_2(X0,sK0) )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f60])).

fof(f62,plain,
    ( spl3_7
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f58,f27,f60])).

fof(f27,plain,
    ( spl3_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f58,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ r1_tarski(X0,X1)
        | ~ v2_tops_2(X1,sK0)
        | v2_tops_2(X0,sK0) )
    | ~ spl3_1 ),
    inference(resolution,[],[f20,f29])).

fof(f29,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f27])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ r1_tarski(X1,X2)
      | ~ v2_tops_2(X2,X0)
      | v2_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_tops_2(X1,X0)
              | ~ v2_tops_2(X2,X0)
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_tops_2(X1,X0)
              | ~ v2_tops_2(X2,X0)
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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

fof(f57,plain,
    ( ~ spl3_6
    | spl3_3
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f52,f47,f37,f54])).

fof(f37,plain,
    ( spl3_3
  <=> v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f47,plain,
    ( spl3_5
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f52,plain,
    ( ~ v2_tops_2(k3_xboole_0(sK1,sK2),sK0)
    | spl3_3
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f51,f49])).

fof(f49,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f47])).

fof(f51,plain,
    ( ~ v2_tops_2(k3_xboole_0(sK1,sK2),sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | spl3_3 ),
    inference(superposition,[],[f39,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f39,plain,
    ( ~ v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f37])).

% (31644)lrs+1004_5:4_aac=none:add=large:afp=100000:afq=1.4:anc=all_dependent:bd=off:cond=fast:gsp=input_only:gs=on:gsem=off:lma=on:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sp=occurrence:updr=off:uhcvi=on_99 on theBenchmark
fof(f50,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f15,f47])).

fof(f15,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
              & v2_tops_2(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
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
                 => v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( v2_tops_2(X1,X0)
               => v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_tops_2)).

fof(f45,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f16,f42])).

fof(f16,plain,(
    v2_tops_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f40,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f17,f37])).

fof(f17,plain,(
    ~ v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f35,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f18,f32])).

fof(f18,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f9])).

fof(f30,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f19,f27])).

fof(f19,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:12:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.41  % (31646)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.20/0.41  % (31650)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.21/0.43  % (31642)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.21/0.43  % (31645)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.21/0.43  % (31643)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
% 0.21/0.43  % (31642)Refutation found. Thanks to Tanya!
% 0.21/0.43  % SZS status Theorem for theBenchmark
% 0.21/0.43  % SZS output start Proof for theBenchmark
% 0.21/0.43  fof(f213,plain,(
% 0.21/0.43    $false),
% 0.21/0.43    inference(avatar_sat_refutation,[],[f30,f35,f40,f45,f50,f57,f62,f68,f87,f113,f134,f173,f212])).
% 0.21/0.43  fof(f212,plain,(
% 0.21/0.43    ~spl3_2 | spl3_22),
% 0.21/0.43    inference(avatar_contradiction_clause,[],[f211])).
% 0.21/0.43  fof(f211,plain,(
% 0.21/0.43    $false | (~spl3_2 | spl3_22)),
% 0.21/0.43    inference(subsumption_resolution,[],[f206,f34])).
% 0.21/0.43  fof(f34,plain,(
% 0.21/0.43    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl3_2),
% 0.21/0.43    inference(avatar_component_clause,[],[f32])).
% 0.21/0.43  fof(f32,plain,(
% 0.21/0.43    spl3_2 <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.43  fof(f206,plain,(
% 0.21/0.43    ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | spl3_22),
% 0.21/0.43    inference(resolution,[],[f172,f23])).
% 0.21/0.43  fof(f23,plain,(
% 0.21/0.43    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f4])).
% 0.21/0.43  fof(f4,axiom,(
% 0.21/0.43    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.43  fof(f172,plain,(
% 0.21/0.43    ~r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_22),
% 0.21/0.43    inference(avatar_component_clause,[],[f170])).
% 0.21/0.43  fof(f170,plain,(
% 0.21/0.43    spl3_22 <=> r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.21/0.43  fof(f173,plain,(
% 0.21/0.43    ~spl3_22 | ~spl3_18),
% 0.21/0.43    inference(avatar_split_clause,[],[f166,f132,f170])).
% 0.21/0.43  fof(f132,plain,(
% 0.21/0.43    spl3_18 <=> ! [X0] : (~r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(k3_xboole_0(sK1,sK2),X0))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.21/0.43  fof(f166,plain,(
% 0.21/0.43    ~r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_18),
% 0.21/0.43    inference(resolution,[],[f133,f21])).
% 0.21/0.43  fof(f21,plain,(
% 0.21/0.43    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f1])).
% 0.21/0.43  fof(f1,axiom,(
% 0.21/0.43    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.21/0.43  fof(f133,plain,(
% 0.21/0.43    ( ! [X0] : (~r1_tarski(k3_xboole_0(sK1,sK2),X0) | ~r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl3_18),
% 0.21/0.43    inference(avatar_component_clause,[],[f132])).
% 0.21/0.43  fof(f134,plain,(
% 0.21/0.43    spl3_18 | spl3_15),
% 0.21/0.43    inference(avatar_split_clause,[],[f129,f110,f132])).
% 0.21/0.43  fof(f110,plain,(
% 0.21/0.43    spl3_15 <=> r1_tarski(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.21/0.43  fof(f129,plain,(
% 0.21/0.43    ( ! [X0] : (~r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(k3_xboole_0(sK1,sK2),X0)) ) | spl3_15),
% 0.21/0.43    inference(resolution,[],[f112,f25])).
% 0.21/0.43  fof(f25,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f14])).
% 0.21/0.43  fof(f14,plain,(
% 0.21/0.43    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.43    inference(flattening,[],[f13])).
% 0.21/0.43  fof(f13,plain,(
% 0.21/0.43    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.43    inference(ennf_transformation,[],[f2])).
% 0.21/0.43  fof(f2,axiom,(
% 0.21/0.43    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.21/0.43  fof(f112,plain,(
% 0.21/0.43    ~r1_tarski(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_15),
% 0.21/0.43    inference(avatar_component_clause,[],[f110])).
% 0.21/0.43  fof(f113,plain,(
% 0.21/0.43    ~spl3_15 | spl3_11),
% 0.21/0.43    inference(avatar_split_clause,[],[f108,f84,f110])).
% 0.21/0.43  fof(f84,plain,(
% 0.21/0.43    spl3_11 <=> m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.43  fof(f108,plain,(
% 0.21/0.43    ~r1_tarski(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_11),
% 0.21/0.43    inference(resolution,[],[f86,f22])).
% 0.21/0.43  fof(f22,plain,(
% 0.21/0.43    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f4])).
% 0.21/0.43  fof(f86,plain,(
% 0.21/0.43    ~m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | spl3_11),
% 0.21/0.43    inference(avatar_component_clause,[],[f84])).
% 0.21/0.43  fof(f87,plain,(
% 0.21/0.43    ~spl3_11 | spl3_6 | ~spl3_8),
% 0.21/0.43    inference(avatar_split_clause,[],[f82,f66,f54,f84])).
% 0.21/0.43  fof(f54,plain,(
% 0.21/0.43    spl3_6 <=> v2_tops_2(k3_xboole_0(sK1,sK2),sK0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.43  fof(f66,plain,(
% 0.21/0.43    spl3_8 <=> ! [X0] : (~r1_tarski(X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_2(X0,sK0))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.43  fof(f82,plain,(
% 0.21/0.43    ~m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | (spl3_6 | ~spl3_8)),
% 0.21/0.43    inference(subsumption_resolution,[],[f70,f21])).
% 0.21/0.43  fof(f70,plain,(
% 0.21/0.43    ~m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~r1_tarski(k3_xboole_0(sK1,sK2),sK1) | (spl3_6 | ~spl3_8)),
% 0.21/0.43    inference(resolution,[],[f67,f56])).
% 0.21/0.44  fof(f56,plain,(
% 0.21/0.44    ~v2_tops_2(k3_xboole_0(sK1,sK2),sK0) | spl3_6),
% 0.21/0.44    inference(avatar_component_clause,[],[f54])).
% 0.21/0.44  fof(f67,plain,(
% 0.21/0.44    ( ! [X0] : (v2_tops_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~r1_tarski(X0,sK1)) ) | ~spl3_8),
% 0.21/0.44    inference(avatar_component_clause,[],[f66])).
% 0.21/0.44  fof(f68,plain,(
% 0.21/0.44    spl3_8 | ~spl3_2 | ~spl3_4 | ~spl3_7),
% 0.21/0.44    inference(avatar_split_clause,[],[f64,f60,f42,f32,f66])).
% 0.21/0.44  fof(f42,plain,(
% 0.21/0.44    spl3_4 <=> v2_tops_2(sK1,sK0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.44  fof(f60,plain,(
% 0.21/0.44    spl3_7 <=> ! [X1,X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~r1_tarski(X0,X1) | ~v2_tops_2(X1,sK0) | v2_tops_2(X0,sK0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.44  fof(f64,plain,(
% 0.21/0.44    ( ! [X0] : (~r1_tarski(X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_2(X0,sK0)) ) | (~spl3_2 | ~spl3_4 | ~spl3_7)),
% 0.21/0.44    inference(subsumption_resolution,[],[f63,f34])).
% 0.21/0.44  fof(f63,plain,(
% 0.21/0.44    ( ! [X0] : (~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~r1_tarski(X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_2(X0,sK0)) ) | (~spl3_4 | ~spl3_7)),
% 0.21/0.44    inference(resolution,[],[f61,f44])).
% 0.21/0.44  fof(f44,plain,(
% 0.21/0.44    v2_tops_2(sK1,sK0) | ~spl3_4),
% 0.21/0.44    inference(avatar_component_clause,[],[f42])).
% 0.21/0.44  fof(f61,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~v2_tops_2(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_2(X0,sK0)) ) | ~spl3_7),
% 0.21/0.44    inference(avatar_component_clause,[],[f60])).
% 0.21/0.44  fof(f62,plain,(
% 0.21/0.44    spl3_7 | ~spl3_1),
% 0.21/0.44    inference(avatar_split_clause,[],[f58,f27,f60])).
% 0.21/0.44  fof(f27,plain,(
% 0.21/0.44    spl3_1 <=> l1_pre_topc(sK0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.44  fof(f58,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~r1_tarski(X0,X1) | ~v2_tops_2(X1,sK0) | v2_tops_2(X0,sK0)) ) | ~spl3_1),
% 0.21/0.44    inference(resolution,[],[f20,f29])).
% 0.21/0.44  fof(f29,plain,(
% 0.21/0.44    l1_pre_topc(sK0) | ~spl3_1),
% 0.21/0.44    inference(avatar_component_clause,[],[f27])).
% 0.21/0.44  fof(f20,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X1,X2) | ~v2_tops_2(X2,X0) | v2_tops_2(X1,X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f11])).
% 0.21/0.44  fof(f11,plain,(
% 0.21/0.44    ! [X0] : (! [X1] : (! [X2] : (v2_tops_2(X1,X0) | ~v2_tops_2(X2,X0) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.21/0.44    inference(flattening,[],[f10])).
% 0.21/0.44  fof(f10,plain,(
% 0.21/0.44    ! [X0] : (! [X1] : (! [X2] : ((v2_tops_2(X1,X0) | (~v2_tops_2(X2,X0) | ~r1_tarski(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.21/0.44    inference(ennf_transformation,[],[f5])).
% 0.21/0.44  fof(f5,axiom,(
% 0.21/0.44    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ((v2_tops_2(X2,X0) & r1_tarski(X1,X2)) => v2_tops_2(X1,X0)))))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_tops_2)).
% 0.21/0.44  fof(f57,plain,(
% 0.21/0.44    ~spl3_6 | spl3_3 | ~spl3_5),
% 0.21/0.44    inference(avatar_split_clause,[],[f52,f47,f37,f54])).
% 0.21/0.44  fof(f37,plain,(
% 0.21/0.44    spl3_3 <=> v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.44  fof(f47,plain,(
% 0.21/0.44    spl3_5 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.44  fof(f52,plain,(
% 0.21/0.44    ~v2_tops_2(k3_xboole_0(sK1,sK2),sK0) | (spl3_3 | ~spl3_5)),
% 0.21/0.44    inference(subsumption_resolution,[],[f51,f49])).
% 0.21/0.44  fof(f49,plain,(
% 0.21/0.44    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl3_5),
% 0.21/0.44    inference(avatar_component_clause,[],[f47])).
% 0.21/0.44  fof(f51,plain,(
% 0.21/0.44    ~v2_tops_2(k3_xboole_0(sK1,sK2),sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | spl3_3),
% 0.21/0.44    inference(superposition,[],[f39,f24])).
% 0.21/0.44  fof(f24,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f12])).
% 0.21/0.44  fof(f12,plain,(
% 0.21/0.44    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.21/0.44    inference(ennf_transformation,[],[f3])).
% 0.21/0.44  fof(f3,axiom,(
% 0.21/0.44    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.21/0.44  fof(f39,plain,(
% 0.21/0.44    ~v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) | spl3_3),
% 0.21/0.44    inference(avatar_component_clause,[],[f37])).
% 0.21/0.44  % (31644)lrs+1004_5:4_aac=none:add=large:afp=100000:afq=1.4:anc=all_dependent:bd=off:cond=fast:gsp=input_only:gs=on:gsem=off:lma=on:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sp=occurrence:updr=off:uhcvi=on_99 on theBenchmark
% 0.21/0.44  fof(f50,plain,(
% 0.21/0.44    spl3_5),
% 0.21/0.44    inference(avatar_split_clause,[],[f15,f47])).
% 0.21/0.44  fof(f15,plain,(
% 0.21/0.44    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.44    inference(cnf_transformation,[],[f9])).
% 0.21/0.44  fof(f9,plain,(
% 0.21/0.44    ? [X0] : (? [X1] : (? [X2] : (~v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v2_tops_2(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 0.21/0.44    inference(flattening,[],[f8])).
% 0.21/0.44  fof(f8,plain,(
% 0.21/0.44    ? [X0] : (? [X1] : (? [X2] : ((~v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v2_tops_2(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 0.21/0.44    inference(ennf_transformation,[],[f7])).
% 0.21/0.44  fof(f7,negated_conjecture,(
% 0.21/0.44    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v2_tops_2(X1,X0) => v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)))))),
% 0.21/0.44    inference(negated_conjecture,[],[f6])).
% 0.21/0.44  fof(f6,conjecture,(
% 0.21/0.44    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v2_tops_2(X1,X0) => v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)))))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_tops_2)).
% 0.21/0.44  fof(f45,plain,(
% 0.21/0.44    spl3_4),
% 0.21/0.44    inference(avatar_split_clause,[],[f16,f42])).
% 0.21/0.44  fof(f16,plain,(
% 0.21/0.44    v2_tops_2(sK1,sK0)),
% 0.21/0.44    inference(cnf_transformation,[],[f9])).
% 0.21/0.44  fof(f40,plain,(
% 0.21/0.44    ~spl3_3),
% 0.21/0.44    inference(avatar_split_clause,[],[f17,f37])).
% 0.21/0.44  fof(f17,plain,(
% 0.21/0.44    ~v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)),
% 0.21/0.44    inference(cnf_transformation,[],[f9])).
% 0.21/0.44  fof(f35,plain,(
% 0.21/0.44    spl3_2),
% 0.21/0.44    inference(avatar_split_clause,[],[f18,f32])).
% 0.21/0.44  fof(f18,plain,(
% 0.21/0.44    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.44    inference(cnf_transformation,[],[f9])).
% 0.21/0.44  fof(f30,plain,(
% 0.21/0.44    spl3_1),
% 0.21/0.44    inference(avatar_split_clause,[],[f19,f27])).
% 0.21/0.44  fof(f19,plain,(
% 0.21/0.44    l1_pre_topc(sK0)),
% 0.21/0.44    inference(cnf_transformation,[],[f9])).
% 0.21/0.44  % SZS output end Proof for theBenchmark
% 0.21/0.44  % (31642)------------------------------
% 0.21/0.44  % (31642)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.44  % (31642)Termination reason: Refutation
% 0.21/0.44  
% 0.21/0.44  % (31642)Memory used [KB]: 10618
% 0.21/0.44  % (31642)Time elapsed: 0.038 s
% 0.21/0.44  % (31642)------------------------------
% 0.21/0.44  % (31642)------------------------------
% 0.21/0.44  % (31640)Success in time 0.087 s
%------------------------------------------------------------------------------
