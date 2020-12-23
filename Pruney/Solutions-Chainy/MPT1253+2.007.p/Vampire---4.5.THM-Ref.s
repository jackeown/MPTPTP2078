%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:23 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 112 expanded)
%              Number of leaves         :   18 (  41 expanded)
%              Depth                    :   11
%              Number of atoms          :  203 ( 312 expanded)
%              Number of equality atoms :   15 (  18 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f884,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f94,f99,f104,f109,f148,f226,f237,f879,f883])).

fof(f883,plain,
    ( ~ spl3_1
    | ~ spl3_3
    | spl3_17 ),
    inference(avatar_contradiction_clause,[],[f880])).

fof(f880,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_3
    | spl3_17 ),
    inference(unit_resulting_resolution,[],[f93,f103,f878,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f878,plain,
    ( ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_17 ),
    inference(avatar_component_clause,[],[f876])).

fof(f876,plain,
    ( spl3_17
  <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f103,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl3_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f93,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl3_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f879,plain,
    ( ~ spl3_1
    | ~ spl3_3
    | ~ spl3_17
    | ~ spl3_10
    | spl3_4 ),
    inference(avatar_split_clause,[],[f509,f106,f223,f876,f101,f91])).

fof(f223,plain,
    ( spl3_10
  <=> r1_tarski(k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f106,plain,
    ( spl3_4
  <=> r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f509,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,sK1),sK1)
    | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl3_4 ),
    inference(duplicate_literal_removal,[],[f506])).

fof(f506,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,sK1),sK1)
    | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl3_4 ),
    inference(superposition,[],[f156,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

% (17829)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
fof(f156,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k4_subset_1(X1,X0,k2_tops_1(sK0,sK1)),sK1)
        | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(X1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) )
    | spl3_4 ),
    inference(superposition,[],[f150,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f77,f59])).

fof(f59,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f150,plain,
    ( ! [X0] : ~ r1_tarski(k3_tarski(k2_tarski(X0,k2_tops_1(sK0,sK1))),sK1)
    | spl3_4 ),
    inference(superposition,[],[f119,f57])).

fof(f57,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f119,plain,
    ( ! [X0] : ~ r1_tarski(k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),X0)),sK1)
    | spl3_4 ),
    inference(resolution,[],[f118,f80])).

fof(f80,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f54,f59])).

fof(f54,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f118,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_tops_1(sK0,sK1),X0)
        | ~ r1_tarski(X0,sK1) )
    | spl3_4 ),
    inference(resolution,[],[f108,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f108,plain,
    ( ~ r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f106])).

fof(f237,plain,(
    spl3_9 ),
    inference(avatar_contradiction_clause,[],[f229])).

fof(f229,plain,
    ( $false
    | spl3_9 ),
    inference(unit_resulting_resolution,[],[f89,f88,f221,f76])).

fof(f221,plain,
    ( ~ r1_tarski(sK1,sK1)
    | spl3_9 ),
    inference(avatar_component_clause,[],[f219])).

fof(f219,plain,
    ( spl3_9
  <=> r1_tarski(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f88,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f89,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f226,plain,
    ( ~ spl3_2
    | ~ spl3_9
    | spl3_10
    | ~ spl3_3
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f178,f146,f101,f223,f219,f96])).

fof(f96,plain,
    ( spl3_2
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f146,plain,
    ( spl3_8
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(k2_pre_topc(sK0,sK1),X0)
        | ~ r1_tarski(sK1,X0)
        | ~ v4_pre_topc(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f178,plain,
    ( r1_tarski(k2_pre_topc(sK0,sK1),sK1)
    | ~ r1_tarski(sK1,sK1)
    | ~ v4_pre_topc(sK1,sK0)
    | ~ spl3_3
    | ~ spl3_8 ),
    inference(resolution,[],[f147,f103])).

fof(f147,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(k2_pre_topc(sK0,sK1),X0)
        | ~ r1_tarski(sK1,X0)
        | ~ v4_pre_topc(X0,sK0) )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f146])).

fof(f148,plain,
    ( ~ spl3_1
    | spl3_8
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f110,f101,f146,f91])).

fof(f110,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v4_pre_topc(X0,sK0)
        | ~ r1_tarski(sK1,X0)
        | r1_tarski(k2_pre_topc(sK0,sK1),X0) )
    | ~ spl3_3 ),
    inference(resolution,[],[f103,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ r1_tarski(X2,X1)
      | r1_tarski(k2_pre_topc(X0,X2),X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X2),X1)
              | ~ r1_tarski(X2,X1)
              | ~ v4_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X2),X1)
              | ~ r1_tarski(X2,X1)
              | ~ v4_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_tarski(X2,X1)
                  & v4_pre_topc(X1,X0) )
               => r1_tarski(k2_pre_topc(X0,X2),X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_tops_1)).

fof(f109,plain,(
    ~ spl3_4 ),
    inference(avatar_split_clause,[],[f47,f106])).

fof(f47,plain,(
    ~ r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(X0,X1),X1)
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(X0,X1),X1)
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
             => r1_tarski(k2_tops_1(X0,X1),X1) ) ) ) ),
    inference(negated_conjecture,[],[f25])).

fof(f25,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => r1_tarski(k2_tops_1(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_tops_1)).

fof(f104,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f45,f101])).

fof(f45,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f28])).

fof(f99,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f46,f96])).

fof(f46,plain,(
    v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f94,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f48,f91])).

fof(f48,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:22:35 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (17817)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % (17836)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (17828)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (17833)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.52  % (17827)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.52  % (17824)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.53  % (17814)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (17818)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.53  % (17815)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (17840)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  % (17825)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (17819)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.54  % (17842)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (17839)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.54  % (17838)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.54  % (17841)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.55  % (17830)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.55  % (17831)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.55  % (17834)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.55  % (17832)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.55  % (17816)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.55  % (17843)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.55  % (17823)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.56  % (17820)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.56  % (17826)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.56  % (17835)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.56  % (17822)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.56  % (17836)Refutation found. Thanks to Tanya!
% 0.21/0.56  % SZS status Theorem for theBenchmark
% 0.21/0.56  % SZS output start Proof for theBenchmark
% 0.21/0.56  fof(f884,plain,(
% 0.21/0.56    $false),
% 0.21/0.56    inference(avatar_sat_refutation,[],[f94,f99,f104,f109,f148,f226,f237,f879,f883])).
% 0.21/0.56  fof(f883,plain,(
% 0.21/0.56    ~spl3_1 | ~spl3_3 | spl3_17),
% 0.21/0.56    inference(avatar_contradiction_clause,[],[f880])).
% 0.21/0.56  fof(f880,plain,(
% 0.21/0.56    $false | (~spl3_1 | ~spl3_3 | spl3_17)),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f93,f103,f878,f64])).
% 0.21/0.56  fof(f64,plain,(
% 0.21/0.56    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f36])).
% 0.21/0.56  fof(f36,plain,(
% 0.21/0.56    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.56    inference(flattening,[],[f35])).
% 0.21/0.56  fof(f35,plain,(
% 0.21/0.56    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.21/0.56    inference(ennf_transformation,[],[f21])).
% 0.21/0.56  fof(f21,axiom,(
% 0.21/0.56    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 0.21/0.56  fof(f878,plain,(
% 0.21/0.56    ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_17),
% 0.21/0.56    inference(avatar_component_clause,[],[f876])).
% 0.21/0.56  fof(f876,plain,(
% 0.21/0.56    spl3_17 <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.21/0.56  fof(f103,plain,(
% 0.21/0.56    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_3),
% 0.21/0.56    inference(avatar_component_clause,[],[f101])).
% 0.21/0.56  fof(f101,plain,(
% 0.21/0.56    spl3_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.56  fof(f93,plain,(
% 0.21/0.56    l1_pre_topc(sK0) | ~spl3_1),
% 0.21/0.56    inference(avatar_component_clause,[],[f91])).
% 0.21/0.56  fof(f91,plain,(
% 0.21/0.56    spl3_1 <=> l1_pre_topc(sK0)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.56  fof(f879,plain,(
% 0.21/0.56    ~spl3_1 | ~spl3_3 | ~spl3_17 | ~spl3_10 | spl3_4),
% 0.21/0.56    inference(avatar_split_clause,[],[f509,f106,f223,f876,f101,f91])).
% 0.21/0.56  fof(f223,plain,(
% 0.21/0.56    spl3_10 <=> r1_tarski(k2_pre_topc(sK0,sK1),sK1)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.56  fof(f106,plain,(
% 0.21/0.56    spl3_4 <=> r1_tarski(k2_tops_1(sK0,sK1),sK1)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.56  fof(f509,plain,(
% 0.21/0.56    ~r1_tarski(k2_pre_topc(sK0,sK1),sK1) | ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl3_4),
% 0.21/0.56    inference(duplicate_literal_removal,[],[f506])).
% 0.21/0.56  fof(f506,plain,(
% 0.21/0.56    ~r1_tarski(k2_pre_topc(sK0,sK1),sK1) | ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl3_4),
% 0.21/0.56    inference(superposition,[],[f156,f52])).
% 0.21/0.56  fof(f52,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f30])).
% 0.21/0.56  fof(f30,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.56    inference(ennf_transformation,[],[f24])).
% 0.21/0.56  fof(f24,axiom,(
% 0.21/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).
% 0.21/0.56  % (17829)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.56  fof(f156,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~r1_tarski(k4_subset_1(X1,X0,k2_tops_1(sK0,sK1)),sK1) | ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(X1)) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) ) | spl3_4),
% 0.21/0.56    inference(superposition,[],[f150,f87])).
% 0.21/0.56  fof(f87,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.56    inference(definition_unfolding,[],[f77,f59])).
% 0.21/0.56  fof(f59,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f14])).
% 0.21/0.56  fof(f14,axiom,(
% 0.21/0.56    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.21/0.56  fof(f77,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f44])).
% 0.21/0.56  fof(f44,plain,(
% 0.21/0.56    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.56    inference(flattening,[],[f43])).
% 0.21/0.56  fof(f43,plain,(
% 0.21/0.56    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.21/0.56    inference(ennf_transformation,[],[f17])).
% 0.21/0.56  fof(f17,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 0.21/0.56  fof(f150,plain,(
% 0.21/0.56    ( ! [X0] : (~r1_tarski(k3_tarski(k2_tarski(X0,k2_tops_1(sK0,sK1))),sK1)) ) | spl3_4),
% 0.21/0.56    inference(superposition,[],[f119,f57])).
% 0.21/0.56  fof(f57,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f13])).
% 0.21/0.56  fof(f13,axiom,(
% 0.21/0.56    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.21/0.56  fof(f119,plain,(
% 0.21/0.56    ( ! [X0] : (~r1_tarski(k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),X0)),sK1)) ) | spl3_4),
% 0.21/0.56    inference(resolution,[],[f118,f80])).
% 0.21/0.56  fof(f80,plain,(
% 0.21/0.56    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) )),
% 0.21/0.56    inference(definition_unfolding,[],[f54,f59])).
% 0.21/0.56  fof(f54,plain,(
% 0.21/0.56    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f12])).
% 0.21/0.56  fof(f12,axiom,(
% 0.21/0.56    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.21/0.56  fof(f118,plain,(
% 0.21/0.56    ( ! [X0] : (~r1_tarski(k2_tops_1(sK0,sK1),X0) | ~r1_tarski(X0,sK1)) ) | spl3_4),
% 0.21/0.56    inference(resolution,[],[f108,f76])).
% 0.21/0.56  fof(f76,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f42])).
% 0.21/0.56  fof(f42,plain,(
% 0.21/0.56    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.56    inference(flattening,[],[f41])).
% 0.21/0.56  fof(f41,plain,(
% 0.21/0.56    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.56    inference(ennf_transformation,[],[f5])).
% 0.21/0.56  fof(f5,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.21/0.56  fof(f108,plain,(
% 0.21/0.56    ~r1_tarski(k2_tops_1(sK0,sK1),sK1) | spl3_4),
% 0.21/0.56    inference(avatar_component_clause,[],[f106])).
% 0.21/0.56  fof(f237,plain,(
% 0.21/0.56    spl3_9),
% 0.21/0.56    inference(avatar_contradiction_clause,[],[f229])).
% 0.21/0.56  fof(f229,plain,(
% 0.21/0.56    $false | spl3_9),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f89,f88,f221,f76])).
% 0.21/0.56  fof(f221,plain,(
% 0.21/0.56    ~r1_tarski(sK1,sK1) | spl3_9),
% 0.21/0.56    inference(avatar_component_clause,[],[f219])).
% 0.21/0.56  fof(f219,plain,(
% 0.21/0.56    spl3_9 <=> r1_tarski(sK1,sK1)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.56  fof(f88,plain,(
% 0.21/0.56    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.56    inference(equality_resolution,[],[f66])).
% 0.21/0.56  fof(f66,plain,(
% 0.21/0.56    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.56    inference(cnf_transformation,[],[f2])).
% 0.21/0.56  fof(f2,axiom,(
% 0.21/0.56    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.56  fof(f89,plain,(
% 0.21/0.56    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.56    inference(equality_resolution,[],[f65])).
% 0.21/0.56  fof(f65,plain,(
% 0.21/0.56    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 0.21/0.56    inference(cnf_transformation,[],[f2])).
% 0.21/0.56  fof(f226,plain,(
% 0.21/0.56    ~spl3_2 | ~spl3_9 | spl3_10 | ~spl3_3 | ~spl3_8),
% 0.21/0.56    inference(avatar_split_clause,[],[f178,f146,f101,f223,f219,f96])).
% 0.21/0.56  fof(f96,plain,(
% 0.21/0.56    spl3_2 <=> v4_pre_topc(sK1,sK0)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.56  fof(f146,plain,(
% 0.21/0.56    spl3_8 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(k2_pre_topc(sK0,sK1),X0) | ~r1_tarski(sK1,X0) | ~v4_pre_topc(X0,sK0))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.56  fof(f178,plain,(
% 0.21/0.56    r1_tarski(k2_pre_topc(sK0,sK1),sK1) | ~r1_tarski(sK1,sK1) | ~v4_pre_topc(sK1,sK0) | (~spl3_3 | ~spl3_8)),
% 0.21/0.56    inference(resolution,[],[f147,f103])).
% 0.21/0.56  fof(f147,plain,(
% 0.21/0.56    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(k2_pre_topc(sK0,sK1),X0) | ~r1_tarski(sK1,X0) | ~v4_pre_topc(X0,sK0)) ) | ~spl3_8),
% 0.21/0.56    inference(avatar_component_clause,[],[f146])).
% 0.21/0.56  fof(f148,plain,(
% 0.21/0.56    ~spl3_1 | spl3_8 | ~spl3_3),
% 0.21/0.56    inference(avatar_split_clause,[],[f110,f101,f146,f91])).
% 0.21/0.56  fof(f110,plain,(
% 0.21/0.56    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v4_pre_topc(X0,sK0) | ~r1_tarski(sK1,X0) | r1_tarski(k2_pre_topc(sK0,sK1),X0)) ) | ~spl3_3),
% 0.21/0.56    inference(resolution,[],[f103,f53])).
% 0.21/0.56  fof(f53,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v4_pre_topc(X1,X0) | ~r1_tarski(X2,X1) | r1_tarski(k2_pre_topc(X0,X2),X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f32])).
% 0.21/0.56  fof(f32,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k2_pre_topc(X0,X2),X1) | ~r1_tarski(X2,X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.56    inference(flattening,[],[f31])).
% 0.21/0.56  fof(f31,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k2_pre_topc(X0,X2),X1) | (~r1_tarski(X2,X1) | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.56    inference(ennf_transformation,[],[f22])).
% 0.21/0.56  fof(f22,axiom,(
% 0.21/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X2,X1) & v4_pre_topc(X1,X0)) => r1_tarski(k2_pre_topc(X0,X2),X1)))))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_tops_1)).
% 0.21/0.56  fof(f109,plain,(
% 0.21/0.56    ~spl3_4),
% 0.21/0.56    inference(avatar_split_clause,[],[f47,f106])).
% 0.21/0.56  fof(f47,plain,(
% 0.21/0.56    ~r1_tarski(k2_tops_1(sK0,sK1),sK1)),
% 0.21/0.56    inference(cnf_transformation,[],[f28])).
% 0.21/0.56  fof(f28,plain,(
% 0.21/0.56    ? [X0] : (? [X1] : (~r1_tarski(k2_tops_1(X0,X1),X1) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.21/0.56    inference(flattening,[],[f27])).
% 0.21/0.56  fof(f27,plain,(
% 0.21/0.56    ? [X0] : (? [X1] : ((~r1_tarski(k2_tops_1(X0,X1),X1) & v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.21/0.56    inference(ennf_transformation,[],[f26])).
% 0.21/0.56  fof(f26,negated_conjecture,(
% 0.21/0.56    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => r1_tarski(k2_tops_1(X0,X1),X1))))),
% 0.21/0.56    inference(negated_conjecture,[],[f25])).
% 0.21/0.56  fof(f25,conjecture,(
% 0.21/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => r1_tarski(k2_tops_1(X0,X1),X1))))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_tops_1)).
% 0.21/0.56  fof(f104,plain,(
% 0.21/0.56    spl3_3),
% 0.21/0.56    inference(avatar_split_clause,[],[f45,f101])).
% 0.21/0.56  fof(f45,plain,(
% 0.21/0.56    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.56    inference(cnf_transformation,[],[f28])).
% 0.21/0.56  fof(f99,plain,(
% 0.21/0.56    spl3_2),
% 0.21/0.56    inference(avatar_split_clause,[],[f46,f96])).
% 0.21/0.56  fof(f46,plain,(
% 0.21/0.56    v4_pre_topc(sK1,sK0)),
% 0.21/0.56    inference(cnf_transformation,[],[f28])).
% 0.21/0.56  fof(f94,plain,(
% 0.21/0.56    spl3_1),
% 0.21/0.56    inference(avatar_split_clause,[],[f48,f91])).
% 0.21/0.56  fof(f48,plain,(
% 0.21/0.56    l1_pre_topc(sK0)),
% 0.21/0.56    inference(cnf_transformation,[],[f28])).
% 0.21/0.56  % SZS output end Proof for theBenchmark
% 0.21/0.56  % (17836)------------------------------
% 0.21/0.56  % (17836)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (17836)Termination reason: Refutation
% 0.21/0.56  
% 0.21/0.56  % (17836)Memory used [KB]: 11385
% 0.21/0.56  % (17836)Time elapsed: 0.082 s
% 0.21/0.56  % (17836)------------------------------
% 0.21/0.56  % (17836)------------------------------
% 0.21/0.57  % (17808)Success in time 0.204 s
%------------------------------------------------------------------------------
