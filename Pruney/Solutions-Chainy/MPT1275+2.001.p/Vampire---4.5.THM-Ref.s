%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:12:42 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 200 expanded)
%              Number of leaves         :   25 (  70 expanded)
%              Depth                    :    9
%              Number of atoms          :  273 ( 577 expanded)
%              Number of equality atoms :   52 ( 121 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f232,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f64,f65,f101,f103,f105,f116,f120,f121,f128,f131,f176,f180,f202,f222])).

fof(f222,plain,
    ( spl2_2
    | ~ spl2_8
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f210,f192,f123,f61])).

fof(f61,plain,
    ( spl2_2
  <=> sK1 = k2_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

% (10021)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
fof(f123,plain,
    ( spl2_8
  <=> r1_tarski(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f192,plain,
    ( spl2_12
  <=> k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(sK1,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f210,plain,
    ( ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | sK1 = k2_tops_1(sK0,sK1)
    | ~ spl2_12 ),
    inference(superposition,[],[f143,f194])).

fof(f194,plain,
    ( k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(sK1,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))))
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f192])).

fof(f143,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_setfam_1(k2_tarski(X0,X1)))
      | k1_setfam_1(k2_tarski(X0,X1)) = X0 ) ),
    inference(resolution,[],[f142,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f142,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
    inference(superposition,[],[f51,f52])).

fof(f52,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))))) ),
    inference(definition_unfolding,[],[f44,f42,f50,f50])).

fof(f50,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f43,f42])).

fof(f43,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f42,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f44,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f51,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0) ),
    inference(definition_unfolding,[],[f40,f50])).

fof(f40,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f202,plain,
    ( ~ spl2_10
    | spl2_12
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f201,f173,f192,f169])).

fof(f169,plain,
    ( spl2_10
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f173,plain,
    ( spl2_11
  <=> k2_tops_1(sK0,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f201,plain,
    ( k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(sK1,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_11 ),
    inference(forward_demodulation,[],[f188,f41])).

fof(f41,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f188,plain,
    ( k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_11 ),
    inference(superposition,[],[f78,f175])).

fof(f175,plain,
    ( k2_tops_1(sK0,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f173])).

fof(f78,plain,(
    ! [X4,X5,X3] :
      ( k9_subset_1(X3,X5,X4) = k1_setfam_1(k2_tarski(X4,X5))
      | ~ m1_subset_1(X5,k1_zfmisc_1(X3)) ) ),
    inference(duplicate_literal_removal,[],[f77])).

fof(f77,plain,(
    ! [X4,X5,X3] :
      ( k9_subset_1(X3,X5,X4) = k1_setfam_1(k2_tarski(X4,X5))
      | ~ m1_subset_1(X5,k1_zfmisc_1(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(X3)) ) ),
    inference(superposition,[],[f49,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f48,f42])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f26])).

% (10011)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

fof(f180,plain,(
    spl2_10 ),
    inference(avatar_contradiction_clause,[],[f179])).

fof(f179,plain,
    ( $false
    | spl2_10 ),
    inference(subsumption_resolution,[],[f30,f171])).

fof(f171,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_10 ),
    inference(avatar_component_clause,[],[f169])).

fof(f30,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tops_1(X1,X0)
          <~> k2_tops_1(X0,X1) = X1 )
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tops_1(X1,X0)
          <~> k2_tops_1(X0,X1) = X1 )
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
             => ( v3_tops_1(X1,X0)
              <=> k2_tops_1(X0,X1) = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => ( v3_tops_1(X1,X0)
            <=> k2_tops_1(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_tops_1)).

fof(f176,plain,
    ( ~ spl2_5
    | ~ spl2_10
    | spl2_11
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f163,f90,f173,f169,f98])).

fof(f98,plain,
    ( spl2_5
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f90,plain,
    ( spl2_3
  <=> sK1 = k2_pre_topc(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f163,plain,
    ( k2_tops_1(sK0,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_3 ),
    inference(superposition,[],[f33,f92])).

fof(f92,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f90])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_1)).

fof(f131,plain,
    ( spl2_1
    | ~ spl2_6 ),
    inference(avatar_contradiction_clause,[],[f129])).

fof(f129,plain,
    ( $false
    | spl2_1
    | ~ spl2_6 ),
    inference(unit_resulting_resolution,[],[f32,f59,f31,f111,f30,f37])).

% (10000)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f37,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_tops_1(X1,X0)
      | ~ v4_pre_topc(X1,X0)
      | v3_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f24])).

% (10001)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tops_1(X1,X0)
          | ~ v4_pre_topc(X1,X0)
          | ~ v2_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tops_1(X1,X0)
          | ~ v4_pre_topc(X1,X0)
          | ~ v2_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v4_pre_topc(X1,X0)
              & v2_tops_1(X1,X0) )
           => v3_tops_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_tops_1)).

fof(f111,plain,
    ( v2_tops_1(sK1,sK0)
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl2_6
  <=> v2_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f31,plain,(
    v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f59,plain,
    ( ~ v3_tops_1(sK1,sK0)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl2_1
  <=> v3_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f32,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f128,plain,
    ( ~ spl2_6
    | spl2_8
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f127,f98,f123,f109])).

fof(f127,plain,
    ( ~ l1_pre_topc(sK0)
    | r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | ~ v2_tops_1(sK1,sK0) ),
    inference(resolution,[],[f39,f30])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | r1_tarski(X1,k2_tops_1(X0,X1))
      | ~ v2_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> r1_tarski(X1,k2_tops_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> r1_tarski(X1,k2_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_tops_1)).

fof(f121,plain,
    ( spl2_6
    | ~ spl2_1
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f73,f98,f57,f109])).

fof(f73,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v3_tops_1(sK1,sK0)
    | v2_tops_1(sK1,sK0) ),
    inference(resolution,[],[f36,f30])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v3_tops_1(X1,X0)
      | v2_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tops_1(X1,X0)
          | ~ v3_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tops_1(X1,X0)
          | ~ v3_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tops_1(X1,X0)
           => v2_tops_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_tops_1)).

fof(f120,plain,(
    spl2_7 ),
    inference(avatar_contradiction_clause,[],[f117])).

fof(f117,plain,
    ( $false
    | spl2_7 ),
    inference(unit_resulting_resolution,[],[f54,f115])).

fof(f115,plain,
    ( ~ r1_tarski(sK1,sK1)
    | spl2_7 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl2_7
  <=> r1_tarski(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f54,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f116,plain,
    ( spl2_6
    | ~ spl2_5
    | ~ spl2_7
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f107,f61,f113,f98,f109])).

fof(f107,plain,
    ( ~ r1_tarski(sK1,sK1)
    | ~ l1_pre_topc(sK0)
    | v2_tops_1(sK1,sK0)
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f106,f62])).

fof(f62,plain,
    ( sK1 = k2_tops_1(sK0,sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f61])).

fof(f106,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | v2_tops_1(sK1,sK0) ),
    inference(resolution,[],[f38,f30])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ r1_tarski(X1,k2_tops_1(X0,X1))
      | v2_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f105,plain,(
    spl2_5 ),
    inference(avatar_contradiction_clause,[],[f104])).

fof(f104,plain,
    ( $false
    | spl2_5 ),
    inference(subsumption_resolution,[],[f32,f100])).

fof(f100,plain,
    ( ~ l1_pre_topc(sK0)
    | spl2_5 ),
    inference(avatar_component_clause,[],[f98])).

fof(f103,plain,(
    spl2_4 ),
    inference(avatar_contradiction_clause,[],[f102])).

fof(f102,plain,
    ( $false
    | spl2_4 ),
    inference(subsumption_resolution,[],[f31,f96])).

fof(f96,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | spl2_4 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl2_4
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f101,plain,
    ( spl2_3
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f88,f98,f94,f90])).

fof(f88,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v4_pre_topc(sK1,sK0)
    | sK1 = k2_pre_topc(sK0,sK1) ),
    inference(resolution,[],[f35,f30])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

fof(f65,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f28,f61,f57])).

fof(f28,plain,
    ( sK1 = k2_tops_1(sK0,sK1)
    | v3_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f64,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f29,f61,f57])).

fof(f29,plain,
    ( sK1 != k2_tops_1(sK0,sK1)
    | ~ v3_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n002.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 20:26:22 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.23/0.52  % (9999)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.23/0.53  % (10015)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.23/0.53  % (10007)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.23/0.53  % (9996)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.23/0.54  % (10017)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.23/0.54  % (9995)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.23/0.54  % (9995)Refutation not found, incomplete strategy% (9995)------------------------------
% 0.23/0.54  % (9995)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.54  % (9995)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.54  
% 0.23/0.54  % (9995)Memory used [KB]: 1663
% 0.23/0.54  % (9995)Time elapsed: 0.111 s
% 0.23/0.54  % (9995)------------------------------
% 0.23/0.54  % (9995)------------------------------
% 0.23/0.54  % (10019)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.23/0.54  % (10003)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.23/0.54  % (10009)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.23/0.55  % (10007)Refutation found. Thanks to Tanya!
% 0.23/0.55  % SZS status Theorem for theBenchmark
% 0.23/0.55  % (9998)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.23/0.55  % (9994)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.23/0.55  % SZS output start Proof for theBenchmark
% 0.23/0.55  fof(f232,plain,(
% 0.23/0.55    $false),
% 0.23/0.55    inference(avatar_sat_refutation,[],[f64,f65,f101,f103,f105,f116,f120,f121,f128,f131,f176,f180,f202,f222])).
% 0.23/0.55  fof(f222,plain,(
% 0.23/0.55    spl2_2 | ~spl2_8 | ~spl2_12),
% 0.23/0.55    inference(avatar_split_clause,[],[f210,f192,f123,f61])).
% 0.23/0.55  fof(f61,plain,(
% 0.23/0.55    spl2_2 <=> sK1 = k2_tops_1(sK0,sK1)),
% 0.23/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.23/0.55  % (10021)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.23/0.55  fof(f123,plain,(
% 0.23/0.55    spl2_8 <=> r1_tarski(sK1,k2_tops_1(sK0,sK1))),
% 0.23/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.23/0.55  fof(f192,plain,(
% 0.23/0.55    spl2_12 <=> k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(sK1,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))))),
% 0.23/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.23/0.55  fof(f210,plain,(
% 0.23/0.55    ~r1_tarski(sK1,k2_tops_1(sK0,sK1)) | sK1 = k2_tops_1(sK0,sK1) | ~spl2_12),
% 0.23/0.55    inference(superposition,[],[f143,f194])).
% 0.23/0.55  fof(f194,plain,(
% 0.23/0.55    k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(sK1,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))) | ~spl2_12),
% 0.23/0.55    inference(avatar_component_clause,[],[f192])).
% 0.23/0.55  fof(f143,plain,(
% 0.23/0.55    ( ! [X0,X1] : (~r1_tarski(X0,k1_setfam_1(k2_tarski(X0,X1))) | k1_setfam_1(k2_tarski(X0,X1)) = X0) )),
% 0.23/0.55    inference(resolution,[],[f142,f47])).
% 0.23/0.55  fof(f47,plain,(
% 0.23/0.55    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.23/0.55    inference(cnf_transformation,[],[f1])).
% 0.23/0.55  fof(f1,axiom,(
% 0.23/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.23/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.23/0.55  fof(f142,plain,(
% 0.23/0.55    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0)) )),
% 0.23/0.55    inference(superposition,[],[f51,f52])).
% 0.23/0.55  fof(f52,plain,(
% 0.23/0.55    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))))))) )),
% 0.23/0.55    inference(definition_unfolding,[],[f44,f42,f50,f50])).
% 0.23/0.55  fof(f50,plain,(
% 0.23/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 0.23/0.55    inference(definition_unfolding,[],[f43,f42])).
% 0.23/0.55  fof(f43,plain,(
% 0.23/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.23/0.55    inference(cnf_transformation,[],[f2])).
% 0.23/0.55  fof(f2,axiom,(
% 0.23/0.55    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.23/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.23/0.55  fof(f42,plain,(
% 0.23/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.23/0.55    inference(cnf_transformation,[],[f8])).
% 0.23/0.55  fof(f8,axiom,(
% 0.23/0.55    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.23/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.23/0.55  fof(f44,plain,(
% 0.23/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.23/0.55    inference(cnf_transformation,[],[f4])).
% 0.23/0.55  fof(f4,axiom,(
% 0.23/0.55    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.23/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.23/0.55  fof(f51,plain,(
% 0.23/0.55    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0)) )),
% 0.23/0.55    inference(definition_unfolding,[],[f40,f50])).
% 0.23/0.55  fof(f40,plain,(
% 0.23/0.55    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.23/0.55    inference(cnf_transformation,[],[f3])).
% 0.23/0.55  fof(f3,axiom,(
% 0.23/0.55    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.23/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.23/0.55  fof(f202,plain,(
% 0.23/0.55    ~spl2_10 | spl2_12 | ~spl2_11),
% 0.23/0.55    inference(avatar_split_clause,[],[f201,f173,f192,f169])).
% 0.23/0.55  fof(f169,plain,(
% 0.23/0.55    spl2_10 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.23/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.23/0.55  fof(f173,plain,(
% 0.23/0.55    spl2_11 <=> k2_tops_1(sK0,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))),
% 0.23/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.23/0.55  fof(f201,plain,(
% 0.23/0.55    k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(sK1,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_11),
% 0.23/0.55    inference(forward_demodulation,[],[f188,f41])).
% 0.23/0.55  fof(f41,plain,(
% 0.23/0.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.23/0.55    inference(cnf_transformation,[],[f5])).
% 0.23/0.55  fof(f5,axiom,(
% 0.23/0.55    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.23/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.23/0.55  fof(f188,plain,(
% 0.23/0.55    k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_11),
% 0.23/0.55    inference(superposition,[],[f78,f175])).
% 0.23/0.55  fof(f175,plain,(
% 0.23/0.55    k2_tops_1(sK0,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) | ~spl2_11),
% 0.23/0.55    inference(avatar_component_clause,[],[f173])).
% 0.23/0.55  fof(f78,plain,(
% 0.23/0.55    ( ! [X4,X5,X3] : (k9_subset_1(X3,X5,X4) = k1_setfam_1(k2_tarski(X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(X3))) )),
% 0.23/0.55    inference(duplicate_literal_removal,[],[f77])).
% 0.23/0.55  fof(f77,plain,(
% 0.23/0.55    ( ! [X4,X5,X3] : (k9_subset_1(X3,X5,X4) = k1_setfam_1(k2_tarski(X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(X3))) )),
% 0.23/0.55    inference(superposition,[],[f49,f53])).
% 0.23/0.55  fof(f53,plain,(
% 0.23/0.55    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.23/0.55    inference(definition_unfolding,[],[f48,f42])).
% 0.23/0.55  fof(f48,plain,(
% 0.23/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)) )),
% 0.23/0.55    inference(cnf_transformation,[],[f26])).
% 0.23/0.55  % (10011)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.23/0.55  fof(f26,plain,(
% 0.23/0.55    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.23/0.55    inference(ennf_transformation,[],[f7])).
% 0.23/0.55  fof(f7,axiom,(
% 0.23/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.23/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.23/0.55  fof(f49,plain,(
% 0.23/0.55    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.23/0.55    inference(cnf_transformation,[],[f27])).
% 0.23/0.55  fof(f27,plain,(
% 0.23/0.55    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.23/0.55    inference(ennf_transformation,[],[f6])).
% 0.23/0.55  fof(f6,axiom,(
% 0.23/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1))),
% 0.23/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).
% 0.23/0.55  fof(f180,plain,(
% 0.23/0.55    spl2_10),
% 0.23/0.55    inference(avatar_contradiction_clause,[],[f179])).
% 0.23/0.55  fof(f179,plain,(
% 0.23/0.55    $false | spl2_10),
% 0.23/0.55    inference(subsumption_resolution,[],[f30,f171])).
% 0.23/0.55  fof(f171,plain,(
% 0.23/0.55    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl2_10),
% 0.23/0.55    inference(avatar_component_clause,[],[f169])).
% 0.23/0.55  fof(f30,plain,(
% 0.23/0.55    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.23/0.55    inference(cnf_transformation,[],[f17])).
% 0.23/0.55  fof(f17,plain,(
% 0.23/0.55    ? [X0] : (? [X1] : ((v3_tops_1(X1,X0) <~> k2_tops_1(X0,X1) = X1) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.23/0.55    inference(flattening,[],[f16])).
% 0.23/0.55  fof(f16,plain,(
% 0.23/0.55    ? [X0] : (? [X1] : (((v3_tops_1(X1,X0) <~> k2_tops_1(X0,X1) = X1) & v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.23/0.55    inference(ennf_transformation,[],[f15])).
% 0.23/0.55  fof(f15,negated_conjecture,(
% 0.23/0.55    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => (v3_tops_1(X1,X0) <=> k2_tops_1(X0,X1) = X1))))),
% 0.23/0.55    inference(negated_conjecture,[],[f14])).
% 0.23/0.55  fof(f14,conjecture,(
% 0.23/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => (v3_tops_1(X1,X0) <=> k2_tops_1(X0,X1) = X1))))),
% 0.23/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_tops_1)).
% 0.23/0.55  fof(f176,plain,(
% 0.23/0.55    ~spl2_5 | ~spl2_10 | spl2_11 | ~spl2_3),
% 0.23/0.55    inference(avatar_split_clause,[],[f163,f90,f173,f169,f98])).
% 0.23/0.55  fof(f98,plain,(
% 0.23/0.55    spl2_5 <=> l1_pre_topc(sK0)),
% 0.23/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.23/0.55  fof(f90,plain,(
% 0.23/0.55    spl2_3 <=> sK1 = k2_pre_topc(sK0,sK1)),
% 0.23/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.23/0.55  fof(f163,plain,(
% 0.23/0.55    k2_tops_1(sK0,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl2_3),
% 0.23/0.55    inference(superposition,[],[f33,f92])).
% 0.23/0.55  fof(f92,plain,(
% 0.23/0.55    sK1 = k2_pre_topc(sK0,sK1) | ~spl2_3),
% 0.23/0.55    inference(avatar_component_clause,[],[f90])).
% 0.23/0.55  fof(f33,plain,(
% 0.23/0.55    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.23/0.55    inference(cnf_transformation,[],[f18])).
% 0.23/0.55  fof(f18,plain,(
% 0.23/0.55    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.23/0.55    inference(ennf_transformation,[],[f10])).
% 0.23/0.55  fof(f10,axiom,(
% 0.23/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))))),
% 0.23/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_1)).
% 0.23/0.55  fof(f131,plain,(
% 0.23/0.55    spl2_1 | ~spl2_6),
% 0.23/0.55    inference(avatar_contradiction_clause,[],[f129])).
% 0.23/0.55  fof(f129,plain,(
% 0.23/0.55    $false | (spl2_1 | ~spl2_6)),
% 0.23/0.55    inference(unit_resulting_resolution,[],[f32,f59,f31,f111,f30,f37])).
% 0.23/0.55  % (10000)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.23/0.55  fof(f37,plain,(
% 0.23/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_tops_1(X1,X0) | ~v4_pre_topc(X1,X0) | v3_tops_1(X1,X0)) )),
% 0.23/0.55    inference(cnf_transformation,[],[f24])).
% 0.23/0.55  % (10001)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.23/0.55  fof(f24,plain,(
% 0.23/0.55    ! [X0] : (! [X1] : (v3_tops_1(X1,X0) | ~v4_pre_topc(X1,X0) | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.23/0.55    inference(flattening,[],[f23])).
% 0.23/0.55  fof(f23,plain,(
% 0.23/0.55    ! [X0] : (! [X1] : ((v3_tops_1(X1,X0) | (~v4_pre_topc(X1,X0) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.23/0.55    inference(ennf_transformation,[],[f13])).
% 0.23/0.55  fof(f13,axiom,(
% 0.23/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X1,X0) & v2_tops_1(X1,X0)) => v3_tops_1(X1,X0))))),
% 0.23/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_tops_1)).
% 0.23/0.55  fof(f111,plain,(
% 0.23/0.55    v2_tops_1(sK1,sK0) | ~spl2_6),
% 0.23/0.55    inference(avatar_component_clause,[],[f109])).
% 0.23/0.55  fof(f109,plain,(
% 0.23/0.55    spl2_6 <=> v2_tops_1(sK1,sK0)),
% 0.23/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.23/0.55  fof(f31,plain,(
% 0.23/0.55    v4_pre_topc(sK1,sK0)),
% 0.23/0.55    inference(cnf_transformation,[],[f17])).
% 0.23/0.55  fof(f59,plain,(
% 0.23/0.55    ~v3_tops_1(sK1,sK0) | spl2_1),
% 0.23/0.55    inference(avatar_component_clause,[],[f57])).
% 0.23/0.55  fof(f57,plain,(
% 0.23/0.55    spl2_1 <=> v3_tops_1(sK1,sK0)),
% 0.23/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.23/0.55  fof(f32,plain,(
% 0.23/0.55    l1_pre_topc(sK0)),
% 0.23/0.55    inference(cnf_transformation,[],[f17])).
% 0.23/0.55  fof(f128,plain,(
% 0.23/0.55    ~spl2_6 | spl2_8 | ~spl2_5),
% 0.23/0.55    inference(avatar_split_clause,[],[f127,f98,f123,f109])).
% 0.23/0.55  fof(f127,plain,(
% 0.23/0.55    ~l1_pre_topc(sK0) | r1_tarski(sK1,k2_tops_1(sK0,sK1)) | ~v2_tops_1(sK1,sK0)),
% 0.23/0.55    inference(resolution,[],[f39,f30])).
% 0.23/0.55  fof(f39,plain,(
% 0.23/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | r1_tarski(X1,k2_tops_1(X0,X1)) | ~v2_tops_1(X1,X0)) )),
% 0.23/0.55    inference(cnf_transformation,[],[f25])).
% 0.23/0.55  fof(f25,plain,(
% 0.23/0.55    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> r1_tarski(X1,k2_tops_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.23/0.55    inference(ennf_transformation,[],[f11])).
% 0.23/0.55  fof(f11,axiom,(
% 0.23/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> r1_tarski(X1,k2_tops_1(X0,X1)))))),
% 0.23/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_tops_1)).
% 0.23/0.55  fof(f121,plain,(
% 0.23/0.55    spl2_6 | ~spl2_1 | ~spl2_5),
% 0.23/0.55    inference(avatar_split_clause,[],[f73,f98,f57,f109])).
% 0.23/0.55  fof(f73,plain,(
% 0.23/0.55    ~l1_pre_topc(sK0) | ~v3_tops_1(sK1,sK0) | v2_tops_1(sK1,sK0)),
% 0.23/0.55    inference(resolution,[],[f36,f30])).
% 0.23/0.55  fof(f36,plain,(
% 0.23/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v3_tops_1(X1,X0) | v2_tops_1(X1,X0)) )),
% 0.23/0.55    inference(cnf_transformation,[],[f22])).
% 0.23/0.55  fof(f22,plain,(
% 0.23/0.55    ! [X0] : (! [X1] : (v2_tops_1(X1,X0) | ~v3_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.23/0.55    inference(flattening,[],[f21])).
% 0.23/0.55  fof(f21,plain,(
% 0.23/0.55    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) | ~v3_tops_1(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.23/0.55    inference(ennf_transformation,[],[f12])).
% 0.23/0.55  fof(f12,axiom,(
% 0.23/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tops_1(X1,X0) => v2_tops_1(X1,X0))))),
% 0.23/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_tops_1)).
% 0.23/0.55  fof(f120,plain,(
% 0.23/0.55    spl2_7),
% 0.23/0.55    inference(avatar_contradiction_clause,[],[f117])).
% 0.23/0.55  fof(f117,plain,(
% 0.23/0.55    $false | spl2_7),
% 0.23/0.55    inference(unit_resulting_resolution,[],[f54,f115])).
% 0.23/0.55  fof(f115,plain,(
% 0.23/0.55    ~r1_tarski(sK1,sK1) | spl2_7),
% 0.23/0.55    inference(avatar_component_clause,[],[f113])).
% 0.23/0.55  fof(f113,plain,(
% 0.23/0.55    spl2_7 <=> r1_tarski(sK1,sK1)),
% 0.23/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.23/0.55  fof(f54,plain,(
% 0.23/0.55    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.23/0.55    inference(equality_resolution,[],[f46])).
% 0.23/0.55  fof(f46,plain,(
% 0.23/0.55    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.23/0.55    inference(cnf_transformation,[],[f1])).
% 0.23/0.55  fof(f116,plain,(
% 0.23/0.55    spl2_6 | ~spl2_5 | ~spl2_7 | ~spl2_2),
% 0.23/0.55    inference(avatar_split_clause,[],[f107,f61,f113,f98,f109])).
% 0.23/0.55  fof(f107,plain,(
% 0.23/0.55    ~r1_tarski(sK1,sK1) | ~l1_pre_topc(sK0) | v2_tops_1(sK1,sK0) | ~spl2_2),
% 0.23/0.55    inference(forward_demodulation,[],[f106,f62])).
% 0.23/0.55  fof(f62,plain,(
% 0.23/0.55    sK1 = k2_tops_1(sK0,sK1) | ~spl2_2),
% 0.23/0.55    inference(avatar_component_clause,[],[f61])).
% 0.23/0.55  fof(f106,plain,(
% 0.23/0.55    ~l1_pre_topc(sK0) | ~r1_tarski(sK1,k2_tops_1(sK0,sK1)) | v2_tops_1(sK1,sK0)),
% 0.23/0.55    inference(resolution,[],[f38,f30])).
% 0.23/0.55  fof(f38,plain,(
% 0.23/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~r1_tarski(X1,k2_tops_1(X0,X1)) | v2_tops_1(X1,X0)) )),
% 0.23/0.55    inference(cnf_transformation,[],[f25])).
% 0.23/0.55  fof(f105,plain,(
% 0.23/0.55    spl2_5),
% 0.23/0.55    inference(avatar_contradiction_clause,[],[f104])).
% 0.23/0.55  fof(f104,plain,(
% 0.23/0.55    $false | spl2_5),
% 0.23/0.55    inference(subsumption_resolution,[],[f32,f100])).
% 0.23/0.55  fof(f100,plain,(
% 0.23/0.55    ~l1_pre_topc(sK0) | spl2_5),
% 0.23/0.55    inference(avatar_component_clause,[],[f98])).
% 0.23/0.55  fof(f103,plain,(
% 0.23/0.55    spl2_4),
% 0.23/0.55    inference(avatar_contradiction_clause,[],[f102])).
% 0.23/0.55  fof(f102,plain,(
% 0.23/0.55    $false | spl2_4),
% 0.23/0.55    inference(subsumption_resolution,[],[f31,f96])).
% 0.23/0.55  fof(f96,plain,(
% 0.23/0.55    ~v4_pre_topc(sK1,sK0) | spl2_4),
% 0.23/0.55    inference(avatar_component_clause,[],[f94])).
% 0.23/0.55  fof(f94,plain,(
% 0.23/0.55    spl2_4 <=> v4_pre_topc(sK1,sK0)),
% 0.23/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.23/0.55  fof(f101,plain,(
% 0.23/0.55    spl2_3 | ~spl2_4 | ~spl2_5),
% 0.23/0.55    inference(avatar_split_clause,[],[f88,f98,f94,f90])).
% 0.23/0.55  fof(f88,plain,(
% 0.23/0.55    ~l1_pre_topc(sK0) | ~v4_pre_topc(sK1,sK0) | sK1 = k2_pre_topc(sK0,sK1)),
% 0.23/0.55    inference(resolution,[],[f35,f30])).
% 0.23/0.55  fof(f35,plain,(
% 0.23/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) = X1) )),
% 0.23/0.55    inference(cnf_transformation,[],[f20])).
% 0.23/0.55  fof(f20,plain,(
% 0.23/0.55    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.23/0.55    inference(flattening,[],[f19])).
% 0.23/0.55  fof(f19,plain,(
% 0.23/0.55    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.23/0.55    inference(ennf_transformation,[],[f9])).
% 0.23/0.55  fof(f9,axiom,(
% 0.23/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 0.23/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).
% 0.23/0.55  fof(f65,plain,(
% 0.23/0.55    spl2_1 | spl2_2),
% 0.23/0.55    inference(avatar_split_clause,[],[f28,f61,f57])).
% 0.23/0.55  fof(f28,plain,(
% 0.23/0.55    sK1 = k2_tops_1(sK0,sK1) | v3_tops_1(sK1,sK0)),
% 0.23/0.55    inference(cnf_transformation,[],[f17])).
% 0.23/0.55  fof(f64,plain,(
% 0.23/0.55    ~spl2_1 | ~spl2_2),
% 0.23/0.55    inference(avatar_split_clause,[],[f29,f61,f57])).
% 0.23/0.55  fof(f29,plain,(
% 0.23/0.55    sK1 != k2_tops_1(sK0,sK1) | ~v3_tops_1(sK1,sK0)),
% 0.23/0.55    inference(cnf_transformation,[],[f17])).
% 0.23/0.55  % SZS output end Proof for theBenchmark
% 0.23/0.55  % (10007)------------------------------
% 0.23/0.55  % (10007)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.55  % (10007)Termination reason: Refutation
% 0.23/0.55  
% 0.23/0.55  % (10007)Memory used [KB]: 6396
% 0.23/0.55  % (10007)Time elapsed: 0.123 s
% 0.23/0.55  % (10007)------------------------------
% 0.23/0.55  % (10007)------------------------------
% 0.23/0.55  % (10011)Refutation not found, incomplete strategy% (10011)------------------------------
% 0.23/0.55  % (10011)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.55  % (10011)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.55  
% 0.23/0.55  % (10011)Memory used [KB]: 10618
% 0.23/0.55  % (10011)Time elapsed: 0.128 s
% 0.23/0.55  % (10011)------------------------------
% 0.23/0.55  % (10011)------------------------------
% 0.23/0.55  % (9997)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.23/0.55  % (9992)Success in time 0.181 s
%------------------------------------------------------------------------------
