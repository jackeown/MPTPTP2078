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
% DateTime   : Thu Dec  3 13:13:47 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 152 expanded)
%              Number of leaves         :   27 (  58 expanded)
%              Depth                    :   10
%              Number of atoms          :  276 ( 505 expanded)
%              Number of equality atoms :   37 (  67 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f226,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f46,f51,f56,f61,f66,f83,f93,f109,f119,f132,f156,f173,f208,f209,f210,f225])).

fof(f225,plain,
    ( ~ spl5_1
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_21 ),
    inference(avatar_contradiction_clause,[],[f224])).

fof(f224,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_21 ),
    inference(subsumption_resolution,[],[f223,f45])).

fof(f45,plain,
    ( l1_pre_topc(sK0)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f43])).

% (1350)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
fof(f43,plain,
    ( spl5_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f223,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_21 ),
    inference(subsumption_resolution,[],[f222,f82])).

fof(f82,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl5_7
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f222,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_21 ),
    inference(subsumption_resolution,[],[f221,f60])).

fof(f60,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl5_4
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f221,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl5_5
    | ~ spl5_21 ),
    inference(resolution,[],[f199,f65])).

fof(f65,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl5_5
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f199,plain,
    ( ! [X0] :
        ( ~ v4_pre_topc(sK1,X0)
        | ~ m1_pre_topc(sK2,X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl5_21 ),
    inference(avatar_component_clause,[],[f198])).

fof(f198,plain,
    ( spl5_21
  <=> ! [X0] :
        ( ~ m1_pre_topc(sK2,X0)
        | ~ v4_pre_topc(sK1,X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f210,plain,
    ( u1_struct_0(sK2) != k2_struct_0(sK2)
    | sK1 != k3_xboole_0(sK1,u1_struct_0(sK2))
    | sK1 != sK3
    | v4_pre_topc(sK3,sK2)
    | ~ v4_pre_topc(k3_xboole_0(sK1,k2_struct_0(sK2)),sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f209,plain,
    ( sK1 != k3_xboole_0(sK1,u1_struct_0(sK2))
    | u1_struct_0(sK2) != k2_struct_0(sK2)
    | m1_subset_1(k3_xboole_0(sK1,k2_struct_0(sK2)),k1_zfmisc_1(k2_struct_0(sK2)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK2))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f208,plain,
    ( spl5_21
    | spl5_22
    | ~ spl5_23
    | ~ spl5_9
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f193,f170,f90,f205,f201,f198])).

fof(f201,plain,
    ( spl5_22
  <=> v4_pre_topc(k3_xboole_0(sK1,k2_struct_0(sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f205,plain,
    ( spl5_23
  <=> m1_subset_1(k3_xboole_0(sK1,k2_struct_0(sK2)),k1_zfmisc_1(k2_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f90,plain,
    ( spl5_9
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f170,plain,
    ( spl5_18
  <=> u1_struct_0(sK2) = k2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f193,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k3_xboole_0(sK1,k2_struct_0(sK2)),k1_zfmisc_1(k2_struct_0(sK2)))
        | v4_pre_topc(k3_xboole_0(sK1,k2_struct_0(sK2)),sK2)
        | ~ m1_pre_topc(sK2,X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v4_pre_topc(sK1,X0) )
    | ~ spl5_9
    | ~ spl5_18 ),
    inference(forward_demodulation,[],[f137,f172])).

fof(f172,plain,
    ( u1_struct_0(sK2) = k2_struct_0(sK2)
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f170])).

fof(f137,plain,
    ( ! [X0] :
        ( v4_pre_topc(k3_xboole_0(sK1,k2_struct_0(sK2)),sK2)
        | ~ m1_subset_1(k3_xboole_0(sK1,k2_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ m1_pre_topc(sK2,X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v4_pre_topc(sK1,X0) )
    | ~ spl5_9 ),
    inference(forward_demodulation,[],[f136,f35])).

fof(f35,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f136,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k3_xboole_0(sK1,k2_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ m1_pre_topc(sK2,X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v4_pre_topc(sK1,X0)
        | v4_pre_topc(k3_xboole_0(k2_struct_0(sK2),sK1),sK2) )
    | ~ spl5_9 ),
    inference(forward_demodulation,[],[f135,f35])).

fof(f135,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k3_xboole_0(k2_struct_0(sK2),sK1),k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ m1_pre_topc(sK2,X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v4_pre_topc(sK1,X0)
        | v4_pre_topc(k3_xboole_0(k2_struct_0(sK2),sK1),sK2) )
    | ~ spl5_9 ),
    inference(superposition,[],[f41,f133])).

fof(f133,plain,
    ( ! [X0] : k9_subset_1(u1_struct_0(sK2),sK1,X0) = k3_xboole_0(X0,sK1)
    | ~ spl5_9 ),
    inference(forward_demodulation,[],[f97,f98])).

fof(f98,plain,
    ( ! [X1] : k3_xboole_0(X1,sK1) = k9_subset_1(u1_struct_0(sK2),X1,sK1)
    | ~ spl5_9 ),
    inference(resolution,[],[f92,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f92,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f90])).

fof(f97,plain,
    ( ! [X0] : k9_subset_1(u1_struct_0(sK2),X0,sK1) = k9_subset_1(u1_struct_0(sK2),sK1,X0)
    | ~ spl5_9 ),
    inference(resolution,[],[f92,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

fof(f41,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X3,X0)
      | v4_pre_topc(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),X1) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X3,X0)
      | k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
      | v4_pre_topc(X2,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v4_pre_topc(X2,X1)
              <=> ? [X3] :
                    ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                    & v4_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => ( v4_pre_topc(X2,X1)
              <=> ? [X3] :
                    ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                    & v4_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_pre_topc)).

fof(f173,plain,
    ( spl5_18
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f134,f129,f170])).

fof(f129,plain,
    ( spl5_13
  <=> l1_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f134,plain,
    ( u1_struct_0(sK2) = k2_struct_0(sK2)
    | ~ spl5_13 ),
    inference(resolution,[],[f131,f28])).

fof(f28,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f131,plain,
    ( l1_struct_0(sK2)
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f129])).

fof(f156,plain,
    ( spl5_15
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f113,f106,f153])).

fof(f153,plain,
    ( spl5_15
  <=> sK1 = k3_xboole_0(sK1,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f106,plain,
    ( spl5_11
  <=> r1_tarski(sK1,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f113,plain,
    ( sK1 = k3_xboole_0(sK1,u1_struct_0(sK2))
    | ~ spl5_11 ),
    inference(resolution,[],[f108,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f108,plain,
    ( r1_tarski(sK1,u1_struct_0(sK2))
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f106])).

fof(f132,plain,
    ( spl5_13
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f124,f116,f129])).

fof(f116,plain,
    ( spl5_12
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f124,plain,
    ( l1_struct_0(sK2)
    | ~ spl5_12 ),
    inference(resolution,[],[f118,f29])).

fof(f29,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f118,plain,
    ( l1_pre_topc(sK2)
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f116])).

fof(f119,plain,
    ( spl5_12
    | ~ spl5_1
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f114,f58,f43,f116])).

fof(f114,plain,
    ( l1_pre_topc(sK2)
    | ~ spl5_1
    | ~ spl5_4 ),
    inference(resolution,[],[f69,f60])).

fof(f69,plain,
    ( ! [X4] :
        ( ~ m1_pre_topc(X4,sK0)
        | l1_pre_topc(X4) )
    | ~ spl5_1 ),
    inference(resolution,[],[f45,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f109,plain,
    ( spl5_11
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f99,f90,f106])).

fof(f99,plain,
    ( r1_tarski(sK1,u1_struct_0(sK2))
    | ~ spl5_9 ),
    inference(resolution,[],[f92,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f93,plain,
    ( spl5_9
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f78,f48,f90])).

fof(f48,plain,
    ( spl5_2
  <=> sK1 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f78,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f21,f50])).

fof(f50,plain,
    ( sK1 = sK3
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f48])).

fof(f21,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v4_pre_topc(X3,X2)
                  & X1 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              & v4_pre_topc(X1,X0)
              & m1_pre_topc(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v4_pre_topc(X3,X2)
                  & X1 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              & v4_pre_topc(X1,X0)
              & m1_pre_topc(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
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
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
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

fof(f83,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f26,f80])).

fof(f26,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f13])).

fof(f66,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f25,f63])).

fof(f25,plain,(
    v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f61,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f24,f58])).

fof(f24,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f56,plain,(
    ~ spl5_3 ),
    inference(avatar_split_clause,[],[f23,f53])).

fof(f53,plain,
    ( spl5_3
  <=> v4_pre_topc(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f23,plain,(
    ~ v4_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f51,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f22,f48])).

fof(f22,plain,(
    sK1 = sK3 ),
    inference(cnf_transformation,[],[f13])).

fof(f46,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f27,f43])).

fof(f27,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:33:14 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.46  % (1339)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.47  % (1338)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.47  % (1339)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.48  % (1353)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f226,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f46,f51,f56,f61,f66,f83,f93,f109,f119,f132,f156,f173,f208,f209,f210,f225])).
% 0.21/0.48  fof(f225,plain,(
% 0.21/0.48    ~spl5_1 | ~spl5_4 | ~spl5_5 | ~spl5_7 | ~spl5_21),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f224])).
% 0.21/0.48  fof(f224,plain,(
% 0.21/0.48    $false | (~spl5_1 | ~spl5_4 | ~spl5_5 | ~spl5_7 | ~spl5_21)),
% 0.21/0.48    inference(subsumption_resolution,[],[f223,f45])).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    l1_pre_topc(sK0) | ~spl5_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f43])).
% 0.21/0.48  % (1350)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    spl5_1 <=> l1_pre_topc(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.48  fof(f223,plain,(
% 0.21/0.48    ~l1_pre_topc(sK0) | (~spl5_4 | ~spl5_5 | ~spl5_7 | ~spl5_21)),
% 0.21/0.48    inference(subsumption_resolution,[],[f222,f82])).
% 0.21/0.48  fof(f82,plain,(
% 0.21/0.48    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_7),
% 0.21/0.48    inference(avatar_component_clause,[],[f80])).
% 0.21/0.48  fof(f80,plain,(
% 0.21/0.48    spl5_7 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.21/0.48  fof(f222,plain,(
% 0.21/0.48    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl5_4 | ~spl5_5 | ~spl5_21)),
% 0.21/0.48    inference(subsumption_resolution,[],[f221,f60])).
% 0.21/0.48  fof(f60,plain,(
% 0.21/0.48    m1_pre_topc(sK2,sK0) | ~spl5_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f58])).
% 0.21/0.48  fof(f58,plain,(
% 0.21/0.48    spl5_4 <=> m1_pre_topc(sK2,sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.48  fof(f221,plain,(
% 0.21/0.48    ~m1_pre_topc(sK2,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl5_5 | ~spl5_21)),
% 0.21/0.48    inference(resolution,[],[f199,f65])).
% 0.21/0.48  fof(f65,plain,(
% 0.21/0.48    v4_pre_topc(sK1,sK0) | ~spl5_5),
% 0.21/0.48    inference(avatar_component_clause,[],[f63])).
% 0.21/0.48  fof(f63,plain,(
% 0.21/0.48    spl5_5 <=> v4_pre_topc(sK1,sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.48  fof(f199,plain,(
% 0.21/0.48    ( ! [X0] : (~v4_pre_topc(sK1,X0) | ~m1_pre_topc(sK2,X0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) ) | ~spl5_21),
% 0.21/0.48    inference(avatar_component_clause,[],[f198])).
% 0.21/0.48  fof(f198,plain,(
% 0.21/0.48    spl5_21 <=> ! [X0] : (~m1_pre_topc(sK2,X0) | ~v4_pre_topc(sK1,X0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 0.21/0.48  fof(f210,plain,(
% 0.21/0.48    u1_struct_0(sK2) != k2_struct_0(sK2) | sK1 != k3_xboole_0(sK1,u1_struct_0(sK2)) | sK1 != sK3 | v4_pre_topc(sK3,sK2) | ~v4_pre_topc(k3_xboole_0(sK1,k2_struct_0(sK2)),sK2)),
% 0.21/0.48    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.48  fof(f209,plain,(
% 0.21/0.48    sK1 != k3_xboole_0(sK1,u1_struct_0(sK2)) | u1_struct_0(sK2) != k2_struct_0(sK2) | m1_subset_1(k3_xboole_0(sK1,k2_struct_0(sK2)),k1_zfmisc_1(k2_struct_0(sK2))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.21/0.48    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.48  fof(f208,plain,(
% 0.21/0.48    spl5_21 | spl5_22 | ~spl5_23 | ~spl5_9 | ~spl5_18),
% 0.21/0.48    inference(avatar_split_clause,[],[f193,f170,f90,f205,f201,f198])).
% 0.21/0.48  fof(f201,plain,(
% 0.21/0.48    spl5_22 <=> v4_pre_topc(k3_xboole_0(sK1,k2_struct_0(sK2)),sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 0.21/0.48  fof(f205,plain,(
% 0.21/0.48    spl5_23 <=> m1_subset_1(k3_xboole_0(sK1,k2_struct_0(sK2)),k1_zfmisc_1(k2_struct_0(sK2)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).
% 0.21/0.48  fof(f90,plain,(
% 0.21/0.48    spl5_9 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.21/0.48  fof(f170,plain,(
% 0.21/0.48    spl5_18 <=> u1_struct_0(sK2) = k2_struct_0(sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 0.21/0.48  fof(f193,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(k3_xboole_0(sK1,k2_struct_0(sK2)),k1_zfmisc_1(k2_struct_0(sK2))) | v4_pre_topc(k3_xboole_0(sK1,k2_struct_0(sK2)),sK2) | ~m1_pre_topc(sK2,X0) | ~l1_pre_topc(X0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(sK1,X0)) ) | (~spl5_9 | ~spl5_18)),
% 0.21/0.48    inference(forward_demodulation,[],[f137,f172])).
% 0.21/0.48  fof(f172,plain,(
% 0.21/0.48    u1_struct_0(sK2) = k2_struct_0(sK2) | ~spl5_18),
% 0.21/0.48    inference(avatar_component_clause,[],[f170])).
% 0.21/0.48  fof(f137,plain,(
% 0.21/0.48    ( ! [X0] : (v4_pre_topc(k3_xboole_0(sK1,k2_struct_0(sK2)),sK2) | ~m1_subset_1(k3_xboole_0(sK1,k2_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK2))) | ~m1_pre_topc(sK2,X0) | ~l1_pre_topc(X0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(sK1,X0)) ) | ~spl5_9),
% 0.21/0.48    inference(forward_demodulation,[],[f136,f35])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.48  fof(f136,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(k3_xboole_0(sK1,k2_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK2))) | ~m1_pre_topc(sK2,X0) | ~l1_pre_topc(X0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(sK1,X0) | v4_pre_topc(k3_xboole_0(k2_struct_0(sK2),sK1),sK2)) ) | ~spl5_9),
% 0.21/0.48    inference(forward_demodulation,[],[f135,f35])).
% 0.21/0.48  fof(f135,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(k3_xboole_0(k2_struct_0(sK2),sK1),k1_zfmisc_1(u1_struct_0(sK2))) | ~m1_pre_topc(sK2,X0) | ~l1_pre_topc(X0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(sK1,X0) | v4_pre_topc(k3_xboole_0(k2_struct_0(sK2),sK1),sK2)) ) | ~spl5_9),
% 0.21/0.48    inference(superposition,[],[f41,f133])).
% 0.21/0.48  fof(f133,plain,(
% 0.21/0.48    ( ! [X0] : (k9_subset_1(u1_struct_0(sK2),sK1,X0) = k3_xboole_0(X0,sK1)) ) | ~spl5_9),
% 0.21/0.48    inference(forward_demodulation,[],[f97,f98])).
% 0.21/0.48  fof(f98,plain,(
% 0.21/0.48    ( ! [X1] : (k3_xboole_0(X1,sK1) = k9_subset_1(u1_struct_0(sK2),X1,sK1)) ) | ~spl5_9),
% 0.21/0.48    inference(resolution,[],[f92,f39])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.21/0.48  fof(f92,plain,(
% 0.21/0.48    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK2))) | ~spl5_9),
% 0.21/0.48    inference(avatar_component_clause,[],[f90])).
% 0.21/0.48  fof(f97,plain,(
% 0.21/0.48    ( ! [X0] : (k9_subset_1(u1_struct_0(sK2),X0,sK1) = k9_subset_1(u1_struct_0(sK2),sK1,X0)) ) | ~spl5_9),
% 0.21/0.48    inference(resolution,[],[f92,f40])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k9_subset_1)).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    ( ! [X0,X3,X1] : (~m1_subset_1(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X3,X0) | v4_pre_topc(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),X1)) )),
% 0.21/0.48    inference(equality_resolution,[],[f34])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X3,X0) | k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | v4_pre_topc(X2,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : ((v4_pre_topc(X2,X1) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,axiom,(
% 0.21/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => (v4_pre_topc(X2,X1) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_pre_topc)).
% 0.21/0.48  fof(f173,plain,(
% 0.21/0.48    spl5_18 | ~spl5_13),
% 0.21/0.48    inference(avatar_split_clause,[],[f134,f129,f170])).
% 0.21/0.48  fof(f129,plain,(
% 0.21/0.48    spl5_13 <=> l1_struct_0(sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.21/0.48  fof(f134,plain,(
% 0.21/0.48    u1_struct_0(sK2) = k2_struct_0(sK2) | ~spl5_13),
% 0.21/0.48    inference(resolution,[],[f131,f28])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.21/0.48  fof(f131,plain,(
% 0.21/0.48    l1_struct_0(sK2) | ~spl5_13),
% 0.21/0.48    inference(avatar_component_clause,[],[f129])).
% 0.21/0.48  fof(f156,plain,(
% 0.21/0.48    spl5_15 | ~spl5_11),
% 0.21/0.48    inference(avatar_split_clause,[],[f113,f106,f153])).
% 0.21/0.48  fof(f153,plain,(
% 0.21/0.48    spl5_15 <=> sK1 = k3_xboole_0(sK1,u1_struct_0(sK2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 0.21/0.48  fof(f106,plain,(
% 0.21/0.48    spl5_11 <=> r1_tarski(sK1,u1_struct_0(sK2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.21/0.48  fof(f113,plain,(
% 0.21/0.48    sK1 = k3_xboole_0(sK1,u1_struct_0(sK2)) | ~spl5_11),
% 0.21/0.48    inference(resolution,[],[f108,f36])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.48  fof(f108,plain,(
% 0.21/0.48    r1_tarski(sK1,u1_struct_0(sK2)) | ~spl5_11),
% 0.21/0.48    inference(avatar_component_clause,[],[f106])).
% 0.21/0.48  fof(f132,plain,(
% 0.21/0.48    spl5_13 | ~spl5_12),
% 0.21/0.48    inference(avatar_split_clause,[],[f124,f116,f129])).
% 0.21/0.48  fof(f116,plain,(
% 0.21/0.48    spl5_12 <=> l1_pre_topc(sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.21/0.48  fof(f124,plain,(
% 0.21/0.48    l1_struct_0(sK2) | ~spl5_12),
% 0.21/0.48    inference(resolution,[],[f118,f29])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.48  fof(f118,plain,(
% 0.21/0.48    l1_pre_topc(sK2) | ~spl5_12),
% 0.21/0.48    inference(avatar_component_clause,[],[f116])).
% 0.21/0.48  fof(f119,plain,(
% 0.21/0.48    spl5_12 | ~spl5_1 | ~spl5_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f114,f58,f43,f116])).
% 0.21/0.48  fof(f114,plain,(
% 0.21/0.48    l1_pre_topc(sK2) | (~spl5_1 | ~spl5_4)),
% 0.21/0.48    inference(resolution,[],[f69,f60])).
% 0.21/0.48  fof(f69,plain,(
% 0.21/0.48    ( ! [X4] : (~m1_pre_topc(X4,sK0) | l1_pre_topc(X4)) ) | ~spl5_1),
% 0.21/0.48    inference(resolution,[],[f45,f30])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,axiom,(
% 0.21/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.21/0.48  fof(f109,plain,(
% 0.21/0.48    spl5_11 | ~spl5_9),
% 0.21/0.48    inference(avatar_split_clause,[],[f99,f90,f106])).
% 0.21/0.48  fof(f99,plain,(
% 0.21/0.48    r1_tarski(sK1,u1_struct_0(sK2)) | ~spl5_9),
% 0.21/0.48    inference(resolution,[],[f92,f38])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.48  fof(f93,plain,(
% 0.21/0.48    spl5_9 | ~spl5_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f78,f48,f90])).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    spl5_2 <=> sK1 = sK3),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.48  fof(f78,plain,(
% 0.21/0.48    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK2))) | ~spl5_2),
% 0.21/0.48    inference(forward_demodulation,[],[f21,f50])).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    sK1 = sK3 | ~spl5_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f48])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.21/0.48    inference(cnf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~v4_pre_topc(X3,X2) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v4_pre_topc(X1,X0) & m1_pre_topc(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.21/0.48    inference(flattening,[],[f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : ((~v4_pre_topc(X3,X2) & X1 = X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v4_pre_topc(X1,X0)) & m1_pre_topc(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,negated_conjecture,(
% 0.21/0.48    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_pre_topc(X2,X0) => (v4_pre_topc(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) => (X1 = X3 => v4_pre_topc(X3,X2)))))))),
% 0.21/0.48    inference(negated_conjecture,[],[f10])).
% 0.21/0.48  fof(f10,conjecture,(
% 0.21/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_pre_topc(X2,X0) => (v4_pre_topc(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) => (X1 = X3 => v4_pre_topc(X3,X2)))))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_tops_2)).
% 0.21/0.48  fof(f83,plain,(
% 0.21/0.48    spl5_7),
% 0.21/0.48    inference(avatar_split_clause,[],[f26,f80])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.48    inference(cnf_transformation,[],[f13])).
% 0.21/0.48  fof(f66,plain,(
% 0.21/0.48    spl5_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f25,f63])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    v4_pre_topc(sK1,sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f13])).
% 0.21/0.48  fof(f61,plain,(
% 0.21/0.48    spl5_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f24,f58])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    m1_pre_topc(sK2,sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f13])).
% 0.21/0.48  fof(f56,plain,(
% 0.21/0.48    ~spl5_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f23,f53])).
% 0.21/0.48  fof(f53,plain,(
% 0.21/0.48    spl5_3 <=> v4_pre_topc(sK3,sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ~v4_pre_topc(sK3,sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f13])).
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    spl5_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f22,f48])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    sK1 = sK3),
% 0.21/0.48    inference(cnf_transformation,[],[f13])).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    spl5_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f27,f43])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    l1_pre_topc(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f13])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (1339)------------------------------
% 0.21/0.48  % (1339)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (1339)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (1339)Memory used [KB]: 10746
% 0.21/0.48  % (1339)Time elapsed: 0.068 s
% 0.21/0.48  % (1339)------------------------------
% 0.21/0.48  % (1339)------------------------------
% 0.21/0.49  % (1335)Success in time 0.125 s
%------------------------------------------------------------------------------
