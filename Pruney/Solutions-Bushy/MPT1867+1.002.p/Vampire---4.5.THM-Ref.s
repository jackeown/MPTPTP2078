%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1867+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:47 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 139 expanded)
%              Number of leaves         :   16 (  49 expanded)
%              Depth                    :   12
%              Number of atoms          :  264 ( 470 expanded)
%              Number of equality atoms :   19 (  22 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f138,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f41,f45,f49,f54,f58,f81,f91,f96,f127,f137])).

fof(f137,plain,
    ( ~ spl5_1
    | ~ spl5_3
    | spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_11 ),
    inference(avatar_contradiction_clause,[],[f136])).

fof(f136,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_3
    | spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_11 ),
    inference(subsumption_resolution,[],[f134,f132])).

fof(f132,plain,
    ( sK1 != sK2(sK0,sK1)
    | ~ spl5_3
    | spl5_4
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(forward_demodulation,[],[f131,f67])).

fof(f67,plain,
    ( ! [X4] : k9_subset_1(u1_struct_0(sK0),X4,X4) = X4
    | ~ spl5_5 ),
    inference(resolution,[],[f57,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X1) = X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k9_subset_1)).

fof(f57,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl5_5
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f131,plain,
    ( sK2(sK0,sK1) != k9_subset_1(u1_struct_0(sK0),sK1,sK1)
    | ~ spl5_3
    | spl5_4
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f129,f80])).

fof(f80,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl5_6
  <=> v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f129,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | sK2(sK0,sK1) != k9_subset_1(u1_struct_0(sK0),sK1,sK1)
    | ~ spl5_3
    | spl5_4
    | ~ spl5_5 ),
    inference(resolution,[],[f70,f57])).

fof(f70,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X0,sK0)
        | k9_subset_1(u1_struct_0(sK0),sK1,X0) != sK2(sK0,sK1) )
    | ~ spl5_3
    | spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f69,f53])).

fof(f53,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | spl5_4 ),
    inference(avatar_component_clause,[],[f52])).

fof(f52,plain,
    ( spl5_4
  <=> v2_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f69,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X0,sK0)
        | k9_subset_1(u1_struct_0(sK0),sK1,X0) != sK2(sK0,sK1)
        | v2_tex_2(sK1,sK0) )
    | ~ spl5_3
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f59,f48])).

fof(f48,plain,
    ( l1_pre_topc(sK0)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f47])).

fof(f47,plain,
    ( spl5_3
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f59,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X0,sK0)
        | k9_subset_1(u1_struct_0(sK0),sK1,X0) != sK2(sK0,sK1)
        | v2_tex_2(sK1,sK0) )
    | ~ spl5_5 ),
    inference(resolution,[],[f57,f25])).

fof(f25,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X3,X0)
      | k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1)
      | v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ~ ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                            & v3_pre_topc(X3,X0) ) )
                    & r1_tarski(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tex_2)).

fof(f134,plain,
    ( sK1 = sK2(sK0,sK1)
    | ~ spl5_1
    | ~ spl5_11 ),
    inference(resolution,[],[f126,f50])).

fof(f50,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | sK1 = X0 )
    | ~ spl5_1 ),
    inference(resolution,[],[f40,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | X0 = X1
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

fof(f40,plain,
    ( v1_xboole_0(sK1)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f39])).

fof(f39,plain,
    ( spl5_1
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f126,plain,
    ( v1_xboole_0(sK2(sK0,sK1))
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl5_11
  <=> v1_xboole_0(sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f127,plain,
    ( spl5_11
    | ~ spl5_1
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f104,f94,f39,f125])).

fof(f94,plain,
    ( spl5_9
  <=> m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f104,plain,
    ( v1_xboole_0(sK2(sK0,sK1))
    | ~ spl5_1
    | ~ spl5_9 ),
    inference(subsumption_resolution,[],[f103,f40])).

fof(f103,plain,
    ( ~ v1_xboole_0(sK1)
    | v1_xboole_0(sK2(sK0,sK1))
    | ~ spl5_9 ),
    inference(resolution,[],[f95,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f95,plain,
    ( m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f94])).

fof(f96,plain,
    ( spl5_9
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f92,f89,f94])).

fof(f89,plain,
    ( spl5_8
  <=> r1_tarski(sK2(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f92,plain,
    ( m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ spl5_8 ),
    inference(resolution,[],[f90,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f90,plain,
    ( r1_tarski(sK2(sK0,sK1),sK1)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f89])).

fof(f91,plain,
    ( spl5_8
    | ~ spl5_3
    | spl5_4
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f74,f56,f52,f47,f89])).

fof(f74,plain,
    ( r1_tarski(sK2(sK0,sK1),sK1)
    | ~ spl5_3
    | spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f73,f53])).

fof(f73,plain,
    ( r1_tarski(sK2(sK0,sK1),sK1)
    | v2_tex_2(sK1,sK0)
    | ~ spl5_3
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f64,f48])).

fof(f64,plain,
    ( ~ l1_pre_topc(sK0)
    | r1_tarski(sK2(sK0,sK1),sK1)
    | v2_tex_2(sK1,sK0)
    | ~ spl5_5 ),
    inference(resolution,[],[f57,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | r1_tarski(sK2(X0,X1),X1)
      | v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f81,plain,
    ( spl5_6
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f77,f56,f47,f43,f39,f79])).

fof(f43,plain,
    ( spl5_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f77,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f76,f40])).

fof(f76,plain,
    ( ~ v1_xboole_0(sK1)
    | v3_pre_topc(sK1,sK0)
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f75,f44])).

fof(f44,plain,
    ( v2_pre_topc(sK0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f43])).

fof(f75,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ v1_xboole_0(sK1)
    | v3_pre_topc(sK1,sK0)
    | ~ spl5_3
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f65,f48])).

fof(f65,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ v1_xboole_0(sK1)
    | v3_pre_topc(sK1,sK0)
    | ~ spl5_5 ),
    inference(resolution,[],[f57,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ v1_xboole_0(X1)
      | v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_xboole_0(X1)
           => v3_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_tops_1)).

fof(f58,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f21,f56])).

fof(f21,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_xboole_0(X1) )
           => v2_tex_2(X1,X0) ) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_xboole_0(X1) )
           => v2_tex_2(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tex_2)).

fof(f54,plain,(
    ~ spl5_4 ),
    inference(avatar_split_clause,[],[f22,f52])).

fof(f22,plain,(
    ~ v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f49,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f24,f47])).

% (23196)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
fof(f24,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f45,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f23,f43])).

fof(f23,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f41,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f20,f39])).

fof(f20,plain,(
    v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f12])).

%------------------------------------------------------------------------------
