%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:05 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 468 expanded)
%              Number of leaves         :    9 (  92 expanded)
%              Depth                    :   26
%              Number of atoms          :  371 (2644 expanded)
%              Number of equality atoms :   20 (  42 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f119,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f49,f50,f113,f118])).

fof(f118,plain,
    ( ~ spl3_1
    | spl3_2 ),
    inference(avatar_contradiction_clause,[],[f117])).

fof(f117,plain,
    ( $false
    | ~ spl3_1
    | spl3_2 ),
    inference(subsumption_resolution,[],[f116,f24])).

fof(f24,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tex_2(X1,X0)
          <~> v1_zfmisc_1(X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tex_2(X1,X0)
          <~> v1_zfmisc_1(X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & ~ v1_xboole_0(X1) )
           => ( v3_tex_2(X1,X0)
            <=> v1_zfmisc_1(X1) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ( v3_tex_2(X1,X0)
          <=> v1_zfmisc_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_tex_2)).

fof(f116,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_1
    | spl3_2 ),
    inference(subsumption_resolution,[],[f115,f23])).

fof(f23,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f115,plain,
    ( v1_xboole_0(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_1
    | spl3_2 ),
    inference(subsumption_resolution,[],[f114,f48])).

fof(f48,plain,
    ( ~ v1_zfmisc_1(sK1)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f46])).

fof(f46,plain,
    ( spl3_2
  <=> v1_zfmisc_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f114,plain,
    ( v1_zfmisc_1(sK1)
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_1 ),
    inference(resolution,[],[f43,f70])).

fof(f70,plain,(
    ! [X0] :
      ( ~ v3_tex_2(X0,sK0)
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(duplicate_literal_removal,[],[f68])).

fof(f68,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_tex_2(X0,sK0) ) ),
    inference(resolution,[],[f67,f55])).

fof(f55,plain,(
    ! [X0] :
      ( v2_tex_2(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_tex_2(X0,sK0) ) ),
    inference(resolution,[],[f36,f28])).

fof(f28,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tex_2(X1,X0)
      | ~ v3_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( X1 = X2
                  | ~ r1_tarski(X1,X2)
                  | ~ v2_tex_2(X2,X0)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( X1 = X2
                  | ~ r1_tarski(X1,X2)
                  | ~ v2_tex_2(X2,X0)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r1_tarski(X1,X2)
                      & v2_tex_2(X2,X0) )
                   => X1 = X2 ) )
              & v2_tex_2(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tex_2)).

fof(f67,plain,(
    ! [X0] :
      ( ~ v2_tex_2(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f66,f28])).

fof(f66,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_zfmisc_1(X0)
      | ~ v2_tex_2(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f65,f25])).

fof(f25,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f65,plain,(
    ! [X0] :
      ( v2_struct_0(sK0)
      | ~ l1_pre_topc(sK0)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_zfmisc_1(X0)
      | ~ v2_tex_2(X0,sK0) ) ),
    inference(resolution,[],[f51,f27])).

fof(f27,plain,(
    v2_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ v2_tdlat_3(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_zfmisc_1(X1)
      | ~ v2_tex_2(X1,X0) ) ),
    inference(subsumption_resolution,[],[f38,f30])).

fof(f30,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_tdlat_3(X0)
       => v2_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tdlat_3)).

fof(f38,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_zfmisc_1(X1)
      | ~ v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> v1_zfmisc_1(X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> v1_zfmisc_1(X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ( v2_tex_2(X1,X0)
          <=> v1_zfmisc_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tex_2)).

fof(f43,plain,
    ( v3_tex_2(sK1,sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f42])).

fof(f42,plain,
    ( spl3_1
  <=> v3_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f113,plain,
    ( spl3_1
    | ~ spl3_2 ),
    inference(avatar_contradiction_clause,[],[f112])).

fof(f112,plain,
    ( $false
    | spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f111,f81])).

fof(f81,plain,
    ( sK1 != sK2(sK0,sK1)
    | spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f80,f44])).

fof(f44,plain,
    ( ~ v3_tex_2(sK1,sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f42])).

fof(f80,plain,
    ( sK1 != sK2(sK0,sK1)
    | v3_tex_2(sK1,sK0)
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f78,f24])).

fof(f78,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | sK1 != sK2(sK0,sK1)
    | v3_tex_2(sK1,sK0)
    | ~ spl3_2 ),
    inference(resolution,[],[f76,f61])).

fof(f61,plain,(
    ! [X0] :
      ( ~ v2_tex_2(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | sK2(sK0,X0) != X0
      | v3_tex_2(X0,sK0) ) ),
    inference(resolution,[],[f34,f28])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | sK2(X0,X1) != X1
      | v3_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f76,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f75,f25])).

fof(f75,plain,
    ( v2_struct_0(sK0)
    | v2_tex_2(sK1,sK0)
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f74,f27])).

fof(f74,plain,
    ( ~ v2_tdlat_3(sK0)
    | v2_struct_0(sK0)
    | v2_tex_2(sK1,sK0)
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f73,f28])).

fof(f73,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_tdlat_3(sK0)
    | v2_struct_0(sK0)
    | v2_tex_2(sK1,sK0)
    | ~ spl3_2 ),
    inference(resolution,[],[f72,f24])).

fof(f72,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0)
        | ~ v2_tdlat_3(X0)
        | v2_struct_0(X0)
        | v2_tex_2(sK1,X0) )
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f71,f23])).

fof(f71,plain,
    ( ! [X0] :
        ( ~ v2_tdlat_3(X0)
        | ~ l1_pre_topc(X0)
        | v1_xboole_0(sK1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | v2_struct_0(X0)
        | v2_tex_2(sK1,X0) )
    | ~ spl3_2 ),
    inference(resolution,[],[f52,f47])).

fof(f47,plain,
    ( v1_zfmisc_1(sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f46])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ v1_zfmisc_1(X1)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_struct_0(X0)
      | v2_tex_2(X1,X0) ) ),
    inference(subsumption_resolution,[],[f37,f30])).

fof(f37,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_zfmisc_1(X1)
      | v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f111,plain,
    ( sK1 = sK2(sK0,sK1)
    | spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f110,f23])).

fof(f110,plain,
    ( v1_xboole_0(sK1)
    | sK1 = sK2(sK0,sK1)
    | spl3_1
    | ~ spl3_2 ),
    inference(resolution,[],[f109,f83])).

fof(f83,plain,
    ( r1_tarski(sK1,sK2(sK0,sK1))
    | spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f82,f44])).

fof(f82,plain,
    ( r1_tarski(sK1,sK2(sK0,sK1))
    | v3_tex_2(sK1,sK0)
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f79,f24])).

fof(f79,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK1,sK2(sK0,sK1))
    | v3_tex_2(sK1,sK0)
    | ~ spl3_2 ),
    inference(resolution,[],[f76,f57])).

fof(f57,plain,(
    ! [X0] :
      ( ~ v2_tex_2(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r1_tarski(X0,sK2(sK0,X0))
      | v3_tex_2(X0,sK0) ) ),
    inference(resolution,[],[f33,f28])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | r1_tarski(X1,sK2(X0,X1))
      | v3_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f109,plain,
    ( ! [X1] :
        ( ~ r1_tarski(X1,sK2(sK0,sK1))
        | v1_xboole_0(X1)
        | sK2(sK0,sK1) = X1 )
    | spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f107,f86])).

fof(f86,plain,
    ( ~ v1_xboole_0(sK2(sK0,sK1))
    | spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f85,f23])).

fof(f85,plain,
    ( ~ v1_xboole_0(sK2(sK0,sK1))
    | v1_xboole_0(sK1)
    | spl3_1
    | ~ spl3_2 ),
    inference(superposition,[],[f39,f84])).

fof(f84,plain,
    ( sK2(sK0,sK1) = k2_xboole_0(sK1,sK2(sK0,sK1))
    | spl3_1
    | ~ spl3_2 ),
    inference(resolution,[],[f83,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k2_xboole_0(X0,X1))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k2_xboole_0(X0,X1))
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
     => ~ v1_xboole_0(k2_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_xboole_0)).

fof(f107,plain,
    ( ! [X1] :
        ( v1_xboole_0(sK2(sK0,sK1))
        | v1_xboole_0(X1)
        | ~ r1_tarski(X1,sK2(sK0,sK1))
        | sK2(sK0,sK1) = X1 )
    | spl3_1
    | ~ spl3_2 ),
    inference(resolution,[],[f105,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ v1_zfmisc_1(X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

fof(f105,plain,
    ( v1_zfmisc_1(sK2(sK0,sK1))
    | spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f104,f44])).

fof(f104,plain,
    ( v1_zfmisc_1(sK2(sK0,sK1))
    | v3_tex_2(sK1,sK0)
    | spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f103,f24])).

fof(f103,plain,
    ( v1_zfmisc_1(sK2(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_tex_2(sK1,sK0)
    | spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f100,f86])).

fof(f100,plain,
    ( v1_xboole_0(sK2(sK0,sK1))
    | v1_zfmisc_1(sK2(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_tex_2(sK1,sK0)
    | ~ spl3_2 ),
    inference(resolution,[],[f88,f76])).

fof(f88,plain,(
    ! [X1] :
      ( ~ v2_tex_2(X1,sK0)
      | v1_xboole_0(sK2(sK0,X1))
      | v1_zfmisc_1(sK2(sK0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v3_tex_2(X1,sK0) ) ),
    inference(subsumption_resolution,[],[f69,f87])).

% (31849)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
fof(f87,plain,(
    ! [X0] :
      ( ~ v2_tex_2(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_subset_1(sK2(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
      | v3_tex_2(X0,sK0) ) ),
    inference(resolution,[],[f31,f28])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v3_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f69,plain,(
    ! [X1] :
      ( ~ m1_subset_1(sK2(sK0,X1),k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_zfmisc_1(sK2(sK0,X1))
      | v1_xboole_0(sK2(sK0,X1))
      | ~ v2_tex_2(X1,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v3_tex_2(X1,sK0) ) ),
    inference(resolution,[],[f67,f56])).

fof(f56,plain,(
    ! [X0] :
      ( v2_tex_2(sK2(sK0,X0),sK0)
      | ~ v2_tex_2(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v3_tex_2(X0,sK0) ) ),
    inference(resolution,[],[f32,f28])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | v2_tex_2(sK2(X0,X1),X0)
      | v3_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f50,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f21,f46,f42])).

fof(f21,plain,
    ( v1_zfmisc_1(sK1)
    | v3_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f49,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f22,f46,f42])).

fof(f22,plain,
    ( ~ v1_zfmisc_1(sK1)
    | ~ v3_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:00:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.49  % (31838)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.19/0.49  % (31838)Refutation not found, incomplete strategy% (31838)------------------------------
% 0.19/0.49  % (31838)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.49  % (31846)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.19/0.49  % (31860)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.19/0.49  % (31841)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.19/0.49  % (31844)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.19/0.49  % (31860)Refutation found. Thanks to Tanya!
% 0.19/0.49  % SZS status Theorem for theBenchmark
% 0.19/0.49  % SZS output start Proof for theBenchmark
% 0.19/0.49  fof(f119,plain,(
% 0.19/0.49    $false),
% 0.19/0.49    inference(avatar_sat_refutation,[],[f49,f50,f113,f118])).
% 0.19/0.49  fof(f118,plain,(
% 0.19/0.49    ~spl3_1 | spl3_2),
% 0.19/0.49    inference(avatar_contradiction_clause,[],[f117])).
% 0.19/0.49  fof(f117,plain,(
% 0.19/0.49    $false | (~spl3_1 | spl3_2)),
% 0.19/0.49    inference(subsumption_resolution,[],[f116,f24])).
% 0.19/0.49  fof(f24,plain,(
% 0.19/0.49    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.19/0.49    inference(cnf_transformation,[],[f10])).
% 0.19/0.49  fof(f10,plain,(
% 0.19/0.49    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.19/0.49    inference(flattening,[],[f9])).
% 0.19/0.49  fof(f9,plain,(
% 0.19/0.49    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.19/0.49    inference(ennf_transformation,[],[f8])).
% 0.19/0.49  fof(f8,negated_conjecture,(
% 0.19/0.49    ~! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v3_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 0.19/0.49    inference(negated_conjecture,[],[f7])).
% 0.19/0.49  fof(f7,conjecture,(
% 0.19/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v3_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_tex_2)).
% 0.19/0.49  fof(f116,plain,(
% 0.19/0.49    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_1 | spl3_2)),
% 0.19/0.49    inference(subsumption_resolution,[],[f115,f23])).
% 0.19/0.49  fof(f23,plain,(
% 0.19/0.49    ~v1_xboole_0(sK1)),
% 0.19/0.49    inference(cnf_transformation,[],[f10])).
% 0.19/0.49  fof(f115,plain,(
% 0.19/0.49    v1_xboole_0(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_1 | spl3_2)),
% 0.19/0.49    inference(subsumption_resolution,[],[f114,f48])).
% 0.19/0.49  fof(f48,plain,(
% 0.19/0.49    ~v1_zfmisc_1(sK1) | spl3_2),
% 0.19/0.49    inference(avatar_component_clause,[],[f46])).
% 0.19/0.49  fof(f46,plain,(
% 0.19/0.49    spl3_2 <=> v1_zfmisc_1(sK1)),
% 0.19/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.19/0.49  fof(f114,plain,(
% 0.19/0.49    v1_zfmisc_1(sK1) | v1_xboole_0(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_1),
% 0.19/0.49    inference(resolution,[],[f43,f70])).
% 0.19/0.49  fof(f70,plain,(
% 0.19/0.49    ( ! [X0] : (~v3_tex_2(X0,sK0) | v1_zfmisc_1(X0) | v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.19/0.49    inference(duplicate_literal_removal,[],[f68])).
% 0.19/0.49  fof(f68,plain,(
% 0.19/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_zfmisc_1(X0) | v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_tex_2(X0,sK0)) )),
% 0.19/0.49    inference(resolution,[],[f67,f55])).
% 0.19/0.49  fof(f55,plain,(
% 0.19/0.49    ( ! [X0] : (v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_tex_2(X0,sK0)) )),
% 0.19/0.49    inference(resolution,[],[f36,f28])).
% 0.19/0.49  fof(f28,plain,(
% 0.19/0.49    l1_pre_topc(sK0)),
% 0.19/0.49    inference(cnf_transformation,[],[f10])).
% 0.19/0.49  fof(f36,plain,(
% 0.19/0.49    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_tex_2(X1,X0) | ~v3_tex_2(X1,X0)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f16])).
% 0.19/0.49  fof(f16,plain,(
% 0.19/0.49    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.19/0.49    inference(flattening,[],[f15])).
% 0.19/0.49  fof(f15,plain,(
% 0.19/0.49    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : ((X1 = X2 | (~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.19/0.49    inference(ennf_transformation,[],[f4])).
% 0.19/0.49  fof(f4,axiom,(
% 0.19/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v2_tex_2(X2,X0)) => X1 = X2)) & v2_tex_2(X1,X0)))))),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tex_2)).
% 0.19/0.49  fof(f67,plain,(
% 0.19/0.49    ( ! [X0] : (~v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 0.19/0.49    inference(subsumption_resolution,[],[f66,f28])).
% 0.19/0.49  fof(f66,plain,(
% 0.19/0.49    ( ! [X0] : (~l1_pre_topc(sK0) | v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_zfmisc_1(X0) | ~v2_tex_2(X0,sK0)) )),
% 0.19/0.49    inference(subsumption_resolution,[],[f65,f25])).
% 0.19/0.49  fof(f25,plain,(
% 0.19/0.49    ~v2_struct_0(sK0)),
% 0.19/0.49    inference(cnf_transformation,[],[f10])).
% 0.19/0.49  fof(f65,plain,(
% 0.19/0.49    ( ! [X0] : (v2_struct_0(sK0) | ~l1_pre_topc(sK0) | v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_zfmisc_1(X0) | ~v2_tex_2(X0,sK0)) )),
% 0.19/0.49    inference(resolution,[],[f51,f27])).
% 0.19/0.49  fof(f27,plain,(
% 0.19/0.49    v2_tdlat_3(sK0)),
% 0.19/0.49    inference(cnf_transformation,[],[f10])).
% 0.19/0.49  fof(f51,plain,(
% 0.19/0.49    ( ! [X0,X1] : (~v2_tdlat_3(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) )),
% 0.19/0.49    inference(subsumption_resolution,[],[f38,f30])).
% 0.19/0.49  fof(f30,plain,(
% 0.19/0.49    ( ! [X0] : (v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f14])).
% 0.19/0.49  fof(f14,plain,(
% 0.19/0.49    ! [X0] : (v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0))),
% 0.19/0.49    inference(flattening,[],[f13])).
% 0.19/0.49  fof(f13,plain,(
% 0.19/0.49    ! [X0] : ((v2_pre_topc(X0) | ~v2_tdlat_3(X0)) | ~l1_pre_topc(X0))),
% 0.19/0.49    inference(ennf_transformation,[],[f3])).
% 0.19/0.49  fof(f3,axiom,(
% 0.19/0.49    ! [X0] : (l1_pre_topc(X0) => (v2_tdlat_3(X0) => v2_pre_topc(X0)))),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tdlat_3)).
% 0.19/0.49  fof(f38,plain,(
% 0.19/0.49    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f18])).
% 0.19/0.49  fof(f18,plain,(
% 0.19/0.49    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.19/0.49    inference(flattening,[],[f17])).
% 0.19/0.49  fof(f17,plain,(
% 0.19/0.49    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.19/0.49    inference(ennf_transformation,[],[f6])).
% 0.19/0.49  fof(f6,axiom,(
% 0.19/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tex_2)).
% 0.19/0.49  fof(f43,plain,(
% 0.19/0.49    v3_tex_2(sK1,sK0) | ~spl3_1),
% 0.19/0.49    inference(avatar_component_clause,[],[f42])).
% 0.19/0.49  fof(f42,plain,(
% 0.19/0.49    spl3_1 <=> v3_tex_2(sK1,sK0)),
% 0.19/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.19/0.49  fof(f113,plain,(
% 0.19/0.49    spl3_1 | ~spl3_2),
% 0.19/0.49    inference(avatar_contradiction_clause,[],[f112])).
% 0.19/0.49  fof(f112,plain,(
% 0.19/0.49    $false | (spl3_1 | ~spl3_2)),
% 0.19/0.49    inference(subsumption_resolution,[],[f111,f81])).
% 0.19/0.49  fof(f81,plain,(
% 0.19/0.49    sK1 != sK2(sK0,sK1) | (spl3_1 | ~spl3_2)),
% 0.19/0.49    inference(subsumption_resolution,[],[f80,f44])).
% 0.19/0.49  fof(f44,plain,(
% 0.19/0.49    ~v3_tex_2(sK1,sK0) | spl3_1),
% 0.19/0.49    inference(avatar_component_clause,[],[f42])).
% 0.19/0.49  fof(f80,plain,(
% 0.19/0.49    sK1 != sK2(sK0,sK1) | v3_tex_2(sK1,sK0) | ~spl3_2),
% 0.19/0.49    inference(subsumption_resolution,[],[f78,f24])).
% 0.19/0.49  fof(f78,plain,(
% 0.19/0.49    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | sK1 != sK2(sK0,sK1) | v3_tex_2(sK1,sK0) | ~spl3_2),
% 0.19/0.49    inference(resolution,[],[f76,f61])).
% 0.19/0.49  fof(f61,plain,(
% 0.19/0.49    ( ! [X0] : (~v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | sK2(sK0,X0) != X0 | v3_tex_2(X0,sK0)) )),
% 0.19/0.49    inference(resolution,[],[f34,f28])).
% 0.19/0.49  fof(f34,plain,(
% 0.19/0.49    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | sK2(X0,X1) != X1 | v3_tex_2(X1,X0)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f16])).
% 0.19/0.49  fof(f76,plain,(
% 0.19/0.49    v2_tex_2(sK1,sK0) | ~spl3_2),
% 0.19/0.49    inference(subsumption_resolution,[],[f75,f25])).
% 0.19/0.49  fof(f75,plain,(
% 0.19/0.49    v2_struct_0(sK0) | v2_tex_2(sK1,sK0) | ~spl3_2),
% 0.19/0.49    inference(subsumption_resolution,[],[f74,f27])).
% 0.19/0.49  fof(f74,plain,(
% 0.19/0.49    ~v2_tdlat_3(sK0) | v2_struct_0(sK0) | v2_tex_2(sK1,sK0) | ~spl3_2),
% 0.19/0.49    inference(subsumption_resolution,[],[f73,f28])).
% 0.19/0.49  fof(f73,plain,(
% 0.19/0.49    ~l1_pre_topc(sK0) | ~v2_tdlat_3(sK0) | v2_struct_0(sK0) | v2_tex_2(sK1,sK0) | ~spl3_2),
% 0.19/0.49    inference(resolution,[],[f72,f24])).
% 0.19/0.49  fof(f72,plain,(
% 0.19/0.49    ( ! [X0] : (~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | v2_struct_0(X0) | v2_tex_2(sK1,X0)) ) | ~spl3_2),
% 0.19/0.49    inference(subsumption_resolution,[],[f71,f23])).
% 0.19/0.49  fof(f71,plain,(
% 0.19/0.49    ( ! [X0] : (~v2_tdlat_3(X0) | ~l1_pre_topc(X0) | v1_xboole_0(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) | v2_struct_0(X0) | v2_tex_2(sK1,X0)) ) | ~spl3_2),
% 0.19/0.49    inference(resolution,[],[f52,f47])).
% 0.19/0.49  fof(f47,plain,(
% 0.19/0.49    v1_zfmisc_1(sK1) | ~spl3_2),
% 0.19/0.49    inference(avatar_component_clause,[],[f46])).
% 0.19/0.49  fof(f52,plain,(
% 0.19/0.49    ( ! [X0,X1] : (~v1_zfmisc_1(X1) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_struct_0(X0) | v2_tex_2(X1,X0)) )),
% 0.19/0.49    inference(subsumption_resolution,[],[f37,f30])).
% 0.19/0.49  fof(f37,plain,(
% 0.19/0.49    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_zfmisc_1(X1) | v2_tex_2(X1,X0)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f18])).
% 0.19/0.49  fof(f111,plain,(
% 0.19/0.49    sK1 = sK2(sK0,sK1) | (spl3_1 | ~spl3_2)),
% 0.19/0.49    inference(subsumption_resolution,[],[f110,f23])).
% 0.19/0.49  fof(f110,plain,(
% 0.19/0.49    v1_xboole_0(sK1) | sK1 = sK2(sK0,sK1) | (spl3_1 | ~spl3_2)),
% 0.19/0.49    inference(resolution,[],[f109,f83])).
% 0.19/0.49  fof(f83,plain,(
% 0.19/0.49    r1_tarski(sK1,sK2(sK0,sK1)) | (spl3_1 | ~spl3_2)),
% 0.19/0.49    inference(subsumption_resolution,[],[f82,f44])).
% 0.19/0.49  fof(f82,plain,(
% 0.19/0.49    r1_tarski(sK1,sK2(sK0,sK1)) | v3_tex_2(sK1,sK0) | ~spl3_2),
% 0.19/0.49    inference(subsumption_resolution,[],[f79,f24])).
% 0.19/0.49  fof(f79,plain,(
% 0.19/0.49    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(sK1,sK2(sK0,sK1)) | v3_tex_2(sK1,sK0) | ~spl3_2),
% 0.19/0.49    inference(resolution,[],[f76,f57])).
% 0.19/0.49  fof(f57,plain,(
% 0.19/0.49    ( ! [X0] : (~v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(X0,sK2(sK0,X0)) | v3_tex_2(X0,sK0)) )),
% 0.19/0.49    inference(resolution,[],[f33,f28])).
% 0.19/0.49  fof(f33,plain,(
% 0.19/0.49    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | r1_tarski(X1,sK2(X0,X1)) | v3_tex_2(X1,X0)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f16])).
% 0.19/0.49  fof(f109,plain,(
% 0.19/0.49    ( ! [X1] : (~r1_tarski(X1,sK2(sK0,sK1)) | v1_xboole_0(X1) | sK2(sK0,sK1) = X1) ) | (spl3_1 | ~spl3_2)),
% 0.19/0.49    inference(subsumption_resolution,[],[f107,f86])).
% 0.19/0.49  fof(f86,plain,(
% 0.19/0.49    ~v1_xboole_0(sK2(sK0,sK1)) | (spl3_1 | ~spl3_2)),
% 0.19/0.49    inference(subsumption_resolution,[],[f85,f23])).
% 0.19/0.49  fof(f85,plain,(
% 0.19/0.49    ~v1_xboole_0(sK2(sK0,sK1)) | v1_xboole_0(sK1) | (spl3_1 | ~spl3_2)),
% 0.19/0.49    inference(superposition,[],[f39,f84])).
% 0.19/0.49  fof(f84,plain,(
% 0.19/0.49    sK2(sK0,sK1) = k2_xboole_0(sK1,sK2(sK0,sK1)) | (spl3_1 | ~spl3_2)),
% 0.19/0.49    inference(resolution,[],[f83,f40])).
% 0.19/0.49  fof(f40,plain,(
% 0.19/0.49    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.19/0.49    inference(cnf_transformation,[],[f20])).
% 0.19/0.49  fof(f20,plain,(
% 0.19/0.49    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.19/0.49    inference(ennf_transformation,[],[f2])).
% 0.19/0.49  fof(f2,axiom,(
% 0.19/0.49    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.19/0.49  fof(f39,plain,(
% 0.19/0.49    ( ! [X0,X1] : (~v1_xboole_0(k2_xboole_0(X0,X1)) | v1_xboole_0(X0)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f19])).
% 0.19/0.49  fof(f19,plain,(
% 0.19/0.49    ! [X0,X1] : (~v1_xboole_0(k2_xboole_0(X0,X1)) | v1_xboole_0(X0))),
% 0.19/0.49    inference(ennf_transformation,[],[f1])).
% 0.19/0.49  fof(f1,axiom,(
% 0.19/0.49    ! [X0,X1] : (~v1_xboole_0(X0) => ~v1_xboole_0(k2_xboole_0(X0,X1)))),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_xboole_0)).
% 0.19/0.49  fof(f107,plain,(
% 0.19/0.49    ( ! [X1] : (v1_xboole_0(sK2(sK0,sK1)) | v1_xboole_0(X1) | ~r1_tarski(X1,sK2(sK0,sK1)) | sK2(sK0,sK1) = X1) ) | (spl3_1 | ~spl3_2)),
% 0.19/0.49    inference(resolution,[],[f105,f29])).
% 0.19/0.49  fof(f29,plain,(
% 0.19/0.49    ( ! [X0,X1] : (~v1_zfmisc_1(X1) | v1_xboole_0(X1) | v1_xboole_0(X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.19/0.49    inference(cnf_transformation,[],[f12])).
% 0.19/0.49  fof(f12,plain,(
% 0.19/0.49    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.19/0.49    inference(flattening,[],[f11])).
% 0.19/0.49  fof(f11,plain,(
% 0.19/0.49    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 0.19/0.49    inference(ennf_transformation,[],[f5])).
% 0.19/0.49  fof(f5,axiom,(
% 0.19/0.49    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).
% 0.19/0.49  fof(f105,plain,(
% 0.19/0.49    v1_zfmisc_1(sK2(sK0,sK1)) | (spl3_1 | ~spl3_2)),
% 0.19/0.49    inference(subsumption_resolution,[],[f104,f44])).
% 0.19/0.49  fof(f104,plain,(
% 0.19/0.49    v1_zfmisc_1(sK2(sK0,sK1)) | v3_tex_2(sK1,sK0) | (spl3_1 | ~spl3_2)),
% 0.19/0.49    inference(subsumption_resolution,[],[f103,f24])).
% 0.19/0.49  fof(f103,plain,(
% 0.19/0.49    v1_zfmisc_1(sK2(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v3_tex_2(sK1,sK0) | (spl3_1 | ~spl3_2)),
% 0.19/0.49    inference(subsumption_resolution,[],[f100,f86])).
% 0.19/0.49  fof(f100,plain,(
% 0.19/0.49    v1_xboole_0(sK2(sK0,sK1)) | v1_zfmisc_1(sK2(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v3_tex_2(sK1,sK0) | ~spl3_2),
% 0.19/0.49    inference(resolution,[],[f88,f76])).
% 0.19/0.49  fof(f88,plain,(
% 0.19/0.49    ( ! [X1] : (~v2_tex_2(X1,sK0) | v1_xboole_0(sK2(sK0,X1)) | v1_zfmisc_1(sK2(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | v3_tex_2(X1,sK0)) )),
% 0.19/0.49    inference(subsumption_resolution,[],[f69,f87])).
% 0.19/0.49  % (31849)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.19/0.49  fof(f87,plain,(
% 0.19/0.49    ( ! [X0] : (~v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(sK2(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | v3_tex_2(X0,sK0)) )),
% 0.19/0.49    inference(resolution,[],[f31,f28])).
% 0.19/0.49  fof(f31,plain,(
% 0.19/0.49    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | v3_tex_2(X1,X0)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f16])).
% 0.19/0.49  fof(f69,plain,(
% 0.19/0.49    ( ! [X1] : (~m1_subset_1(sK2(sK0,X1),k1_zfmisc_1(u1_struct_0(sK0))) | v1_zfmisc_1(sK2(sK0,X1)) | v1_xboole_0(sK2(sK0,X1)) | ~v2_tex_2(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | v3_tex_2(X1,sK0)) )),
% 0.19/0.49    inference(resolution,[],[f67,f56])).
% 0.19/0.49  fof(f56,plain,(
% 0.19/0.49    ( ! [X0] : (v2_tex_2(sK2(sK0,X0),sK0) | ~v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v3_tex_2(X0,sK0)) )),
% 0.19/0.49    inference(resolution,[],[f32,f28])).
% 0.19/0.49  fof(f32,plain,(
% 0.19/0.49    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | v2_tex_2(sK2(X0,X1),X0) | v3_tex_2(X1,X0)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f16])).
% 0.19/0.49  fof(f50,plain,(
% 0.19/0.49    spl3_1 | spl3_2),
% 0.19/0.49    inference(avatar_split_clause,[],[f21,f46,f42])).
% 0.19/0.49  fof(f21,plain,(
% 0.19/0.49    v1_zfmisc_1(sK1) | v3_tex_2(sK1,sK0)),
% 0.19/0.49    inference(cnf_transformation,[],[f10])).
% 0.19/0.49  fof(f49,plain,(
% 0.19/0.49    ~spl3_1 | ~spl3_2),
% 0.19/0.49    inference(avatar_split_clause,[],[f22,f46,f42])).
% 0.19/0.49  fof(f22,plain,(
% 0.19/0.49    ~v1_zfmisc_1(sK1) | ~v3_tex_2(sK1,sK0)),
% 0.19/0.49    inference(cnf_transformation,[],[f10])).
% 0.19/0.49  % SZS output end Proof for theBenchmark
% 0.19/0.49  % (31860)------------------------------
% 0.19/0.49  % (31860)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.49  % (31860)Termination reason: Refutation
% 0.19/0.49  
% 0.19/0.49  % (31860)Memory used [KB]: 10618
% 0.19/0.49  % (31860)Time elapsed: 0.091 s
% 0.19/0.49  % (31860)------------------------------
% 0.19/0.49  % (31860)------------------------------
% 0.19/0.49  % (31840)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.19/0.50  % (31839)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.19/0.50  % (31853)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.19/0.50  % (31855)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.19/0.50  % (31837)Success in time 0.148 s
%------------------------------------------------------------------------------
