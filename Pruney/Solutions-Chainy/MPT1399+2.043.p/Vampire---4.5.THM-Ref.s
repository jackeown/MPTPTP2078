%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:18 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 177 expanded)
%              Number of leaves         :   21 (  55 expanded)
%              Depth                    :   10
%              Number of atoms          :  257 ( 745 expanded)
%              Number of equality atoms :   12 (  60 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f370,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f129,f135,f189,f212,f220,f222,f224,f229,f239,f343,f369])).

fof(f369,plain,(
    ~ spl3_40 ),
    inference(avatar_contradiction_clause,[],[f368])).

fof(f368,plain,
    ( $false
    | ~ spl3_40 ),
    inference(resolution,[],[f363,f36])).

fof(f36,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f363,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl3_40 ),
    inference(resolution,[],[f341,f50])).

fof(f50,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f38,f37])).

fof(f37,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f38,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f341,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X3))
        | ~ v1_xboole_0(X3) )
    | ~ spl3_40 ),
    inference(avatar_component_clause,[],[f340])).

fof(f340,plain,
    ( spl3_40
  <=> ! [X3] :
        ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X3))
        | ~ v1_xboole_0(X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).

fof(f343,plain,
    ( spl3_13
    | spl3_40
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f328,f143,f340,f127])).

fof(f127,plain,
    ( spl3_13
  <=> v1_xboole_0(k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f143,plain,
    ( spl3_15
  <=> r2_hidden(k2_struct_0(sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f328,plain,
    ( ! [X14] :
        ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X14))
        | v1_xboole_0(k2_struct_0(sK0))
        | ~ v1_xboole_0(X14) )
    | ~ spl3_15 ),
    inference(resolution,[],[f202,f188])).

fof(f188,plain,
    ( r2_hidden(k2_struct_0(sK0),k1_xboole_0)
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f143])).

fof(f202,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r2_hidden(X2,X0)
      | v1_xboole_0(X2)
      | ~ v1_xboole_0(X1) ) ),
    inference(resolution,[],[f48,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f239,plain,(
    spl3_24 ),
    inference(avatar_contradiction_clause,[],[f235])).

fof(f235,plain,
    ( $false
    | spl3_24 ),
    inference(resolution,[],[f210,f113])).

fof(f113,plain,(
    m1_subset_1(sK1,k2_struct_0(sK0)) ),
    inference(backward_demodulation,[],[f32,f95])).

fof(f95,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(resolution,[],[f64,f35])).

fof(f35,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( r2_hidden(X3,X2)
                  <=> ( r2_hidden(X1,X3)
                      & v4_pre_topc(X3,X0)
                      & v3_pre_topc(X3,X0) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( r2_hidden(X3,X2)
                  <=> ( r2_hidden(X1,X3)
                      & v4_pre_topc(X3,X0)
                      & v3_pre_topc(X3,X0) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => ~ ( k1_xboole_0 = X2
                    & ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ( r2_hidden(X3,X2)
                        <=> ( r2_hidden(X1,X3)
                            & v4_pre_topc(X3,X0)
                            & v3_pre_topc(X3,X0) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ~ ( k1_xboole_0 = X2
                  & ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                     => ( r2_hidden(X3,X2)
                      <=> ( r2_hidden(X1,X3)
                          & v4_pre_topc(X3,X0)
                          & v3_pre_topc(X3,X0) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_connsp_2)).

fof(f64,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(resolution,[],[f39,f40])).

fof(f40,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f39,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f32,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f210,plain,
    ( ~ m1_subset_1(sK1,k2_struct_0(sK0))
    | spl3_24 ),
    inference(avatar_component_clause,[],[f209])).

fof(f209,plain,
    ( spl3_24
  <=> m1_subset_1(sK1,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f229,plain,(
    spl3_26 ),
    inference(avatar_contradiction_clause,[],[f228])).

fof(f228,plain,
    ( $false
    | spl3_26 ),
    inference(resolution,[],[f219,f35])).

fof(f219,plain,
    ( ~ l1_pre_topc(sK0)
    | spl3_26 ),
    inference(avatar_component_clause,[],[f218])).

fof(f218,plain,
    ( spl3_26
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f224,plain,(
    spl3_25 ),
    inference(avatar_contradiction_clause,[],[f223])).

fof(f223,plain,
    ( $false
    | spl3_25 ),
    inference(resolution,[],[f216,f34])).

fof(f34,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f216,plain,
    ( ~ v2_pre_topc(sK0)
    | spl3_25 ),
    inference(avatar_component_clause,[],[f215])).

fof(f215,plain,
    ( spl3_25
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f222,plain,
    ( ~ spl3_25
    | ~ spl3_26
    | spl3_14 ),
    inference(avatar_split_clause,[],[f221,f140,f218,f215])).

fof(f140,plain,
    ( spl3_14
  <=> v3_pre_topc(k2_struct_0(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f221,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | spl3_14 ),
    inference(resolution,[],[f187,f43])).

fof(f43,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_tops_1)).

fof(f187,plain,
    ( ~ v3_pre_topc(k2_struct_0(sK0),sK0)
    | spl3_14 ),
    inference(avatar_component_clause,[],[f140])).

fof(f220,plain,
    ( ~ spl3_25
    | ~ spl3_26
    | spl3_18 ),
    inference(avatar_split_clause,[],[f213,f159,f218,f215])).

fof(f159,plain,
    ( spl3_18
  <=> v4_pre_topc(k2_struct_0(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f213,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | spl3_18 ),
    inference(resolution,[],[f186,f42])).

fof(f42,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_pre_topc)).

fof(f186,plain,
    ( ~ v4_pre_topc(k2_struct_0(sK0),sK0)
    | spl3_18 ),
    inference(avatar_component_clause,[],[f159])).

fof(f212,plain,
    ( ~ spl3_24
    | spl3_13
    | spl3_20 ),
    inference(avatar_split_clause,[],[f207,f171,f127,f209])).

fof(f171,plain,
    ( spl3_20
  <=> r2_hidden(sK1,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f207,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | ~ m1_subset_1(sK1,k2_struct_0(sK0))
    | spl3_20 ),
    inference(resolution,[],[f185,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f185,plain,
    ( ~ r2_hidden(sK1,k2_struct_0(sK0))
    | spl3_20 ),
    inference(avatar_component_clause,[],[f171])).

fof(f189,plain,
    ( ~ spl3_20
    | ~ spl3_18
    | ~ spl3_14
    | spl3_15 ),
    inference(avatar_split_clause,[],[f182,f143,f140,f159,f171])).

fof(f182,plain,
    ( r2_hidden(k2_struct_0(sK0),k1_xboole_0)
    | ~ v3_pre_topc(k2_struct_0(sK0),sK0)
    | ~ v4_pre_topc(k2_struct_0(sK0),sK0)
    | ~ r2_hidden(sK1,k2_struct_0(sK0)) ),
    inference(resolution,[],[f181,f50])).

fof(f181,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0)))
      | r2_hidden(X3,k1_xboole_0)
      | ~ v3_pre_topc(X3,sK0)
      | ~ v4_pre_topc(X3,sK0)
      | ~ r2_hidden(sK1,X3) ) ),
    inference(forward_demodulation,[],[f180,f31])).

fof(f31,plain,(
    k1_xboole_0 = sK2 ),
    inference(cnf_transformation,[],[f14])).

fof(f180,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v3_pre_topc(X3,sK0)
      | ~ v4_pre_topc(X3,sK0)
      | ~ r2_hidden(sK1,X3)
      | r2_hidden(X3,sK2) ) ),
    inference(forward_demodulation,[],[f29,f95])).

fof(f29,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X3,sK0)
      | ~ v4_pre_topc(X3,sK0)
      | ~ r2_hidden(sK1,X3)
      | r2_hidden(X3,sK2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f135,plain,(
    spl3_12 ),
    inference(avatar_contradiction_clause,[],[f134])).

% (22971)Termination reason: Refutation not found, incomplete strategy
fof(f134,plain,
    ( $false
    | spl3_12 ),
    inference(resolution,[],[f132,f35])).

% (22971)Memory used [KB]: 6140
fof(f132,plain,
    ( ~ l1_pre_topc(sK0)
    | spl3_12 ),
    inference(resolution,[],[f125,f40])).

% (22971)Time elapsed: 0.069 s
fof(f125,plain,
    ( ~ l1_struct_0(sK0)
    | spl3_12 ),
    inference(avatar_component_clause,[],[f124])).

% (22971)------------------------------
% (22971)------------------------------
fof(f124,plain,
    ( spl3_12
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f129,plain,
    ( ~ spl3_12
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f122,f127,f124])).

fof(f122,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK0))
    | ~ l1_struct_0(sK0) ),
    inference(global_subsumption,[],[f33,f121])).

fof(f121,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK0))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f41,f95])).

fof(f41,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f33,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:51:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.46  % (22963)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.22/0.47  % (22963)Refutation found. Thanks to Tanya!
% 0.22/0.47  % SZS status Theorem for theBenchmark
% 0.22/0.47  % (22971)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.22/0.47  % (22971)Refutation not found, incomplete strategy% (22971)------------------------------
% 0.22/0.47  % (22971)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % SZS output start Proof for theBenchmark
% 0.22/0.47  fof(f370,plain,(
% 0.22/0.47    $false),
% 0.22/0.47    inference(avatar_sat_refutation,[],[f129,f135,f189,f212,f220,f222,f224,f229,f239,f343,f369])).
% 0.22/0.47  fof(f369,plain,(
% 0.22/0.47    ~spl3_40),
% 0.22/0.47    inference(avatar_contradiction_clause,[],[f368])).
% 0.22/0.47  fof(f368,plain,(
% 0.22/0.47    $false | ~spl3_40),
% 0.22/0.47    inference(resolution,[],[f363,f36])).
% 0.22/0.47  fof(f36,plain,(
% 0.22/0.47    v1_xboole_0(k1_xboole_0)),
% 0.22/0.47    inference(cnf_transformation,[],[f1])).
% 0.22/0.47  fof(f1,axiom,(
% 0.22/0.47    v1_xboole_0(k1_xboole_0)),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.47  fof(f363,plain,(
% 0.22/0.47    ~v1_xboole_0(k1_xboole_0) | ~spl3_40),
% 0.22/0.47    inference(resolution,[],[f341,f50])).
% 0.22/0.47  fof(f50,plain,(
% 0.22/0.47    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.22/0.47    inference(forward_demodulation,[],[f38,f37])).
% 0.22/0.47  fof(f37,plain,(
% 0.22/0.47    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.22/0.47    inference(cnf_transformation,[],[f3])).
% 0.22/0.47  fof(f3,axiom,(
% 0.22/0.47    ! [X0] : k2_subset_1(X0) = X0),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 0.22/0.47  fof(f38,plain,(
% 0.22/0.47    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f4])).
% 0.22/0.47  fof(f4,axiom,(
% 0.22/0.47    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.22/0.47  fof(f341,plain,(
% 0.22/0.47    ( ! [X3] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X3)) | ~v1_xboole_0(X3)) ) | ~spl3_40),
% 0.22/0.47    inference(avatar_component_clause,[],[f340])).
% 0.22/0.47  fof(f340,plain,(
% 0.22/0.47    spl3_40 <=> ! [X3] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X3)) | ~v1_xboole_0(X3))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).
% 0.22/0.47  fof(f343,plain,(
% 0.22/0.47    spl3_13 | spl3_40 | ~spl3_15),
% 0.22/0.47    inference(avatar_split_clause,[],[f328,f143,f340,f127])).
% 0.22/0.47  fof(f127,plain,(
% 0.22/0.47    spl3_13 <=> v1_xboole_0(k2_struct_0(sK0))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.22/0.47  fof(f143,plain,(
% 0.22/0.47    spl3_15 <=> r2_hidden(k2_struct_0(sK0),k1_xboole_0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.22/0.47  fof(f328,plain,(
% 0.22/0.47    ( ! [X14] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X14)) | v1_xboole_0(k2_struct_0(sK0)) | ~v1_xboole_0(X14)) ) | ~spl3_15),
% 0.22/0.47    inference(resolution,[],[f202,f188])).
% 0.22/0.47  fof(f188,plain,(
% 0.22/0.47    r2_hidden(k2_struct_0(sK0),k1_xboole_0) | ~spl3_15),
% 0.22/0.47    inference(avatar_component_clause,[],[f143])).
% 0.22/0.47  fof(f202,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r2_hidden(X2,X0) | v1_xboole_0(X2) | ~v1_xboole_0(X1)) )),
% 0.22/0.47    inference(resolution,[],[f48,f45])).
% 0.22/0.47  fof(f45,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | v1_xboole_0(X1) | ~v1_xboole_0(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f23])).
% 0.22/0.47  fof(f23,plain,(
% 0.22/0.47    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.22/0.47    inference(ennf_transformation,[],[f2])).
% 0.22/0.47  fof(f2,axiom,(
% 0.22/0.47    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 0.22/0.47  fof(f48,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f25])).
% 0.22/0.47  fof(f25,plain,(
% 0.22/0.47    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.22/0.47    inference(flattening,[],[f24])).
% 0.22/0.47  fof(f24,plain,(
% 0.22/0.47    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.22/0.47    inference(ennf_transformation,[],[f5])).
% 0.22/0.47  fof(f5,axiom,(
% 0.22/0.47    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 0.22/0.47  fof(f239,plain,(
% 0.22/0.47    spl3_24),
% 0.22/0.47    inference(avatar_contradiction_clause,[],[f235])).
% 0.22/0.47  fof(f235,plain,(
% 0.22/0.47    $false | spl3_24),
% 0.22/0.47    inference(resolution,[],[f210,f113])).
% 0.22/0.47  fof(f113,plain,(
% 0.22/0.47    m1_subset_1(sK1,k2_struct_0(sK0))),
% 0.22/0.47    inference(backward_demodulation,[],[f32,f95])).
% 0.22/0.47  fof(f95,plain,(
% 0.22/0.47    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.22/0.47    inference(resolution,[],[f64,f35])).
% 0.22/0.47  fof(f35,plain,(
% 0.22/0.47    l1_pre_topc(sK0)),
% 0.22/0.47    inference(cnf_transformation,[],[f14])).
% 0.22/0.47  fof(f14,plain,(
% 0.22/0.47    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : ((r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.47    inference(flattening,[],[f13])).
% 0.22/0.47  fof(f13,plain,(
% 0.22/0.47    ? [X0] : (? [X1] : (? [X2] : ((k1_xboole_0 = X2 & ! [X3] : ((r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.47    inference(ennf_transformation,[],[f12])).
% 0.22/0.47  fof(f12,negated_conjecture,(
% 0.22/0.47    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(k1_xboole_0 = X2 & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))))))))),
% 0.22/0.47    inference(negated_conjecture,[],[f11])).
% 0.22/0.47  fof(f11,conjecture,(
% 0.22/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(k1_xboole_0 = X2 & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))))))))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_connsp_2)).
% 0.22/0.47  fof(f64,plain,(
% 0.22/0.47    ( ! [X0] : (~l1_pre_topc(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.22/0.47    inference(resolution,[],[f39,f40])).
% 0.22/0.47  fof(f40,plain,(
% 0.22/0.47    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f16])).
% 0.22/0.47  fof(f16,plain,(
% 0.22/0.47    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.22/0.47    inference(ennf_transformation,[],[f7])).
% 0.22/0.47  fof(f7,axiom,(
% 0.22/0.47    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.22/0.47  fof(f39,plain,(
% 0.22/0.47    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f15])).
% 0.22/0.47  fof(f15,plain,(
% 0.22/0.47    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.22/0.47    inference(ennf_transformation,[],[f6])).
% 0.22/0.47  fof(f6,axiom,(
% 0.22/0.47    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.22/0.47  fof(f32,plain,(
% 0.22/0.47    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.22/0.47    inference(cnf_transformation,[],[f14])).
% 0.22/0.47  fof(f210,plain,(
% 0.22/0.47    ~m1_subset_1(sK1,k2_struct_0(sK0)) | spl3_24),
% 0.22/0.47    inference(avatar_component_clause,[],[f209])).
% 0.22/0.47  fof(f209,plain,(
% 0.22/0.47    spl3_24 <=> m1_subset_1(sK1,k2_struct_0(sK0))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.22/0.47  fof(f229,plain,(
% 0.22/0.47    spl3_26),
% 0.22/0.47    inference(avatar_contradiction_clause,[],[f228])).
% 0.22/0.47  fof(f228,plain,(
% 0.22/0.47    $false | spl3_26),
% 0.22/0.47    inference(resolution,[],[f219,f35])).
% 0.22/0.47  fof(f219,plain,(
% 0.22/0.47    ~l1_pre_topc(sK0) | spl3_26),
% 0.22/0.47    inference(avatar_component_clause,[],[f218])).
% 0.22/0.47  fof(f218,plain,(
% 0.22/0.47    spl3_26 <=> l1_pre_topc(sK0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 0.22/0.47  fof(f224,plain,(
% 0.22/0.47    spl3_25),
% 0.22/0.47    inference(avatar_contradiction_clause,[],[f223])).
% 0.22/0.47  fof(f223,plain,(
% 0.22/0.47    $false | spl3_25),
% 0.22/0.47    inference(resolution,[],[f216,f34])).
% 0.22/0.47  fof(f34,plain,(
% 0.22/0.47    v2_pre_topc(sK0)),
% 0.22/0.47    inference(cnf_transformation,[],[f14])).
% 0.22/0.47  fof(f216,plain,(
% 0.22/0.47    ~v2_pre_topc(sK0) | spl3_25),
% 0.22/0.47    inference(avatar_component_clause,[],[f215])).
% 0.22/0.47  fof(f215,plain,(
% 0.22/0.47    spl3_25 <=> v2_pre_topc(sK0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 0.22/0.47  fof(f222,plain,(
% 0.22/0.47    ~spl3_25 | ~spl3_26 | spl3_14),
% 0.22/0.47    inference(avatar_split_clause,[],[f221,f140,f218,f215])).
% 0.22/0.47  fof(f140,plain,(
% 0.22/0.47    spl3_14 <=> v3_pre_topc(k2_struct_0(sK0),sK0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.22/0.47  fof(f221,plain,(
% 0.22/0.47    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | spl3_14),
% 0.22/0.47    inference(resolution,[],[f187,f43])).
% 0.22/0.47  fof(f43,plain,(
% 0.22/0.47    ( ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f22])).
% 0.22/0.47  fof(f22,plain,(
% 0.22/0.47    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.47    inference(flattening,[],[f21])).
% 0.22/0.47  fof(f21,plain,(
% 0.22/0.47    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.47    inference(ennf_transformation,[],[f10])).
% 0.22/0.47  fof(f10,axiom,(
% 0.22/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_struct_0(X0),X0))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_tops_1)).
% 0.22/0.47  fof(f187,plain,(
% 0.22/0.47    ~v3_pre_topc(k2_struct_0(sK0),sK0) | spl3_14),
% 0.22/0.47    inference(avatar_component_clause,[],[f140])).
% 0.22/0.47  fof(f220,plain,(
% 0.22/0.47    ~spl3_25 | ~spl3_26 | spl3_18),
% 0.22/0.47    inference(avatar_split_clause,[],[f213,f159,f218,f215])).
% 0.22/0.47  fof(f159,plain,(
% 0.22/0.47    spl3_18 <=> v4_pre_topc(k2_struct_0(sK0),sK0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.22/0.47  fof(f213,plain,(
% 0.22/0.47    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | spl3_18),
% 0.22/0.47    inference(resolution,[],[f186,f42])).
% 0.22/0.47  fof(f42,plain,(
% 0.22/0.47    ( ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f20])).
% 0.22/0.47  fof(f20,plain,(
% 0.22/0.47    ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.47    inference(flattening,[],[f19])).
% 0.22/0.47  fof(f19,plain,(
% 0.22/0.47    ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.47    inference(ennf_transformation,[],[f9])).
% 0.22/0.47  fof(f9,axiom,(
% 0.22/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_struct_0(X0),X0))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_pre_topc)).
% 0.22/0.47  fof(f186,plain,(
% 0.22/0.47    ~v4_pre_topc(k2_struct_0(sK0),sK0) | spl3_18),
% 0.22/0.47    inference(avatar_component_clause,[],[f159])).
% 0.22/0.47  fof(f212,plain,(
% 0.22/0.47    ~spl3_24 | spl3_13 | spl3_20),
% 0.22/0.47    inference(avatar_split_clause,[],[f207,f171,f127,f209])).
% 0.22/0.47  fof(f171,plain,(
% 0.22/0.47    spl3_20 <=> r2_hidden(sK1,k2_struct_0(sK0))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.22/0.47  fof(f207,plain,(
% 0.22/0.47    v1_xboole_0(k2_struct_0(sK0)) | ~m1_subset_1(sK1,k2_struct_0(sK0)) | spl3_20),
% 0.22/0.47    inference(resolution,[],[f185,f47])).
% 0.22/0.47  fof(f47,plain,(
% 0.22/0.47    ( ! [X0,X1] : (r2_hidden(X1,X0) | v1_xboole_0(X0) | ~m1_subset_1(X1,X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f23])).
% 0.22/0.47  fof(f185,plain,(
% 0.22/0.47    ~r2_hidden(sK1,k2_struct_0(sK0)) | spl3_20),
% 0.22/0.47    inference(avatar_component_clause,[],[f171])).
% 0.22/0.47  fof(f189,plain,(
% 0.22/0.47    ~spl3_20 | ~spl3_18 | ~spl3_14 | spl3_15),
% 0.22/0.47    inference(avatar_split_clause,[],[f182,f143,f140,f159,f171])).
% 0.22/0.47  fof(f182,plain,(
% 0.22/0.47    r2_hidden(k2_struct_0(sK0),k1_xboole_0) | ~v3_pre_topc(k2_struct_0(sK0),sK0) | ~v4_pre_topc(k2_struct_0(sK0),sK0) | ~r2_hidden(sK1,k2_struct_0(sK0))),
% 0.22/0.47    inference(resolution,[],[f181,f50])).
% 0.22/0.47  fof(f181,plain,(
% 0.22/0.47    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0))) | r2_hidden(X3,k1_xboole_0) | ~v3_pre_topc(X3,sK0) | ~v4_pre_topc(X3,sK0) | ~r2_hidden(sK1,X3)) )),
% 0.22/0.47    inference(forward_demodulation,[],[f180,f31])).
% 0.22/0.47  fof(f31,plain,(
% 0.22/0.47    k1_xboole_0 = sK2),
% 0.22/0.47    inference(cnf_transformation,[],[f14])).
% 0.22/0.47  fof(f180,plain,(
% 0.22/0.47    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0))) | ~v3_pre_topc(X3,sK0) | ~v4_pre_topc(X3,sK0) | ~r2_hidden(sK1,X3) | r2_hidden(X3,sK2)) )),
% 0.22/0.47    inference(forward_demodulation,[],[f29,f95])).
% 0.22/0.47  fof(f29,plain,(
% 0.22/0.47    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X3,sK0) | ~v4_pre_topc(X3,sK0) | ~r2_hidden(sK1,X3) | r2_hidden(X3,sK2)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f14])).
% 0.22/0.47  fof(f135,plain,(
% 0.22/0.47    spl3_12),
% 0.22/0.47    inference(avatar_contradiction_clause,[],[f134])).
% 0.22/0.47  % (22971)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.47  fof(f134,plain,(
% 0.22/0.47    $false | spl3_12),
% 0.22/0.47    inference(resolution,[],[f132,f35])).
% 0.22/0.47  
% 0.22/0.47  % (22971)Memory used [KB]: 6140
% 0.22/0.47  fof(f132,plain,(
% 0.22/0.47    ~l1_pre_topc(sK0) | spl3_12),
% 0.22/0.47    inference(resolution,[],[f125,f40])).
% 0.22/0.47  % (22971)Time elapsed: 0.069 s
% 0.22/0.47  fof(f125,plain,(
% 0.22/0.47    ~l1_struct_0(sK0) | spl3_12),
% 0.22/0.47    inference(avatar_component_clause,[],[f124])).
% 0.22/0.47  % (22971)------------------------------
% 0.22/0.47  % (22971)------------------------------
% 0.22/0.47  fof(f124,plain,(
% 0.22/0.47    spl3_12 <=> l1_struct_0(sK0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.22/0.48  fof(f129,plain,(
% 0.22/0.48    ~spl3_12 | ~spl3_13),
% 0.22/0.48    inference(avatar_split_clause,[],[f122,f127,f124])).
% 0.22/0.48  fof(f122,plain,(
% 0.22/0.48    ~v1_xboole_0(k2_struct_0(sK0)) | ~l1_struct_0(sK0)),
% 0.22/0.48    inference(global_subsumption,[],[f33,f121])).
% 0.22/0.48  fof(f121,plain,(
% 0.22/0.48    ~v1_xboole_0(k2_struct_0(sK0)) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.22/0.48    inference(superposition,[],[f41,f95])).
% 0.22/0.48  fof(f41,plain,(
% 0.22/0.48    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f18])).
% 0.22/0.48  fof(f18,plain,(
% 0.22/0.48    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.48    inference(flattening,[],[f17])).
% 0.22/0.48  fof(f17,plain,(
% 0.22/0.48    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f8])).
% 0.22/0.48  fof(f8,axiom,(
% 0.22/0.48    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.22/0.48  fof(f33,plain,(
% 0.22/0.48    ~v2_struct_0(sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f14])).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (22963)------------------------------
% 0.22/0.48  % (22963)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (22963)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (22963)Memory used [KB]: 10746
% 0.22/0.48  % (22963)Time elapsed: 0.065 s
% 0.22/0.48  % (22963)------------------------------
% 0.22/0.48  % (22963)------------------------------
% 0.22/0.48  % (22950)Success in time 0.115 s
%------------------------------------------------------------------------------
