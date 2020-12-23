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
% DateTime   : Thu Dec  3 13:13:36 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 164 expanded)
%              Number of leaves         :   29 (  78 expanded)
%              Depth                    :    7
%              Number of atoms          :  268 ( 548 expanded)
%              Number of equality atoms :   20 (  32 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f199,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f39,f44,f49,f54,f59,f63,f67,f71,f79,f92,f96,f107,f119,f137,f142,f150,f177,f186,f198])).

fof(f198,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_13
    | ~ spl3_19
    | spl3_20
    | ~ spl3_24
    | ~ spl3_25 ),
    inference(avatar_contradiction_clause,[],[f197])).

fof(f197,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_13
    | ~ spl3_19
    | spl3_20
    | ~ spl3_24
    | ~ spl3_25 ),
    inference(subsumption_resolution,[],[f152,f196])).

fof(f196,plain,
    ( ! [X10,X9] : r1_tarski(k3_xboole_0(X9,X10),X9)
    | ~ spl3_24
    | ~ spl3_25 ),
    inference(superposition,[],[f185,f176])).

fof(f176,plain,
    ( ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f175])).

fof(f175,plain,
    ( spl3_24
  <=> ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f185,plain,
    ( ! [X2,X0,X1] : r1_tarski(k3_xboole_0(X0,X2),k2_xboole_0(X1,X0))
    | ~ spl3_25 ),
    inference(avatar_component_clause,[],[f184])).

fof(f184,plain,
    ( spl3_25
  <=> ! [X1,X0,X2] : r1_tarski(k3_xboole_0(X0,X2),k2_xboole_0(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f152,plain,
    ( ~ r1_tarski(k3_xboole_0(sK1,sK2),sK1)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_13
    | ~ spl3_19
    | spl3_20 ),
    inference(unit_resulting_resolution,[],[f38,f43,f48,f141,f149,f106])).

fof(f106,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ v2_tops_2(X2,X0)
        | ~ r1_tarski(X1,X2)
        | v2_tops_2(X1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ l1_pre_topc(X0) )
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl3_13
  <=> ! [X1,X0,X2] :
        ( v2_tops_2(X1,X0)
        | ~ v2_tops_2(X2,X0)
        | ~ r1_tarski(X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f149,plain,
    ( ~ v2_tops_2(k3_xboole_0(sK1,sK2),sK0)
    | spl3_20 ),
    inference(avatar_component_clause,[],[f147])).

fof(f147,plain,
    ( spl3_20
  <=> v2_tops_2(k3_xboole_0(sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f141,plain,
    ( ! [X0] : m1_subset_1(k3_xboole_0(X0,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f140])).

fof(f140,plain,
    ( spl3_19
  <=> ! [X0] : m1_subset_1(k3_xboole_0(X0,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f48,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f46])).

fof(f46,plain,
    ( spl3_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f43,plain,
    ( v2_tops_2(sK1,sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f41])).

fof(f41,plain,
    ( spl3_2
  <=> v2_tops_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f38,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f36])).

fof(f36,plain,
    ( spl3_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f186,plain,
    ( spl3_25
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f80,f69,f65,f184])).

fof(f65,plain,
    ( spl3_7
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f69,plain,
    ( spl3_8
  <=> ! [X1,X0,X2] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f80,plain,
    ( ! [X2,X0,X1] : r1_tarski(k3_xboole_0(X0,X2),k2_xboole_0(X1,X0))
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(superposition,[],[f70,f66])).

fof(f66,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f65])).

fof(f70,plain,
    ( ! [X2,X0,X1] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f69])).

fof(f177,plain,
    ( spl3_24
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f82,f77,f61,f175])).

fof(f61,plain,
    ( spl3_6
  <=> ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f77,plain,
    ( spl3_10
  <=> ! [X1,X0] :
        ( k2_xboole_0(X0,X1) = X1
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f82,plain,
    ( ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(unit_resulting_resolution,[],[f62,f78])).

fof(f78,plain,
    ( ! [X0,X1] :
        ( k2_xboole_0(X0,X1) = X1
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f77])).

fof(f62,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f61])).

fof(f150,plain,
    ( ~ spl3_4
    | ~ spl3_20
    | spl3_5
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f101,f94,f56,f147,f51])).

fof(f51,plain,
    ( spl3_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f56,plain,
    ( spl3_5
  <=> v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f94,plain,
    ( spl3_12
  <=> ! [X1,X0,X2] :
        ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f101,plain,
    ( ~ v2_tops_2(k3_xboole_0(sK1,sK2),sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | spl3_5
    | ~ spl3_12 ),
    inference(superposition,[],[f58,f95])).

fof(f95,plain,
    ( ! [X2,X0,X1] :
        ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f94])).

fof(f58,plain,
    ( ~ v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)
    | spl3_5 ),
    inference(avatar_component_clause,[],[f56])).

fof(f142,plain,
    ( spl3_19
    | ~ spl3_15
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f138,f135,f117,f140])).

fof(f117,plain,
    ( spl3_15
  <=> ! [X0] : k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0,sK2) = k3_xboole_0(X0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f135,plain,
    ( spl3_18
  <=> ! [X0] : m1_subset_1(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f138,plain,
    ( ! [X0] : m1_subset_1(k3_xboole_0(X0,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl3_15
    | ~ spl3_18 ),
    inference(forward_demodulation,[],[f136,f118])).

fof(f118,plain,
    ( ! [X0] : k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0,sK2) = k3_xboole_0(X0,sK2)
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f117])).

fof(f136,plain,
    ( ! [X0] : m1_subset_1(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f135])).

fof(f137,plain,
    ( spl3_18
    | ~ spl3_4
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f98,f90,f51,f135])).

fof(f90,plain,
    ( spl3_11
  <=> ! [X1,X0,X2] :
        ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f98,plain,
    ( ! [X0] : m1_subset_1(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl3_4
    | ~ spl3_11 ),
    inference(unit_resulting_resolution,[],[f53,f91])).

fof(f91,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f90])).

fof(f53,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f51])).

fof(f119,plain,
    ( spl3_15
    | ~ spl3_4
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f100,f94,f51,f117])).

fof(f100,plain,
    ( ! [X0] : k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0,sK2) = k3_xboole_0(X0,sK2)
    | ~ spl3_4
    | ~ spl3_12 ),
    inference(unit_resulting_resolution,[],[f53,f95])).

fof(f107,plain,(
    spl3_13 ),
    inference(avatar_split_clause,[],[f28,f105])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( v2_tops_2(X1,X0)
      | ~ v2_tops_2(X2,X0)
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_tops_2(X1,X0)
              | ~ v2_tops_2(X2,X0)
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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

fof(f96,plain,(
    spl3_12 ),
    inference(avatar_split_clause,[],[f34,f94])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f92,plain,(
    spl3_11 ),
    inference(avatar_split_clause,[],[f33,f90])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(f79,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f31,f77])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f71,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f32,f69])).

fof(f32,plain,(
    ! [X2,X0,X1] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_xboole_1)).

fof(f67,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f29,f65])).

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f63,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f27,f61])).

fof(f27,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f59,plain,(
    ~ spl3_5 ),
    inference(avatar_split_clause,[],[f26,f56])).

fof(f26,plain,(
    ~ v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ~ v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)
    & v2_tops_2(sK1,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f20,f19,f18])).

fof(f18,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
                & v2_tops_2(X1,X0)
                & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X1,X2),sK0)
              & v2_tops_2(X1,sK0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X1,X2),sK0)
            & v2_tops_2(X1,sK0)
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
   => ( ? [X2] :
          ( ~ v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X2),sK0)
          & v2_tops_2(sK1,sK0)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
      & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X2] :
        ( ~ v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X2),sK0)
        & v2_tops_2(sK1,sK0)
        & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
   => ( ~ v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)
      & v2_tops_2(sK1,sK0)
      & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
              & v2_tops_2(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
              & v2_tops_2(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => ( v2_tops_2(X1,X0)
                 => v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( v2_tops_2(X1,X0)
               => v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_tops_2)).

fof(f54,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f24,f51])).

fof(f24,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f21])).

fof(f49,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f23,f46])).

fof(f23,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f21])).

fof(f44,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f25,f41])).

fof(f25,plain,(
    v2_tops_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f39,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f22,f36])).

fof(f22,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:53:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (5693)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.48  % (5700)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.49  % (5693)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f199,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f39,f44,f49,f54,f59,f63,f67,f71,f79,f92,f96,f107,f119,f137,f142,f150,f177,f186,f198])).
% 0.21/0.49  fof(f198,plain,(
% 0.21/0.49    ~spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_13 | ~spl3_19 | spl3_20 | ~spl3_24 | ~spl3_25),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f197])).
% 0.21/0.49  fof(f197,plain,(
% 0.21/0.49    $false | (~spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_13 | ~spl3_19 | spl3_20 | ~spl3_24 | ~spl3_25)),
% 0.21/0.49    inference(subsumption_resolution,[],[f152,f196])).
% 0.21/0.49  fof(f196,plain,(
% 0.21/0.49    ( ! [X10,X9] : (r1_tarski(k3_xboole_0(X9,X10),X9)) ) | (~spl3_24 | ~spl3_25)),
% 0.21/0.49    inference(superposition,[],[f185,f176])).
% 0.21/0.49  fof(f176,plain,(
% 0.21/0.49    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) ) | ~spl3_24),
% 0.21/0.49    inference(avatar_component_clause,[],[f175])).
% 0.21/0.49  fof(f175,plain,(
% 0.21/0.49    spl3_24 <=> ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.21/0.49  fof(f185,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,X2),k2_xboole_0(X1,X0))) ) | ~spl3_25),
% 0.21/0.49    inference(avatar_component_clause,[],[f184])).
% 0.21/0.49  fof(f184,plain,(
% 0.21/0.49    spl3_25 <=> ! [X1,X0,X2] : r1_tarski(k3_xboole_0(X0,X2),k2_xboole_0(X1,X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 0.21/0.49  fof(f152,plain,(
% 0.21/0.49    ~r1_tarski(k3_xboole_0(sK1,sK2),sK1) | (~spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_13 | ~spl3_19 | spl3_20)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f38,f43,f48,f141,f149,f106])).
% 0.21/0.49  fof(f106,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_2(X2,X0) | ~r1_tarski(X1,X2) | v2_tops_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) ) | ~spl3_13),
% 0.21/0.49    inference(avatar_component_clause,[],[f105])).
% 0.21/0.49  fof(f105,plain,(
% 0.21/0.49    spl3_13 <=> ! [X1,X0,X2] : (v2_tops_2(X1,X0) | ~v2_tops_2(X2,X0) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.21/0.49  fof(f149,plain,(
% 0.21/0.49    ~v2_tops_2(k3_xboole_0(sK1,sK2),sK0) | spl3_20),
% 0.21/0.49    inference(avatar_component_clause,[],[f147])).
% 0.21/0.49  fof(f147,plain,(
% 0.21/0.49    spl3_20 <=> v2_tops_2(k3_xboole_0(sK1,sK2),sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.21/0.49  fof(f141,plain,(
% 0.21/0.49    ( ! [X0] : (m1_subset_1(k3_xboole_0(X0,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) ) | ~spl3_19),
% 0.21/0.49    inference(avatar_component_clause,[],[f140])).
% 0.21/0.49  fof(f140,plain,(
% 0.21/0.49    spl3_19 <=> ! [X0] : m1_subset_1(k3_xboole_0(X0,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl3_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f46])).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    spl3_3 <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    v2_tops_2(sK1,sK0) | ~spl3_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f41])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    spl3_2 <=> v2_tops_2(sK1,sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    l1_pre_topc(sK0) | ~spl3_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f36])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    spl3_1 <=> l1_pre_topc(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.49  fof(f186,plain,(
% 0.21/0.49    spl3_25 | ~spl3_7 | ~spl3_8),
% 0.21/0.49    inference(avatar_split_clause,[],[f80,f69,f65,f184])).
% 0.21/0.49  fof(f65,plain,(
% 0.21/0.49    spl3_7 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.49  fof(f69,plain,(
% 0.21/0.49    spl3_8 <=> ! [X1,X0,X2] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.49  fof(f80,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,X2),k2_xboole_0(X1,X0))) ) | (~spl3_7 | ~spl3_8)),
% 0.21/0.49    inference(superposition,[],[f70,f66])).
% 0.21/0.49  fof(f66,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) ) | ~spl3_7),
% 0.21/0.49    inference(avatar_component_clause,[],[f65])).
% 0.21/0.49  fof(f70,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2))) ) | ~spl3_8),
% 0.21/0.49    inference(avatar_component_clause,[],[f69])).
% 0.21/0.49  fof(f177,plain,(
% 0.21/0.49    spl3_24 | ~spl3_6 | ~spl3_10),
% 0.21/0.49    inference(avatar_split_clause,[],[f82,f77,f61,f175])).
% 0.21/0.49  fof(f61,plain,(
% 0.21/0.49    spl3_6 <=> ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.49  fof(f77,plain,(
% 0.21/0.49    spl3_10 <=> ! [X1,X0] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.49  fof(f82,plain,(
% 0.21/0.49    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) ) | (~spl3_6 | ~spl3_10)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f62,f78])).
% 0.21/0.49  fof(f78,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) ) | ~spl3_10),
% 0.21/0.49    inference(avatar_component_clause,[],[f77])).
% 0.21/0.49  fof(f62,plain,(
% 0.21/0.49    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | ~spl3_6),
% 0.21/0.49    inference(avatar_component_clause,[],[f61])).
% 0.21/0.49  fof(f150,plain,(
% 0.21/0.49    ~spl3_4 | ~spl3_20 | spl3_5 | ~spl3_12),
% 0.21/0.49    inference(avatar_split_clause,[],[f101,f94,f56,f147,f51])).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    spl3_4 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.49  fof(f56,plain,(
% 0.21/0.49    spl3_5 <=> v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.49  fof(f94,plain,(
% 0.21/0.49    spl3_12 <=> ! [X1,X0,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.49  fof(f101,plain,(
% 0.21/0.49    ~v2_tops_2(k3_xboole_0(sK1,sK2),sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | (spl3_5 | ~spl3_12)),
% 0.21/0.49    inference(superposition,[],[f58,f95])).
% 0.21/0.49  fof(f95,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) ) | ~spl3_12),
% 0.21/0.49    inference(avatar_component_clause,[],[f94])).
% 0.21/0.49  fof(f58,plain,(
% 0.21/0.49    ~v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) | spl3_5),
% 0.21/0.49    inference(avatar_component_clause,[],[f56])).
% 0.21/0.49  fof(f142,plain,(
% 0.21/0.49    spl3_19 | ~spl3_15 | ~spl3_18),
% 0.21/0.49    inference(avatar_split_clause,[],[f138,f135,f117,f140])).
% 0.21/0.49  fof(f117,plain,(
% 0.21/0.49    spl3_15 <=> ! [X0] : k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0,sK2) = k3_xboole_0(X0,sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.21/0.49  fof(f135,plain,(
% 0.21/0.49    spl3_18 <=> ! [X0] : m1_subset_1(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.21/0.49  fof(f138,plain,(
% 0.21/0.49    ( ! [X0] : (m1_subset_1(k3_xboole_0(X0,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) ) | (~spl3_15 | ~spl3_18)),
% 0.21/0.49    inference(forward_demodulation,[],[f136,f118])).
% 0.21/0.49  fof(f118,plain,(
% 0.21/0.49    ( ! [X0] : (k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0,sK2) = k3_xboole_0(X0,sK2)) ) | ~spl3_15),
% 0.21/0.49    inference(avatar_component_clause,[],[f117])).
% 0.21/0.49  fof(f136,plain,(
% 0.21/0.49    ( ! [X0] : (m1_subset_1(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) ) | ~spl3_18),
% 0.21/0.49    inference(avatar_component_clause,[],[f135])).
% 0.21/0.49  fof(f137,plain,(
% 0.21/0.49    spl3_18 | ~spl3_4 | ~spl3_11),
% 0.21/0.49    inference(avatar_split_clause,[],[f98,f90,f51,f135])).
% 0.21/0.49  fof(f90,plain,(
% 0.21/0.49    spl3_11 <=> ! [X1,X0,X2] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.49  fof(f98,plain,(
% 0.21/0.49    ( ! [X0] : (m1_subset_1(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) ) | (~spl3_4 | ~spl3_11)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f53,f91])).
% 0.21/0.49  fof(f91,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) ) | ~spl3_11),
% 0.21/0.49    inference(avatar_component_clause,[],[f90])).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl3_4),
% 0.21/0.49    inference(avatar_component_clause,[],[f51])).
% 0.21/0.49  fof(f119,plain,(
% 0.21/0.49    spl3_15 | ~spl3_4 | ~spl3_12),
% 0.21/0.49    inference(avatar_split_clause,[],[f100,f94,f51,f117])).
% 0.21/0.49  fof(f100,plain,(
% 0.21/0.49    ( ! [X0] : (k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0,sK2) = k3_xboole_0(X0,sK2)) ) | (~spl3_4 | ~spl3_12)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f53,f95])).
% 0.21/0.49  fof(f107,plain,(
% 0.21/0.49    spl3_13),
% 0.21/0.49    inference(avatar_split_clause,[],[f28,f105])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (v2_tops_2(X1,X0) | ~v2_tops_2(X2,X0) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (v2_tops_2(X1,X0) | ~v2_tops_2(X2,X0) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(flattening,[],[f13])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : ((v2_tops_2(X1,X0) | (~v2_tops_2(X2,X0) | ~r1_tarski(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,axiom,(
% 0.21/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ((v2_tops_2(X2,X0) & r1_tarski(X1,X2)) => v2_tops_2(X1,X0)))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_tops_2)).
% 0.21/0.49  fof(f96,plain,(
% 0.21/0.49    spl3_12),
% 0.21/0.49    inference(avatar_split_clause,[],[f34,f94])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.21/0.49  fof(f92,plain,(
% 0.21/0.49    spl3_11),
% 0.21/0.49    inference(avatar_split_clause,[],[f33,f90])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).
% 0.21/0.49  fof(f79,plain,(
% 0.21/0.49    spl3_10),
% 0.21/0.49    inference(avatar_split_clause,[],[f31,f77])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.21/0.49  fof(f71,plain,(
% 0.21/0.49    spl3_8),
% 0.21/0.49    inference(avatar_split_clause,[],[f32,f69])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_xboole_1)).
% 0.21/0.49  fof(f67,plain,(
% 0.21/0.49    spl3_7),
% 0.21/0.49    inference(avatar_split_clause,[],[f29,f65])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.21/0.49  fof(f63,plain,(
% 0.21/0.49    spl3_6),
% 0.21/0.49    inference(avatar_split_clause,[],[f27,f61])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.49  fof(f59,plain,(
% 0.21/0.49    ~spl3_5),
% 0.21/0.49    inference(avatar_split_clause,[],[f26,f56])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ~v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ((~v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) & v2_tops_2(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_pre_topc(sK0)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f20,f19,f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : (~v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v2_tops_2(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X1,X2),sK0) & v2_tops_2(X1,sK0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_pre_topc(sK0))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ? [X1] : (? [X2] : (~v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X1,X2),sK0) & v2_tops_2(X1,sK0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) => (? [X2] : (~v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X2),sK0) & v2_tops_2(sK1,sK0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ? [X2] : (~v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X2),sK0) & v2_tops_2(sK1,sK0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) => (~v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) & v2_tops_2(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : (~v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v2_tops_2(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 0.21/0.49    inference(flattening,[],[f11])).
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : ((~v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v2_tops_2(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,negated_conjecture,(
% 0.21/0.49    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v2_tops_2(X1,X0) => v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)))))),
% 0.21/0.49    inference(negated_conjecture,[],[f9])).
% 0.21/0.49  fof(f9,conjecture,(
% 0.21/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v2_tops_2(X1,X0) => v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_tops_2)).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    spl3_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f24,f51])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.49    inference(cnf_transformation,[],[f21])).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    spl3_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f23,f46])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.49    inference(cnf_transformation,[],[f21])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    spl3_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f25,f41])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    v2_tops_2(sK1,sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f21])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    spl3_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f22,f36])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    l1_pre_topc(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f21])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (5693)------------------------------
% 0.21/0.49  % (5693)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (5693)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (5693)Memory used [KB]: 6268
% 0.21/0.49  % (5693)Time elapsed: 0.063 s
% 0.21/0.49  % (5693)------------------------------
% 0.21/0.49  % (5693)------------------------------
% 0.21/0.49  % (5688)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.49  % (5687)Success in time 0.129 s
%------------------------------------------------------------------------------
