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

% Result     : Theorem 2.16s
% Output     : Refutation 2.16s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 153 expanded)
%              Number of leaves         :   20 (  48 expanded)
%              Depth                    :   11
%              Number of atoms          :  228 ( 398 expanded)
%              Number of equality atoms :   21 (  42 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1309,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f119,f124,f193,f203,f205,f582,f594,f604,f1308])).

fof(f1308,plain,
    ( spl3_6
    | ~ spl3_18 ),
    inference(avatar_contradiction_clause,[],[f1296])).

fof(f1296,plain,
    ( $false
    | spl3_6
    | ~ spl3_18 ),
    inference(unit_resulting_resolution,[],[f27,f118,f43,f581])).

fof(f581,plain,
    ( ! [X22,X20] :
        ( ~ r1_tarski(k4_xboole_0(X20,k4_xboole_0(X20,X22)),sK1)
        | v2_tops_2(k4_xboole_0(X20,k4_xboole_0(X20,X22)),sK0)
        | ~ m1_subset_1(X20,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f580])).

fof(f580,plain,
    ( spl3_18
  <=> ! [X20,X22] :
        ( ~ m1_subset_1(X20,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | v2_tops_2(k4_xboole_0(X20,k4_xboole_0(X20,X22)),sK0)
        | ~ r1_tarski(k4_xboole_0(X20,k4_xboole_0(X20,X22)),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f43,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f30,f32])).

fof(f32,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f30,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f118,plain,
    ( ~ v2_tops_2(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK0)
    | spl3_6 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl3_6
  <=> v2_tops_2(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f27,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
              & v2_tops_2(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
              & v2_tops_2(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => ( v2_tops_2(X1,X0)
                 => v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( v2_tops_2(X1,X0)
               => v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_tops_2)).

fof(f604,plain,(
    ~ spl3_14 ),
    inference(avatar_contradiction_clause,[],[f597])).

fof(f597,plain,
    ( $false
    | ~ spl3_14 ),
    inference(unit_resulting_resolution,[],[f47,f224,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X0))
      | ~ r1_tarski(X0,X2) ) ),
    inference(superposition,[],[f78,f31])).

fof(f31,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X0,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f45,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f33,f32])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f45,plain,(
    ! [X2,X0,X1] : r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k2_xboole_0(X0,X2)) ),
    inference(definition_unfolding,[],[f39,f32])).

fof(f39,plain,(
    ! [X2,X0,X1] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_xboole_1)).

fof(f224,plain,
    ( ! [X1] : ~ r1_tarski(k1_zfmisc_1(u1_struct_0(sK0)),X1)
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f223])).

fof(f223,plain,
    ( spl3_14
  <=> ! [X1] : ~ r1_tarski(k1_zfmisc_1(u1_struct_0(sK0)),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f47,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
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

fof(f594,plain,(
    spl3_17 ),
    inference(avatar_contradiction_clause,[],[f592])).

fof(f592,plain,
    ( $false
    | spl3_17 ),
    inference(unit_resulting_resolution,[],[f47,f578,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f578,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | spl3_17 ),
    inference(avatar_component_clause,[],[f576])).

fof(f576,plain,
    ( spl3_17
  <=> m1_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f582,plain,
    ( ~ spl3_17
    | spl3_14
    | spl3_18
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f567,f191,f580,f223,f576])).

fof(f191,plain,
    ( spl3_10
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | v2_tops_2(X0,sK0)
        | ~ r1_tarski(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f567,plain,
    ( ! [X21,X22,X20] :
        ( ~ m1_subset_1(X20,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ r1_tarski(k1_zfmisc_1(u1_struct_0(sK0)),X21)
        | ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ r1_tarski(k4_xboole_0(X20,k4_xboole_0(X20,X22)),sK1)
        | v2_tops_2(k4_xboole_0(X20,k4_xboole_0(X20,X22)),sK0) )
    | ~ spl3_10 ),
    inference(resolution,[],[f366,f208])).

fof(f208,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X0,sK1)
        | v2_tops_2(X0,sK0) )
    | ~ spl3_10 ),
    inference(resolution,[],[f192,f37])).

fof(f192,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | v2_tops_2(X0,sK0)
        | ~ r1_tarski(X0,sK1) )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f191])).

fof(f366,plain,(
    ! [X12,X10,X13,X11] :
      ( r1_tarski(k4_xboole_0(X11,k4_xboole_0(X11,X12)),X10)
      | ~ m1_subset_1(X11,k1_zfmisc_1(X10))
      | ~ r1_tarski(X10,X13)
      | ~ m1_subset_1(X10,k1_zfmisc_1(X10)) ) ),
    inference(superposition,[],[f75,f250])).

fof(f250,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r1_tarski(X0,X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X0)) ) ),
    inference(resolution,[],[f249,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X2),X0)
      | ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X2) = X0 ) ),
    inference(resolution,[],[f78,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f249,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f248])).

fof(f248,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f142,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f142,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_subset_1(X1,X2,X0),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(resolution,[],[f41,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).

fof(f75,plain,(
    ! [X2,X0,X1] : r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X2)),k2_xboole_0(X1,X0)) ),
    inference(superposition,[],[f45,f31])).

fof(f205,plain,(
    spl3_8 ),
    inference(avatar_contradiction_clause,[],[f204])).

fof(f204,plain,
    ( $false
    | spl3_8 ),
    inference(subsumption_resolution,[],[f25,f135])).

fof(f135,plain,
    ( ~ v2_tops_2(sK1,sK0)
    | spl3_8 ),
    inference(avatar_component_clause,[],[f133])).

fof(f133,plain,
    ( spl3_8
  <=> v2_tops_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f25,plain,(
    v2_tops_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f203,plain,(
    spl3_9 ),
    inference(avatar_contradiction_clause,[],[f202])).

fof(f202,plain,
    ( $false
    | spl3_9 ),
    inference(subsumption_resolution,[],[f28,f189])).

fof(f189,plain,
    ( ~ l1_pre_topc(sK0)
    | spl3_9 ),
    inference(avatar_component_clause,[],[f187])).

fof(f187,plain,
    ( spl3_9
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f28,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f193,plain,
    ( ~ spl3_8
    | ~ spl3_9
    | spl3_10 ),
    inference(avatar_split_clause,[],[f182,f191,f187,f133])).

fof(f182,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | ~ l1_pre_topc(sK0)
      | ~ r1_tarski(X0,sK1)
      | ~ v2_tops_2(sK1,sK0)
      | v2_tops_2(X0,sK0) ) ),
    inference(resolution,[],[f29,f27])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | ~ r1_tarski(X1,X2)
      | ~ v2_tops_2(X2,X0)
      | v2_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_tops_2(X1,X0)
              | ~ v2_tops_2(X2,X0)
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_tops_2(X1,X0)
              | ~ v2_tops_2(X2,X0)
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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

fof(f124,plain,(
    spl3_5 ),
    inference(avatar_contradiction_clause,[],[f120])).

fof(f120,plain,
    ( $false
    | spl3_5 ),
    inference(subsumption_resolution,[],[f24,f114])).

fof(f114,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | spl3_5 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl3_5
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f24,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f15])).

fof(f119,plain,
    ( ~ spl3_5
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f102,f116,f112])).

fof(f102,plain,
    ( ~ v2_tops_2(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(superposition,[],[f26,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k4_xboole_0(X1,k4_xboole_0(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f40,f32])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f26,plain,(
    ~ v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 10:34:21 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.51  % (10129)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.52  % (10154)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.52  % (10135)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (10132)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.53  % (10146)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.53  % (10133)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.53  % (10138)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.53  % (10131)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.53  % (10137)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.54  % (10151)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.54  % (10148)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.54  % (10144)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.54  % (10154)Refutation not found, incomplete strategy% (10154)------------------------------
% 0.22/0.54  % (10154)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (10154)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (10154)Memory used [KB]: 6396
% 0.22/0.54  % (10154)Time elapsed: 0.120 s
% 0.22/0.54  % (10154)------------------------------
% 0.22/0.54  % (10154)------------------------------
% 0.22/0.54  % (10147)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.54  % (10152)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.54  % (10150)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.54  % (10143)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.55  % (10134)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.55  % (10158)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.55  % (10155)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.55  % (10140)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.55  % (10141)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.55  % (10139)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.55  % (10142)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.56  % (10130)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.56  % (10156)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.56  % (10156)Refutation not found, incomplete strategy% (10156)------------------------------
% 0.22/0.56  % (10156)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (10156)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (10156)Memory used [KB]: 6268
% 0.22/0.56  % (10156)Time elapsed: 0.152 s
% 0.22/0.56  % (10156)------------------------------
% 0.22/0.56  % (10156)------------------------------
% 0.22/0.56  % (10149)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.57  % (10136)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.57  % (10158)Refutation not found, incomplete strategy% (10158)------------------------------
% 0.22/0.57  % (10158)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (10158)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  
% 0.22/0.57  % (10158)Memory used [KB]: 1663
% 0.22/0.57  % (10158)Time elapsed: 0.159 s
% 0.22/0.57  % (10158)------------------------------
% 0.22/0.57  % (10158)------------------------------
% 0.22/0.57  % (10157)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.57  % (10155)Refutation not found, incomplete strategy% (10155)------------------------------
% 0.22/0.57  % (10155)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.58  % (10139)Refutation not found, incomplete strategy% (10139)------------------------------
% 0.22/0.58  % (10139)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.58  % (10139)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.58  
% 0.22/0.58  % (10139)Memory used [KB]: 10874
% 0.22/0.58  % (10139)Time elapsed: 0.144 s
% 0.22/0.58  % (10139)------------------------------
% 0.22/0.58  % (10139)------------------------------
% 0.22/0.58  % (10155)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.58  % (10157)Refutation not found, incomplete strategy% (10157)------------------------------
% 0.22/0.58  % (10157)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.58  % (10157)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.58  
% 0.22/0.58  % (10157)Memory used [KB]: 10874
% 0.22/0.58  % (10157)Time elapsed: 0.167 s
% 0.22/0.58  % (10157)------------------------------
% 0.22/0.58  % (10157)------------------------------
% 0.22/0.58  
% 0.22/0.58  % (10155)Memory used [KB]: 6396
% 0.22/0.58  % (10155)Time elapsed: 0.147 s
% 0.22/0.58  % (10155)------------------------------
% 0.22/0.58  % (10155)------------------------------
% 0.22/0.60  % (10153)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.82/0.61  % (10145)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.82/0.62  % (10145)Refutation not found, incomplete strategy% (10145)------------------------------
% 1.82/0.62  % (10145)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.82/0.62  % (10145)Termination reason: Refutation not found, incomplete strategy
% 1.82/0.62  
% 1.82/0.62  % (10145)Memory used [KB]: 10618
% 1.82/0.62  % (10145)Time elapsed: 0.184 s
% 1.82/0.62  % (10145)------------------------------
% 1.82/0.62  % (10145)------------------------------
% 2.16/0.68  % (10142)Refutation found. Thanks to Tanya!
% 2.16/0.68  % SZS status Theorem for theBenchmark
% 2.16/0.68  % SZS output start Proof for theBenchmark
% 2.16/0.68  fof(f1309,plain,(
% 2.16/0.68    $false),
% 2.16/0.68    inference(avatar_sat_refutation,[],[f119,f124,f193,f203,f205,f582,f594,f604,f1308])).
% 2.16/0.68  fof(f1308,plain,(
% 2.16/0.68    spl3_6 | ~spl3_18),
% 2.16/0.68    inference(avatar_contradiction_clause,[],[f1296])).
% 2.16/0.68  fof(f1296,plain,(
% 2.16/0.68    $false | (spl3_6 | ~spl3_18)),
% 2.16/0.68    inference(unit_resulting_resolution,[],[f27,f118,f43,f581])).
% 2.16/0.68  fof(f581,plain,(
% 2.16/0.68    ( ! [X22,X20] : (~r1_tarski(k4_xboole_0(X20,k4_xboole_0(X20,X22)),sK1) | v2_tops_2(k4_xboole_0(X20,k4_xboole_0(X20,X22)),sK0) | ~m1_subset_1(X20,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) ) | ~spl3_18),
% 2.16/0.68    inference(avatar_component_clause,[],[f580])).
% 2.16/0.68  fof(f580,plain,(
% 2.16/0.68    spl3_18 <=> ! [X20,X22] : (~m1_subset_1(X20,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_2(k4_xboole_0(X20,k4_xboole_0(X20,X22)),sK0) | ~r1_tarski(k4_xboole_0(X20,k4_xboole_0(X20,X22)),sK1))),
% 2.16/0.68    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 2.16/0.68  fof(f43,plain,(
% 2.16/0.68    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) )),
% 2.16/0.68    inference(definition_unfolding,[],[f30,f32])).
% 2.16/0.68  fof(f32,plain,(
% 2.16/0.68    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.16/0.68    inference(cnf_transformation,[],[f6])).
% 2.16/0.68  fof(f6,axiom,(
% 2.16/0.68    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.16/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.16/0.68  fof(f30,plain,(
% 2.16/0.68    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 2.16/0.68    inference(cnf_transformation,[],[f3])).
% 2.16/0.68  fof(f3,axiom,(
% 2.16/0.68    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 2.16/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 2.16/0.68  fof(f118,plain,(
% 2.16/0.68    ~v2_tops_2(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK0) | spl3_6),
% 2.16/0.68    inference(avatar_component_clause,[],[f116])).
% 2.16/0.68  fof(f116,plain,(
% 2.16/0.68    spl3_6 <=> v2_tops_2(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK0)),
% 2.16/0.68    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 2.16/0.68  fof(f27,plain,(
% 2.16/0.68    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.16/0.68    inference(cnf_transformation,[],[f15])).
% 2.16/0.68  fof(f15,plain,(
% 2.16/0.68    ? [X0] : (? [X1] : (? [X2] : (~v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v2_tops_2(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 2.16/0.68    inference(flattening,[],[f14])).
% 2.16/0.68  fof(f14,plain,(
% 2.16/0.68    ? [X0] : (? [X1] : (? [X2] : ((~v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v2_tops_2(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 2.16/0.68    inference(ennf_transformation,[],[f13])).
% 2.16/0.68  fof(f13,negated_conjecture,(
% 2.16/0.68    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v2_tops_2(X1,X0) => v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)))))),
% 2.16/0.68    inference(negated_conjecture,[],[f12])).
% 2.16/0.68  fof(f12,conjecture,(
% 2.16/0.68    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v2_tops_2(X1,X0) => v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)))))),
% 2.16/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_tops_2)).
% 2.16/0.68  fof(f604,plain,(
% 2.16/0.68    ~spl3_14),
% 2.16/0.68    inference(avatar_contradiction_clause,[],[f597])).
% 2.16/0.68  fof(f597,plain,(
% 2.16/0.68    $false | ~spl3_14),
% 2.16/0.68    inference(unit_resulting_resolution,[],[f47,f224,f83])).
% 2.16/0.68  fof(f83,plain,(
% 2.16/0.68    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X0)) | ~r1_tarski(X0,X2)) )),
% 2.16/0.68    inference(superposition,[],[f78,f31])).
% 2.16/0.68  fof(f31,plain,(
% 2.16/0.68    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 2.16/0.68    inference(cnf_transformation,[],[f1])).
% 2.16/0.68  fof(f1,axiom,(
% 2.16/0.68    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 2.16/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 2.16/0.68  fof(f78,plain,(
% 2.16/0.68    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X2)) | ~r1_tarski(X0,X1)) )),
% 2.16/0.68    inference(superposition,[],[f45,f44])).
% 2.16/0.68  fof(f44,plain,(
% 2.16/0.68    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 2.16/0.68    inference(definition_unfolding,[],[f33,f32])).
% 2.16/0.68  fof(f33,plain,(
% 2.16/0.68    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 2.16/0.68    inference(cnf_transformation,[],[f18])).
% 2.16/0.68  fof(f18,plain,(
% 2.16/0.68    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.16/0.68    inference(ennf_transformation,[],[f4])).
% 2.16/0.68  fof(f4,axiom,(
% 2.16/0.68    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.16/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 2.16/0.68  fof(f45,plain,(
% 2.16/0.68    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k2_xboole_0(X0,X2))) )),
% 2.16/0.68    inference(definition_unfolding,[],[f39,f32])).
% 2.16/0.68  fof(f39,plain,(
% 2.16/0.68    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2))) )),
% 2.16/0.68    inference(cnf_transformation,[],[f5])).
% 2.16/0.68  fof(f5,axiom,(
% 2.16/0.68    ! [X0,X1,X2] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2))),
% 2.16/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_xboole_1)).
% 2.16/0.68  fof(f224,plain,(
% 2.16/0.68    ( ! [X1] : (~r1_tarski(k1_zfmisc_1(u1_struct_0(sK0)),X1)) ) | ~spl3_14),
% 2.16/0.68    inference(avatar_component_clause,[],[f223])).
% 2.16/0.68  fof(f223,plain,(
% 2.16/0.68    spl3_14 <=> ! [X1] : ~r1_tarski(k1_zfmisc_1(u1_struct_0(sK0)),X1)),
% 2.16/0.68    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 2.16/0.68  fof(f47,plain,(
% 2.16/0.68    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.16/0.68    inference(equality_resolution,[],[f35])).
% 2.16/0.68  fof(f35,plain,(
% 2.16/0.68    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.16/0.68    inference(cnf_transformation,[],[f2])).
% 2.16/0.68  fof(f2,axiom,(
% 2.16/0.68    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.16/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.16/0.68  fof(f594,plain,(
% 2.16/0.68    spl3_17),
% 2.16/0.68    inference(avatar_contradiction_clause,[],[f592])).
% 2.16/0.68  fof(f592,plain,(
% 2.16/0.68    $false | spl3_17),
% 2.16/0.68    inference(unit_resulting_resolution,[],[f47,f578,f37])).
% 2.16/0.68  fof(f37,plain,(
% 2.16/0.68    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.16/0.68    inference(cnf_transformation,[],[f10])).
% 2.16/0.68  fof(f10,axiom,(
% 2.16/0.68    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.16/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 2.16/0.68  fof(f578,plain,(
% 2.16/0.68    ~m1_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | spl3_17),
% 2.16/0.68    inference(avatar_component_clause,[],[f576])).
% 2.16/0.68  fof(f576,plain,(
% 2.16/0.68    spl3_17 <=> m1_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.16/0.68    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 2.16/0.68  fof(f582,plain,(
% 2.16/0.68    ~spl3_17 | spl3_14 | spl3_18 | ~spl3_10),
% 2.16/0.68    inference(avatar_split_clause,[],[f567,f191,f580,f223,f576])).
% 2.16/0.68  fof(f191,plain,(
% 2.16/0.68    spl3_10 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_2(X0,sK0) | ~r1_tarski(X0,sK1))),
% 2.16/0.68    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 2.16/0.68  fof(f567,plain,(
% 2.16/0.68    ( ! [X21,X22,X20] : (~m1_subset_1(X20,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~r1_tarski(k1_zfmisc_1(u1_struct_0(sK0)),X21) | ~m1_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~r1_tarski(k4_xboole_0(X20,k4_xboole_0(X20,X22)),sK1) | v2_tops_2(k4_xboole_0(X20,k4_xboole_0(X20,X22)),sK0)) ) | ~spl3_10),
% 2.16/0.68    inference(resolution,[],[f366,f208])).
% 2.16/0.68  fof(f208,plain,(
% 2.16/0.68    ( ! [X0] : (~r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,sK1) | v2_tops_2(X0,sK0)) ) | ~spl3_10),
% 2.16/0.68    inference(resolution,[],[f192,f37])).
% 2.16/0.68  fof(f192,plain,(
% 2.16/0.68    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_2(X0,sK0) | ~r1_tarski(X0,sK1)) ) | ~spl3_10),
% 2.16/0.68    inference(avatar_component_clause,[],[f191])).
% 2.16/0.68  fof(f366,plain,(
% 2.16/0.68    ( ! [X12,X10,X13,X11] : (r1_tarski(k4_xboole_0(X11,k4_xboole_0(X11,X12)),X10) | ~m1_subset_1(X11,k1_zfmisc_1(X10)) | ~r1_tarski(X10,X13) | ~m1_subset_1(X10,k1_zfmisc_1(X10))) )),
% 2.16/0.68    inference(superposition,[],[f75,f250])).
% 2.16/0.68  fof(f250,plain,(
% 2.16/0.68    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r1_tarski(X0,X2) | ~m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 2.16/0.68    inference(resolution,[],[f249,f82])).
% 2.16/0.68  fof(f82,plain,(
% 2.16/0.68    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X2),X0) | ~r1_tarski(X0,X1) | k2_xboole_0(X0,X2) = X0) )),
% 2.16/0.68    inference(resolution,[],[f78,f36])).
% 2.16/0.68  fof(f36,plain,(
% 2.16/0.68    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 2.16/0.68    inference(cnf_transformation,[],[f2])).
% 2.16/0.68  fof(f249,plain,(
% 2.16/0.68    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X1,X2),X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 2.16/0.68    inference(duplicate_literal_removal,[],[f248])).
% 2.16/0.68  fof(f248,plain,(
% 2.16/0.68    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X1,X2),X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.16/0.68    inference(superposition,[],[f142,f42])).
% 2.16/0.68  fof(f42,plain,(
% 2.16/0.68    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.16/0.68    inference(cnf_transformation,[],[f23])).
% 2.16/0.68  fof(f23,plain,(
% 2.16/0.68    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.16/0.68    inference(flattening,[],[f22])).
% 2.16/0.68  fof(f22,plain,(
% 2.16/0.68    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 2.16/0.68    inference(ennf_transformation,[],[f8])).
% 2.16/0.68  fof(f8,axiom,(
% 2.16/0.68    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 2.16/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 2.16/0.68  fof(f142,plain,(
% 2.16/0.68    ( ! [X2,X0,X1] : (r1_tarski(k4_subset_1(X1,X2,X0),X1) | ~m1_subset_1(X2,k1_zfmisc_1(X1)) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.16/0.68    inference(resolution,[],[f41,f38])).
% 2.16/0.68  fof(f38,plain,(
% 2.16/0.68    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 2.16/0.68    inference(cnf_transformation,[],[f10])).
% 2.16/0.68  fof(f41,plain,(
% 2.16/0.68    ( ! [X2,X0,X1] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.16/0.68    inference(cnf_transformation,[],[f21])).
% 2.16/0.68  fof(f21,plain,(
% 2.16/0.68    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.16/0.68    inference(flattening,[],[f20])).
% 2.16/0.68  fof(f20,plain,(
% 2.16/0.68    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 2.16/0.68    inference(ennf_transformation,[],[f7])).
% 2.16/0.68  fof(f7,axiom,(
% 2.16/0.68    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 2.16/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).
% 2.16/0.68  fof(f75,plain,(
% 2.16/0.68    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X2)),k2_xboole_0(X1,X0))) )),
% 2.16/0.68    inference(superposition,[],[f45,f31])).
% 2.16/0.68  fof(f205,plain,(
% 2.16/0.68    spl3_8),
% 2.16/0.68    inference(avatar_contradiction_clause,[],[f204])).
% 2.16/0.68  fof(f204,plain,(
% 2.16/0.68    $false | spl3_8),
% 2.16/0.68    inference(subsumption_resolution,[],[f25,f135])).
% 2.16/0.68  fof(f135,plain,(
% 2.16/0.68    ~v2_tops_2(sK1,sK0) | spl3_8),
% 2.16/0.68    inference(avatar_component_clause,[],[f133])).
% 2.16/0.68  fof(f133,plain,(
% 2.16/0.68    spl3_8 <=> v2_tops_2(sK1,sK0)),
% 2.16/0.68    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 2.16/0.68  fof(f25,plain,(
% 2.16/0.68    v2_tops_2(sK1,sK0)),
% 2.16/0.68    inference(cnf_transformation,[],[f15])).
% 2.16/0.68  fof(f203,plain,(
% 2.16/0.68    spl3_9),
% 2.16/0.68    inference(avatar_contradiction_clause,[],[f202])).
% 2.16/0.68  fof(f202,plain,(
% 2.16/0.68    $false | spl3_9),
% 2.16/0.68    inference(subsumption_resolution,[],[f28,f189])).
% 2.16/0.68  fof(f189,plain,(
% 2.16/0.68    ~l1_pre_topc(sK0) | spl3_9),
% 2.16/0.68    inference(avatar_component_clause,[],[f187])).
% 2.16/0.68  fof(f187,plain,(
% 2.16/0.68    spl3_9 <=> l1_pre_topc(sK0)),
% 2.16/0.68    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 2.16/0.68  fof(f28,plain,(
% 2.16/0.68    l1_pre_topc(sK0)),
% 2.16/0.68    inference(cnf_transformation,[],[f15])).
% 2.16/0.68  fof(f193,plain,(
% 2.16/0.68    ~spl3_8 | ~spl3_9 | spl3_10),
% 2.16/0.68    inference(avatar_split_clause,[],[f182,f191,f187,f133])).
% 2.16/0.68  fof(f182,plain,(
% 2.16/0.68    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~l1_pre_topc(sK0) | ~r1_tarski(X0,sK1) | ~v2_tops_2(sK1,sK0) | v2_tops_2(X0,sK0)) )),
% 2.16/0.68    inference(resolution,[],[f29,f27])).
% 2.16/0.68  fof(f29,plain,(
% 2.16/0.68    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~r1_tarski(X1,X2) | ~v2_tops_2(X2,X0) | v2_tops_2(X1,X0)) )),
% 2.16/0.68    inference(cnf_transformation,[],[f17])).
% 2.16/0.68  fof(f17,plain,(
% 2.16/0.68    ! [X0] : (! [X1] : (! [X2] : (v2_tops_2(X1,X0) | ~v2_tops_2(X2,X0) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 2.16/0.68    inference(flattening,[],[f16])).
% 2.16/0.68  fof(f16,plain,(
% 2.16/0.68    ! [X0] : (! [X1] : (! [X2] : ((v2_tops_2(X1,X0) | (~v2_tops_2(X2,X0) | ~r1_tarski(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 2.16/0.68    inference(ennf_transformation,[],[f11])).
% 2.16/0.68  fof(f11,axiom,(
% 2.16/0.68    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ((v2_tops_2(X2,X0) & r1_tarski(X1,X2)) => v2_tops_2(X1,X0)))))),
% 2.16/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_tops_2)).
% 2.16/0.68  fof(f124,plain,(
% 2.16/0.68    spl3_5),
% 2.16/0.68    inference(avatar_contradiction_clause,[],[f120])).
% 2.16/0.68  fof(f120,plain,(
% 2.16/0.68    $false | spl3_5),
% 2.16/0.68    inference(subsumption_resolution,[],[f24,f114])).
% 2.16/0.68  fof(f114,plain,(
% 2.16/0.68    ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | spl3_5),
% 2.16/0.68    inference(avatar_component_clause,[],[f112])).
% 2.16/0.68  fof(f112,plain,(
% 2.16/0.68    spl3_5 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.16/0.68    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 2.16/0.68  fof(f24,plain,(
% 2.16/0.68    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.16/0.68    inference(cnf_transformation,[],[f15])).
% 2.16/0.68  fof(f119,plain,(
% 2.16/0.68    ~spl3_5 | ~spl3_6),
% 2.16/0.68    inference(avatar_split_clause,[],[f102,f116,f112])).
% 2.16/0.68  fof(f102,plain,(
% 2.16/0.68    ~v2_tops_2(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.16/0.68    inference(superposition,[],[f26,f46])).
% 2.16/0.68  fof(f46,plain,(
% 2.16/0.68    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k4_xboole_0(X1,k4_xboole_0(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 2.16/0.68    inference(definition_unfolding,[],[f40,f32])).
% 2.16/0.68  fof(f40,plain,(
% 2.16/0.68    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)) )),
% 2.16/0.68    inference(cnf_transformation,[],[f19])).
% 2.16/0.68  fof(f19,plain,(
% 2.16/0.68    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 2.16/0.68    inference(ennf_transformation,[],[f9])).
% 2.16/0.68  fof(f9,axiom,(
% 2.16/0.68    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 2.16/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 2.16/0.68  fof(f26,plain,(
% 2.16/0.68    ~v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)),
% 2.16/0.68    inference(cnf_transformation,[],[f15])).
% 2.16/0.68  % SZS output end Proof for theBenchmark
% 2.16/0.68  % (10142)------------------------------
% 2.16/0.68  % (10142)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.16/0.68  % (10142)Termination reason: Refutation
% 2.16/0.68  
% 2.16/0.68  % (10142)Memory used [KB]: 7036
% 2.16/0.68  % (10142)Time elapsed: 0.263 s
% 2.16/0.68  % (10142)------------------------------
% 2.16/0.68  % (10142)------------------------------
% 2.16/0.68  % (10128)Success in time 0.308 s
%------------------------------------------------------------------------------
