%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:49 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 226 expanded)
%              Number of leaves         :   32 (  89 expanded)
%              Depth                    :   11
%              Number of atoms          :  396 ( 779 expanded)
%              Number of equality atoms :   84 ( 177 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f277,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f73,f74,f79,f84,f89,f120,f127,f149,f201,f215,f235,f248,f255,f257,f266,f276])).

fof(f276,plain,
    ( spl2_2
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_9 ),
    inference(avatar_contradiction_clause,[],[f275])).

fof(f275,plain,
    ( $false
    | spl2_2
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_9 ),
    inference(subsumption_resolution,[],[f274,f83])).

fof(f83,plain,
    ( l1_pre_topc(sK0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl2_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f274,plain,
    ( ~ l1_pre_topc(sK0)
    | spl2_2
    | ~ spl2_3
    | ~ spl2_9 ),
    inference(subsumption_resolution,[],[f273,f78])).

fof(f78,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl2_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f273,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl2_2
    | ~ spl2_9 ),
    inference(subsumption_resolution,[],[f272,f72])).

fof(f72,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl2_2
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f272,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_9 ),
    inference(superposition,[],[f52,f136])).

fof(f136,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f134])).

fof(f134,plain,
    ( spl2_9
  <=> sK1 = k2_pre_topc(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

fof(f266,plain,
    ( spl2_9
    | ~ spl2_7
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f265,f130,f124,f134])).

fof(f124,plain,
    ( spl2_7
  <=> r1_tarski(sK1,k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f130,plain,
    ( spl2_8
  <=> r1_tarski(k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f265,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl2_7
    | ~ spl2_8 ),
    inference(subsumption_resolution,[],[f264,f126])).

fof(f126,plain,
    ( r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f124])).

fof(f264,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | ~ spl2_8 ),
    inference(resolution,[],[f131,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f131,plain,
    ( r1_tarski(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f130])).

fof(f257,plain,
    ( spl2_8
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f256,f81,f76,f66,f130])).

fof(f66,plain,
    ( spl2_1
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f256,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | r1_tarski(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f162,f63])).

fof(f63,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f162,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | r1_tarski(k2_pre_topc(sK0,sK1),sK1)
    | ~ r1_tarski(sK1,sK1)
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(resolution,[],[f161,f78])).

fof(f161,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v4_pre_topc(X0,sK0)
        | r1_tarski(k2_pre_topc(sK0,sK1),X0)
        | ~ r1_tarski(sK1,X0) )
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f158,f83])).

fof(f158,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK1,X0)
        | ~ v4_pre_topc(X0,sK0)
        | r1_tarski(k2_pre_topc(sK0,sK1),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl2_3 ),
    inference(resolution,[],[f56,f78])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X2,X1)
      | ~ v4_pre_topc(X1,X0)
      | r1_tarski(k2_pre_topc(X0,X2),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X2),X1)
              | ~ r1_tarski(X2,X1)
              | ~ v4_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X2),X1)
              | ~ r1_tarski(X2,X1)
              | ~ v4_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
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

fof(f255,plain,
    ( sK1 != k2_pre_topc(sK0,sK1)
    | v4_pre_topc(sK1,sK0)
    | ~ v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f248,plain,
    ( spl2_9
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f247,f224,f81,f76,f134])).

fof(f224,plain,
    ( spl2_14
  <=> sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f247,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_14 ),
    inference(subsumption_resolution,[],[f246,f83])).

fof(f246,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl2_3
    | ~ spl2_14 ),
    inference(subsumption_resolution,[],[f240,f78])).

fof(f240,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_14 ),
    inference(superposition,[],[f154,f226])).

fof(f226,plain,
    ( sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f224])).

fof(f154,plain,(
    ! [X2,X3] :
      ( k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2) ) ),
    inference(subsumption_resolution,[],[f153,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f153,plain,(
    ! [X2,X3] :
      ( k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) ) ),
    inference(duplicate_literal_removal,[],[f150])).

fof(f150,plain,(
    ! [X2,X3] :
      ( k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ) ),
    inference(superposition,[],[f54,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
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

fof(f54,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

fof(f235,plain,
    ( spl2_14
    | ~ spl2_13 ),
    inference(avatar_split_clause,[],[f222,f212,f224])).

fof(f212,plain,
    ( spl2_13
  <=> sK1 = k2_xboole_0(k2_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f222,plain,
    ( sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_13 ),
    inference(superposition,[],[f96,f214])).

fof(f214,plain,
    ( sK1 = k2_xboole_0(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f212])).

fof(f96,plain,(
    ! [X2,X3] : k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2) ),
    inference(superposition,[],[f90,f60])).

fof(f60,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f90,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X1,X0)) ),
    inference(superposition,[],[f60,f50])).

fof(f50,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f215,plain,
    ( spl2_13
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f205,f193,f212])).

fof(f193,plain,
    ( spl2_11
  <=> sK1 = k2_xboole_0(k2_tops_1(sK0,sK1),k3_xboole_0(sK1,k3_xboole_0(sK1,k1_tops_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f205,plain,
    ( sK1 = k2_xboole_0(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_11 ),
    inference(superposition,[],[f48,f195])).

fof(f195,plain,
    ( sK1 = k2_xboole_0(k2_tops_1(sK0,sK1),k3_xboole_0(sK1,k3_xboole_0(sK1,k1_tops_1(sK0,sK1))))
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f193])).

fof(f48,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_1)).

fof(f201,plain,
    ( spl2_11
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f200,f115,f193])).

fof(f115,plain,
    ( spl2_6
  <=> k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f200,plain,
    ( sK1 = k2_xboole_0(k2_tops_1(sK0,sK1),k3_xboole_0(sK1,k3_xboole_0(sK1,k1_tops_1(sK0,sK1))))
    | ~ spl2_6 ),
    inference(superposition,[],[f110,f117])).

fof(f117,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f115])).

fof(f110,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X0,X1))) = X0 ),
    inference(forward_demodulation,[],[f104,f49])).

fof(f49,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f104,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(superposition,[],[f59,f61])).

fof(f61,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f59,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_xboole_1)).

fof(f149,plain,
    ( spl2_10
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f144,f86,f81,f76,f146])).

fof(f146,plain,
    ( spl2_10
  <=> v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f86,plain,
    ( spl2_5
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f144,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,sK1),sK0)
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f143,f88])).

fof(f88,plain,
    ( v2_pre_topc(sK0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f86])).

fof(f143,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,sK1),sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f140,f83])).

fof(f140,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl2_3 ),
    inference(resolution,[],[f55,f78])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_pre_topc(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_tops_1)).

fof(f127,plain,
    ( spl2_7
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f122,f81,f76,f124])).

fof(f122,plain,
    ( r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f121,f83])).

fof(f121,plain,
    ( r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_3 ),
    inference(resolution,[],[f58,f78])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(X1,k2_pre_topc(X0,X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).

fof(f120,plain,
    ( spl2_6
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f119,f76,f70,f115])).

fof(f119,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f112,f78])).

fof(f112,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_2 ),
    inference(superposition,[],[f71,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f71,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f70])).

fof(f89,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f40,f86])).

fof(f40,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | ~ v4_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f34,f36,f35])).

fof(f35,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
              | ~ v4_pre_topc(X1,X0) )
            & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
              | v4_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ( k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1))
            | ~ v4_pre_topc(X1,sK0) )
          & ( k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1))
            | v4_pre_topc(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X1] :
        ( ( k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1))
          | ~ v4_pre_topc(X1,sK0) )
        & ( k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1))
          | v4_pre_topc(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
        | ~ v4_pre_topc(sK1,sK0) )
      & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
        | v4_pre_topc(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).

fof(f84,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f41,f81])).

fof(f41,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f79,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f42,f76])).

fof(f42,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f37])).

fof(f74,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f43,f70,f66])).

fof(f43,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f73,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f44,f70,f66])).

fof(f44,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f37])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:38:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (21449)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.51  % (21466)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.51  % (21444)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.51  % (21454)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.51  % (21442)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.52  % (21441)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.52  % (21457)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.52  % (21457)Refutation not found, incomplete strategy% (21457)------------------------------
% 0.21/0.52  % (21457)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (21465)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.52  % (21455)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.52  % (21445)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.52  % (21460)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.52  % (21447)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (21443)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.53  % (21453)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.53  % (21457)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (21457)Memory used [KB]: 10618
% 0.21/0.53  % (21457)Time elapsed: 0.106 s
% 0.21/0.53  % (21457)------------------------------
% 0.21/0.53  % (21457)------------------------------
% 0.21/0.53  % (21448)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.53  % (21452)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.53  % (21464)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.53  % (21470)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.53  % (21461)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.53  % (21470)Refutation not found, incomplete strategy% (21470)------------------------------
% 0.21/0.53  % (21470)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (21470)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (21470)Memory used [KB]: 1663
% 0.21/0.53  % (21470)Time elapsed: 0.001 s
% 0.21/0.53  % (21470)------------------------------
% 0.21/0.53  % (21470)------------------------------
% 0.21/0.53  % (21458)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.53  % (21446)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.54  % (21467)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (21459)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.54  % (21450)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.54  % (21469)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.54  % (21468)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.54  % (21463)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.54  % (21456)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.54  % (21451)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.55  % (21451)Refutation not found, incomplete strategy% (21451)------------------------------
% 0.21/0.55  % (21451)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (21462)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.56  % (21462)Refutation found. Thanks to Tanya!
% 0.21/0.56  % SZS status Theorem for theBenchmark
% 0.21/0.56  % (21469)Refutation not found, incomplete strategy% (21469)------------------------------
% 0.21/0.56  % (21469)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (21469)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (21469)Memory used [KB]: 10746
% 0.21/0.56  % (21469)Time elapsed: 0.150 s
% 0.21/0.56  % (21469)------------------------------
% 0.21/0.56  % (21469)------------------------------
% 0.21/0.56  % (21451)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (21451)Memory used [KB]: 10746
% 0.21/0.56  % (21451)Time elapsed: 0.142 s
% 0.21/0.56  % (21451)------------------------------
% 0.21/0.56  % (21451)------------------------------
% 0.21/0.57  % SZS output start Proof for theBenchmark
% 0.21/0.57  fof(f277,plain,(
% 0.21/0.57    $false),
% 0.21/0.57    inference(avatar_sat_refutation,[],[f73,f74,f79,f84,f89,f120,f127,f149,f201,f215,f235,f248,f255,f257,f266,f276])).
% 0.21/0.57  fof(f276,plain,(
% 0.21/0.57    spl2_2 | ~spl2_3 | ~spl2_4 | ~spl2_9),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f275])).
% 0.21/0.57  fof(f275,plain,(
% 0.21/0.57    $false | (spl2_2 | ~spl2_3 | ~spl2_4 | ~spl2_9)),
% 0.21/0.57    inference(subsumption_resolution,[],[f274,f83])).
% 0.21/0.57  fof(f83,plain,(
% 0.21/0.57    l1_pre_topc(sK0) | ~spl2_4),
% 0.21/0.57    inference(avatar_component_clause,[],[f81])).
% 0.21/0.57  fof(f81,plain,(
% 0.21/0.57    spl2_4 <=> l1_pre_topc(sK0)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.57  fof(f274,plain,(
% 0.21/0.57    ~l1_pre_topc(sK0) | (spl2_2 | ~spl2_3 | ~spl2_9)),
% 0.21/0.57    inference(subsumption_resolution,[],[f273,f78])).
% 0.21/0.57  fof(f78,plain,(
% 0.21/0.57    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_3),
% 0.21/0.57    inference(avatar_component_clause,[],[f76])).
% 0.21/0.57  fof(f76,plain,(
% 0.21/0.57    spl2_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.57  fof(f273,plain,(
% 0.21/0.57    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (spl2_2 | ~spl2_9)),
% 0.21/0.57    inference(subsumption_resolution,[],[f272,f72])).
% 0.21/0.57  fof(f72,plain,(
% 0.21/0.57    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | spl2_2),
% 0.21/0.57    inference(avatar_component_clause,[],[f70])).
% 0.21/0.57  fof(f70,plain,(
% 0.21/0.57    spl2_2 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.57  fof(f272,plain,(
% 0.21/0.57    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl2_9),
% 0.21/0.57    inference(superposition,[],[f52,f136])).
% 0.21/0.57  fof(f136,plain,(
% 0.21/0.57    sK1 = k2_pre_topc(sK0,sK1) | ~spl2_9),
% 0.21/0.57    inference(avatar_component_clause,[],[f134])).
% 0.21/0.57  fof(f134,plain,(
% 0.21/0.57    spl2_9 <=> sK1 = k2_pre_topc(sK0,sK1)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.21/0.57  fof(f52,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f22])).
% 0.21/0.57  fof(f22,plain,(
% 0.21/0.57    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.57    inference(ennf_transformation,[],[f14])).
% 0.21/0.57  fof(f14,axiom,(
% 0.21/0.57    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).
% 0.21/0.57  fof(f266,plain,(
% 0.21/0.57    spl2_9 | ~spl2_7 | ~spl2_8),
% 0.21/0.57    inference(avatar_split_clause,[],[f265,f130,f124,f134])).
% 0.21/0.57  fof(f124,plain,(
% 0.21/0.57    spl2_7 <=> r1_tarski(sK1,k2_pre_topc(sK0,sK1))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.21/0.57  fof(f130,plain,(
% 0.21/0.57    spl2_8 <=> r1_tarski(k2_pre_topc(sK0,sK1),sK1)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.21/0.57  fof(f265,plain,(
% 0.21/0.57    sK1 = k2_pre_topc(sK0,sK1) | (~spl2_7 | ~spl2_8)),
% 0.21/0.57    inference(subsumption_resolution,[],[f264,f126])).
% 0.21/0.57  fof(f126,plain,(
% 0.21/0.57    r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | ~spl2_7),
% 0.21/0.57    inference(avatar_component_clause,[],[f124])).
% 0.21/0.57  fof(f264,plain,(
% 0.21/0.57    sK1 = k2_pre_topc(sK0,sK1) | ~r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | ~spl2_8),
% 0.21/0.57    inference(resolution,[],[f131,f47])).
% 0.21/0.57  fof(f47,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f39])).
% 0.21/0.57  fof(f39,plain,(
% 0.21/0.57    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.57    inference(flattening,[],[f38])).
% 0.21/0.57  fof(f38,plain,(
% 0.21/0.57    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.57    inference(nnf_transformation,[],[f1])).
% 0.21/0.57  fof(f1,axiom,(
% 0.21/0.57    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.57  fof(f131,plain,(
% 0.21/0.57    r1_tarski(k2_pre_topc(sK0,sK1),sK1) | ~spl2_8),
% 0.21/0.57    inference(avatar_component_clause,[],[f130])).
% 0.21/0.57  fof(f257,plain,(
% 0.21/0.57    spl2_8 | ~spl2_1 | ~spl2_3 | ~spl2_4),
% 0.21/0.57    inference(avatar_split_clause,[],[f256,f81,f76,f66,f130])).
% 0.21/0.57  fof(f66,plain,(
% 0.21/0.57    spl2_1 <=> v4_pre_topc(sK1,sK0)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.57  fof(f256,plain,(
% 0.21/0.57    ~v4_pre_topc(sK1,sK0) | r1_tarski(k2_pre_topc(sK0,sK1),sK1) | (~spl2_3 | ~spl2_4)),
% 0.21/0.57    inference(subsumption_resolution,[],[f162,f63])).
% 0.21/0.57  fof(f63,plain,(
% 0.21/0.57    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.57    inference(equality_resolution,[],[f46])).
% 0.21/0.57  fof(f46,plain,(
% 0.21/0.57    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.57    inference(cnf_transformation,[],[f39])).
% 0.21/0.57  fof(f162,plain,(
% 0.21/0.57    ~v4_pre_topc(sK1,sK0) | r1_tarski(k2_pre_topc(sK0,sK1),sK1) | ~r1_tarski(sK1,sK1) | (~spl2_3 | ~spl2_4)),
% 0.21/0.57    inference(resolution,[],[f161,f78])).
% 0.21/0.57  fof(f161,plain,(
% 0.21/0.57    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(X0,sK0) | r1_tarski(k2_pre_topc(sK0,sK1),X0) | ~r1_tarski(sK1,X0)) ) | (~spl2_3 | ~spl2_4)),
% 0.21/0.57    inference(subsumption_resolution,[],[f158,f83])).
% 0.21/0.57  fof(f158,plain,(
% 0.21/0.57    ( ! [X0] : (~r1_tarski(sK1,X0) | ~v4_pre_topc(X0,sK0) | r1_tarski(k2_pre_topc(sK0,sK1),X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) ) | ~spl2_3),
% 0.21/0.57    inference(resolution,[],[f56,f78])).
% 0.21/0.57  fof(f56,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X2,X1) | ~v4_pre_topc(X1,X0) | r1_tarski(k2_pre_topc(X0,X2),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f29])).
% 0.21/0.57  fof(f29,plain,(
% 0.21/0.57    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k2_pre_topc(X0,X2),X1) | ~r1_tarski(X2,X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.57    inference(flattening,[],[f28])).
% 0.21/0.57  fof(f28,plain,(
% 0.21/0.57    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k2_pre_topc(X0,X2),X1) | (~r1_tarski(X2,X1) | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.57    inference(ennf_transformation,[],[f15])).
% 0.21/0.57  fof(f15,axiom,(
% 0.21/0.57    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X2,X1) & v4_pre_topc(X1,X0)) => r1_tarski(k2_pre_topc(X0,X2),X1)))))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_tops_1)).
% 0.21/0.57  fof(f255,plain,(
% 0.21/0.57    sK1 != k2_pre_topc(sK0,sK1) | v4_pre_topc(sK1,sK0) | ~v4_pre_topc(k2_pre_topc(sK0,sK1),sK0)),
% 0.21/0.57    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.57  fof(f248,plain,(
% 0.21/0.57    spl2_9 | ~spl2_3 | ~spl2_4 | ~spl2_14),
% 0.21/0.57    inference(avatar_split_clause,[],[f247,f224,f81,f76,f134])).
% 0.21/0.57  fof(f224,plain,(
% 0.21/0.57    spl2_14 <=> sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.21/0.57  fof(f247,plain,(
% 0.21/0.57    sK1 = k2_pre_topc(sK0,sK1) | (~spl2_3 | ~spl2_4 | ~spl2_14)),
% 0.21/0.57    inference(subsumption_resolution,[],[f246,f83])).
% 0.21/0.57  fof(f246,plain,(
% 0.21/0.57    sK1 = k2_pre_topc(sK0,sK1) | ~l1_pre_topc(sK0) | (~spl2_3 | ~spl2_14)),
% 0.21/0.57    inference(subsumption_resolution,[],[f240,f78])).
% 0.21/0.57  fof(f240,plain,(
% 0.21/0.57    sK1 = k2_pre_topc(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl2_14),
% 0.21/0.57    inference(superposition,[],[f154,f226])).
% 0.21/0.57  fof(f226,plain,(
% 0.21/0.57    sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl2_14),
% 0.21/0.57    inference(avatar_component_clause,[],[f224])).
% 0.21/0.57  fof(f154,plain,(
% 0.21/0.57    ( ! [X2,X3] : (k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2)) )),
% 0.21/0.57    inference(subsumption_resolution,[],[f153,f53])).
% 0.21/0.57  fof(f53,plain,(
% 0.21/0.57    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f24])).
% 0.21/0.57  fof(f24,plain,(
% 0.21/0.57    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.57    inference(flattening,[],[f23])).
% 0.21/0.57  fof(f23,plain,(
% 0.21/0.57    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.21/0.57    inference(ennf_transformation,[],[f12])).
% 0.21/0.57  fof(f12,axiom,(
% 0.21/0.57    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 0.21/0.57  fof(f153,plain,(
% 0.21/0.57    ( ! [X2,X3] : (k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2) | ~m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))) )),
% 0.21/0.57    inference(duplicate_literal_removal,[],[f150])).
% 0.21/0.57  fof(f150,plain,(
% 0.21/0.57    ( ! [X2,X3] : (k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2) | ~m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) )),
% 0.21/0.57    inference(superposition,[],[f54,f57])).
% 0.21/0.57  fof(f57,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f31])).
% 0.21/0.57  fof(f31,plain,(
% 0.21/0.57    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.57    inference(flattening,[],[f30])).
% 0.21/0.57  fof(f30,plain,(
% 0.21/0.57    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.21/0.57    inference(ennf_transformation,[],[f8])).
% 0.21/0.57  fof(f8,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 0.21/0.57  fof(f54,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f25])).
% 0.21/0.57  fof(f25,plain,(
% 0.21/0.57    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.57    inference(ennf_transformation,[],[f16])).
% 0.21/0.57  fof(f16,axiom,(
% 0.21/0.57    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).
% 0.21/0.57  fof(f235,plain,(
% 0.21/0.57    spl2_14 | ~spl2_13),
% 0.21/0.57    inference(avatar_split_clause,[],[f222,f212,f224])).
% 0.21/0.57  fof(f212,plain,(
% 0.21/0.57    spl2_13 <=> sK1 = k2_xboole_0(k2_tops_1(sK0,sK1),sK1)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.21/0.57  fof(f222,plain,(
% 0.21/0.57    sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl2_13),
% 0.21/0.57    inference(superposition,[],[f96,f214])).
% 0.21/0.57  fof(f214,plain,(
% 0.21/0.57    sK1 = k2_xboole_0(k2_tops_1(sK0,sK1),sK1) | ~spl2_13),
% 0.21/0.57    inference(avatar_component_clause,[],[f212])).
% 0.21/0.57  fof(f96,plain,(
% 0.21/0.57    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2)) )),
% 0.21/0.57    inference(superposition,[],[f90,f60])).
% 0.21/0.57  fof(f60,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f7])).
% 0.21/0.57  fof(f7,axiom,(
% 0.21/0.57    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.21/0.57  fof(f90,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X1,X0))) )),
% 0.21/0.57    inference(superposition,[],[f60,f50])).
% 0.21/0.57  fof(f50,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f6])).
% 0.21/0.57  fof(f6,axiom,(
% 0.21/0.57    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.21/0.57  fof(f215,plain,(
% 0.21/0.57    spl2_13 | ~spl2_11),
% 0.21/0.57    inference(avatar_split_clause,[],[f205,f193,f212])).
% 0.21/0.57  fof(f193,plain,(
% 0.21/0.57    spl2_11 <=> sK1 = k2_xboole_0(k2_tops_1(sK0,sK1),k3_xboole_0(sK1,k3_xboole_0(sK1,k1_tops_1(sK0,sK1))))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.21/0.57  fof(f205,plain,(
% 0.21/0.57    sK1 = k2_xboole_0(k2_tops_1(sK0,sK1),sK1) | ~spl2_11),
% 0.21/0.57    inference(superposition,[],[f48,f195])).
% 0.21/0.57  fof(f195,plain,(
% 0.21/0.57    sK1 = k2_xboole_0(k2_tops_1(sK0,sK1),k3_xboole_0(sK1,k3_xboole_0(sK1,k1_tops_1(sK0,sK1)))) | ~spl2_11),
% 0.21/0.57    inference(avatar_component_clause,[],[f193])).
% 0.21/0.57  fof(f48,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f4])).
% 0.21/0.57  fof(f4,axiom,(
% 0.21/0.57    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_1)).
% 0.21/0.57  fof(f201,plain,(
% 0.21/0.57    spl2_11 | ~spl2_6),
% 0.21/0.57    inference(avatar_split_clause,[],[f200,f115,f193])).
% 0.21/0.57  fof(f115,plain,(
% 0.21/0.57    spl2_6 <=> k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.57  fof(f200,plain,(
% 0.21/0.57    sK1 = k2_xboole_0(k2_tops_1(sK0,sK1),k3_xboole_0(sK1,k3_xboole_0(sK1,k1_tops_1(sK0,sK1)))) | ~spl2_6),
% 0.21/0.57    inference(superposition,[],[f110,f117])).
% 0.21/0.57  fof(f117,plain,(
% 0.21/0.57    k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | ~spl2_6),
% 0.21/0.57    inference(avatar_component_clause,[],[f115])).
% 0.21/0.57  fof(f110,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X0,X1))) = X0) )),
% 0.21/0.57    inference(forward_demodulation,[],[f104,f49])).
% 0.21/0.57  fof(f49,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 0.21/0.57    inference(cnf_transformation,[],[f3])).
% 0.21/0.57  fof(f3,axiom,(
% 0.21/0.57    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).
% 0.21/0.57  fof(f104,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 0.21/0.57    inference(superposition,[],[f59,f61])).
% 0.21/0.57  fof(f61,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f2])).
% 0.21/0.57  fof(f2,axiom,(
% 0.21/0.57    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.57  fof(f59,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f5])).
% 0.21/0.57  fof(f5,axiom,(
% 0.21/0.57    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_xboole_1)).
% 0.21/0.57  fof(f149,plain,(
% 0.21/0.57    spl2_10 | ~spl2_3 | ~spl2_4 | ~spl2_5),
% 0.21/0.57    inference(avatar_split_clause,[],[f144,f86,f81,f76,f146])).
% 0.21/0.57  fof(f146,plain,(
% 0.21/0.57    spl2_10 <=> v4_pre_topc(k2_pre_topc(sK0,sK1),sK0)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.21/0.57  fof(f86,plain,(
% 0.21/0.57    spl2_5 <=> v2_pre_topc(sK0)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.57  fof(f144,plain,(
% 0.21/0.57    v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) | (~spl2_3 | ~spl2_4 | ~spl2_5)),
% 0.21/0.57    inference(subsumption_resolution,[],[f143,f88])).
% 0.21/0.57  fof(f88,plain,(
% 0.21/0.57    v2_pre_topc(sK0) | ~spl2_5),
% 0.21/0.57    inference(avatar_component_clause,[],[f86])).
% 0.21/0.57  fof(f143,plain,(
% 0.21/0.57    v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) | ~v2_pre_topc(sK0) | (~spl2_3 | ~spl2_4)),
% 0.21/0.57    inference(subsumption_resolution,[],[f140,f83])).
% 0.21/0.57  fof(f140,plain,(
% 0.21/0.57    v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~spl2_3),
% 0.21/0.57    inference(resolution,[],[f55,f78])).
% 0.21/0.57  fof(f55,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f27])).
% 0.21/0.57  fof(f27,plain,(
% 0.21/0.57    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.57    inference(flattening,[],[f26])).
% 0.21/0.57  fof(f26,plain,(
% 0.21/0.57    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.57    inference(ennf_transformation,[],[f13])).
% 0.21/0.57  fof(f13,axiom,(
% 0.21/0.57    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_pre_topc(X0,X1),X0))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_tops_1)).
% 0.21/0.57  fof(f127,plain,(
% 0.21/0.57    spl2_7 | ~spl2_3 | ~spl2_4),
% 0.21/0.57    inference(avatar_split_clause,[],[f122,f81,f76,f124])).
% 0.21/0.57  fof(f122,plain,(
% 0.21/0.57    r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | (~spl2_3 | ~spl2_4)),
% 0.21/0.57    inference(subsumption_resolution,[],[f121,f83])).
% 0.21/0.57  fof(f121,plain,(
% 0.21/0.57    r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | ~l1_pre_topc(sK0) | ~spl2_3),
% 0.21/0.57    inference(resolution,[],[f58,f78])).
% 0.21/0.57  fof(f58,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(X1,k2_pre_topc(X0,X1)) | ~l1_pre_topc(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f32])).
% 0.21/0.57  fof(f32,plain,(
% 0.21/0.57    ! [X0] : (! [X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.57    inference(ennf_transformation,[],[f11])).
% 0.21/0.57  fof(f11,axiom,(
% 0.21/0.57    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(X1,k2_pre_topc(X0,X1))))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).
% 0.21/0.57  fof(f120,plain,(
% 0.21/0.57    spl2_6 | ~spl2_2 | ~spl2_3),
% 0.21/0.57    inference(avatar_split_clause,[],[f119,f76,f70,f115])).
% 0.21/0.57  fof(f119,plain,(
% 0.21/0.57    k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | (~spl2_2 | ~spl2_3)),
% 0.21/0.57    inference(subsumption_resolution,[],[f112,f78])).
% 0.21/0.57  fof(f112,plain,(
% 0.21/0.57    k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_2),
% 0.21/0.57    inference(superposition,[],[f71,f51])).
% 0.21/0.57  fof(f51,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f21])).
% 0.21/0.57  fof(f21,plain,(
% 0.21/0.57    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.57    inference(ennf_transformation,[],[f9])).
% 0.21/0.57  fof(f9,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 0.21/0.57  fof(f71,plain,(
% 0.21/0.57    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~spl2_2),
% 0.21/0.57    inference(avatar_component_clause,[],[f70])).
% 0.21/0.57  fof(f89,plain,(
% 0.21/0.57    spl2_5),
% 0.21/0.57    inference(avatar_split_clause,[],[f40,f86])).
% 0.21/0.57  fof(f40,plain,(
% 0.21/0.57    v2_pre_topc(sK0)),
% 0.21/0.57    inference(cnf_transformation,[],[f37])).
% 0.21/0.57  fof(f37,plain,(
% 0.21/0.57    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.21/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f34,f36,f35])).
% 0.21/0.57  fof(f35,plain,(
% 0.21/0.57    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f36,plain,(
% 0.21/0.57    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f34,plain,(
% 0.21/0.57    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.57    inference(flattening,[],[f33])).
% 0.21/0.57  fof(f33,plain,(
% 0.21/0.57    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.57    inference(nnf_transformation,[],[f20])).
% 0.21/0.57  fof(f20,plain,(
% 0.21/0.57    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.57    inference(flattening,[],[f19])).
% 0.21/0.57  fof(f19,plain,(
% 0.21/0.57    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.21/0.57    inference(ennf_transformation,[],[f18])).
% 0.21/0.57  fof(f18,negated_conjecture,(
% 0.21/0.57    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 0.21/0.57    inference(negated_conjecture,[],[f17])).
% 0.21/0.57  fof(f17,conjecture,(
% 0.21/0.57    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).
% 0.21/0.57  fof(f84,plain,(
% 0.21/0.57    spl2_4),
% 0.21/0.57    inference(avatar_split_clause,[],[f41,f81])).
% 0.21/0.57  fof(f41,plain,(
% 0.21/0.57    l1_pre_topc(sK0)),
% 0.21/0.57    inference(cnf_transformation,[],[f37])).
% 0.21/0.57  fof(f79,plain,(
% 0.21/0.57    spl2_3),
% 0.21/0.57    inference(avatar_split_clause,[],[f42,f76])).
% 0.21/0.57  fof(f42,plain,(
% 0.21/0.57    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.57    inference(cnf_transformation,[],[f37])).
% 0.21/0.57  fof(f74,plain,(
% 0.21/0.57    spl2_1 | spl2_2),
% 0.21/0.57    inference(avatar_split_clause,[],[f43,f70,f66])).
% 0.21/0.57  fof(f43,plain,(
% 0.21/0.57    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)),
% 0.21/0.57    inference(cnf_transformation,[],[f37])).
% 0.21/0.57  fof(f73,plain,(
% 0.21/0.57    ~spl2_1 | ~spl2_2),
% 0.21/0.57    inference(avatar_split_clause,[],[f44,f70,f66])).
% 0.21/0.57  fof(f44,plain,(
% 0.21/0.57    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)),
% 0.21/0.57    inference(cnf_transformation,[],[f37])).
% 0.21/0.57  % SZS output end Proof for theBenchmark
% 0.21/0.57  % (21462)------------------------------
% 0.21/0.57  % (21462)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (21462)Termination reason: Refutation
% 0.21/0.57  
% 0.21/0.57  % (21462)Memory used [KB]: 6396
% 0.21/0.57  % (21462)Time elapsed: 0.147 s
% 0.21/0.57  % (21462)------------------------------
% 0.21/0.57  % (21462)------------------------------
% 0.21/0.57  % (21440)Success in time 0.208 s
%------------------------------------------------------------------------------
