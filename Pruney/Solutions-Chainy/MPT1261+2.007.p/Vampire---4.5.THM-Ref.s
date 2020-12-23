%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:48 EST 2020

% Result     : Theorem 2.91s
% Output     : Refutation 2.91s
% Verified   : 
% Statistics : Number of formulae       :  177 ( 308 expanded)
%              Number of leaves         :   40 ( 118 expanded)
%              Depth                    :   11
%              Number of atoms          :  496 ( 951 expanded)
%              Number of equality atoms :  112 ( 231 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2503,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f117,f118,f123,f128,f133,f251,f282,f391,f554,f560,f732,f864,f2042,f2064,f2069,f2083,f2201,f2211,f2495,f2501])).

fof(f2501,plain,
    ( spl2_17
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_72 ),
    inference(avatar_split_clause,[],[f2500,f2039,f125,f120,f360])).

fof(f360,plain,
    ( spl2_17
  <=> sK1 = k2_pre_topc(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f120,plain,
    ( spl2_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f125,plain,
    ( spl2_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f2039,plain,
    ( spl2_72
  <=> sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_72])])).

fof(f2500,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_72 ),
    inference(subsumption_resolution,[],[f2499,f127])).

fof(f127,plain,
    ( l1_pre_topc(sK0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f125])).

fof(f2499,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl2_3
    | ~ spl2_72 ),
    inference(subsumption_resolution,[],[f2329,f122])).

fof(f122,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f120])).

fof(f2329,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_72 ),
    inference(superposition,[],[f2041,f336])).

fof(f336,plain,(
    ! [X2,X3] :
      ( k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2) ) ),
    inference(subsumption_resolution,[],[f333,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f333,plain,(
    ! [X2,X3] :
      ( k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) ) ),
    inference(duplicate_literal_removal,[],[f330])).

fof(f330,plain,(
    ! [X2,X3] :
      ( k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ) ),
    inference(superposition,[],[f83,f102])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f83,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

fof(f2041,plain,
    ( sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_72 ),
    inference(avatar_component_clause,[],[f2039])).

fof(f2495,plain,
    ( ~ spl2_3
    | ~ spl2_4
    | spl2_49 ),
    inference(avatar_contradiction_clause,[],[f2494])).

fof(f2494,plain,
    ( $false
    | ~ spl2_3
    | ~ spl2_4
    | spl2_49 ),
    inference(subsumption_resolution,[],[f2493,f127])).

fof(f2493,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl2_3
    | spl2_49 ),
    inference(subsumption_resolution,[],[f2491,f122])).

fof(f2491,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl2_49 ),
    inference(trivial_inequality_removal,[],[f2488])).

fof(f2488,plain,
    ( k1_tops_1(sK0,sK1) != k1_tops_1(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl2_49 ),
    inference(superposition,[],[f1161,f323])).

fof(f323,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f322])).

fof(f322,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(superposition,[],[f78,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f1161,plain,
    ( k1_tops_1(sK0,sK1) != k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | spl2_49 ),
    inference(avatar_component_clause,[],[f1160])).

fof(f1160,plain,
    ( spl2_49
  <=> k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_49])])).

fof(f2211,plain,
    ( ~ spl2_14
    | spl2_16 ),
    inference(avatar_contradiction_clause,[],[f2210])).

fof(f2210,plain,
    ( $false
    | ~ spl2_14
    | spl2_16 ),
    inference(subsumption_resolution,[],[f2208,f279])).

fof(f279,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f277])).

fof(f277,plain,
    ( spl2_14
  <=> r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f2208,plain,
    ( ~ r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | spl2_16 ),
    inference(resolution,[],[f354,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f354,plain,
    ( ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | spl2_16 ),
    inference(avatar_component_clause,[],[f353])).

fof(f353,plain,
    ( spl2_16
  <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f2201,plain,
    ( ~ spl2_9
    | spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f2200,f120,f114,f222])).

fof(f222,plain,
    ( spl2_9
  <=> k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f114,plain,
    ( spl2_2
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f2200,plain,
    ( k2_tops_1(sK0,sK1) != k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | spl2_2
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f2199,f122])).

fof(f2199,plain,
    ( k2_tops_1(sK0,sK1) != k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_2 ),
    inference(superposition,[],[f116,f78])).

fof(f116,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f114])).

fof(f2083,plain,
    ( ~ spl2_16
    | spl2_50
    | ~ spl2_49 ),
    inference(avatar_split_clause,[],[f1771,f1160,f1166,f353])).

fof(f1166,plain,
    ( spl2_50
  <=> k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_50])])).

fof(f1771,plain,
    ( k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k1_tops_1(sK0,sK1))
    | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ spl2_49 ),
    inference(superposition,[],[f215,f1162])).

fof(f1162,plain,
    ( k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_49 ),
    inference(avatar_component_clause,[],[f1160])).

fof(f215,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f211])).

fof(f211,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f75,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f75,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f2069,plain,
    ( ~ spl2_16
    | spl2_52
    | ~ spl2_29 ),
    inference(avatar_split_clause,[],[f1157,f729,f1182,f353])).

fof(f1182,plain,
    ( spl2_52
  <=> sK1 = k2_xboole_0(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_52])])).

fof(f729,plain,
    ( spl2_29
  <=> k1_tops_1(sK0,sK1) = k3_subset_1(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).

fof(f1157,plain,
    ( sK1 = k2_xboole_0(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ spl2_29 ),
    inference(superposition,[],[f304,f731])).

fof(f731,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_29 ),
    inference(avatar_component_clause,[],[f729])).

fof(f304,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X1,k3_subset_1(X0,X1)) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(subsumption_resolution,[],[f303,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f303,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X1,k3_subset_1(X0,X1)) = X0
      | ~ m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f300])).

fof(f300,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X1,k3_subset_1(X0,X1)) = X0
      | ~ m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f102,f252])).

fof(f252,plain,(
    ! [X0,X1] :
      ( k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(forward_demodulation,[],[f97,f105])).

fof(f105,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f97,plain,(
    ! [X0,X1] :
      ( k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).

fof(f2064,plain,
    ( spl2_9
    | ~ spl2_28
    | ~ spl2_50 ),
    inference(avatar_split_clause,[],[f2063,f1166,f725,f222])).

fof(f725,plain,
    ( spl2_28
  <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).

fof(f2063,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_28
    | ~ spl2_50 ),
    inference(subsumption_resolution,[],[f1983,f726])).

fof(f726,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ spl2_28 ),
    inference(avatar_component_clause,[],[f725])).

fof(f1983,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ spl2_50 ),
    inference(superposition,[],[f1168,f76])).

fof(f1168,plain,
    ( k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_50 ),
    inference(avatar_component_clause,[],[f1166])).

fof(f2042,plain,
    ( spl2_72
    | ~ spl2_52 ),
    inference(avatar_split_clause,[],[f2025,f1182,f2039])).

fof(f2025,plain,
    ( sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_52 ),
    inference(superposition,[],[f1289,f1184])).

fof(f1184,plain,
    ( sK1 = k2_xboole_0(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl2_52 ),
    inference(avatar_component_clause,[],[f1182])).

fof(f1289,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k2_xboole_0(X0,X1),X0) ),
    inference(backward_demodulation,[],[f184,f642])).

fof(f642,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(subsumption_resolution,[],[f630,f96])).

fof(f96,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f630,plain,(
    ! [X0] :
      ( k5_xboole_0(X0,k1_xboole_0) = X0
      | ~ r1_tarski(k1_xboole_0,X0) ) ),
    inference(superposition,[],[f185,f103])).

fof(f103,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f185,plain,(
    ! [X2,X3] :
      ( k2_xboole_0(X3,X2) = k5_xboole_0(X3,k1_xboole_0)
      | ~ r1_tarski(X2,X3) ) ),
    inference(superposition,[],[f99,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f99,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f184,plain,(
    ! [X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X0) = k5_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[],[f99,f101])).

fof(f101,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f864,plain,
    ( ~ spl2_12
    | spl2_28 ),
    inference(avatar_contradiction_clause,[],[f863])).

fof(f863,plain,
    ( $false
    | ~ spl2_12
    | spl2_28 ),
    inference(subsumption_resolution,[],[f861,f250])).

fof(f250,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f248])).

fof(f248,plain,
    ( spl2_12
  <=> r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f861,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | spl2_28 ),
    inference(resolution,[],[f727,f87])).

fof(f727,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | spl2_28 ),
    inference(avatar_component_clause,[],[f725])).

fof(f732,plain,
    ( ~ spl2_28
    | spl2_29
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f716,f222,f729,f725])).

fof(f716,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(sK1,k2_tops_1(sK0,sK1))
    | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ spl2_9 ),
    inference(superposition,[],[f215,f224])).

fof(f224,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f222])).

fof(f560,plain,
    ( spl2_9
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f559,f120,f114,f222])).

fof(f559,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f556,f122])).

fof(f556,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_2 ),
    inference(superposition,[],[f78,f115])).

fof(f115,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f114])).

fof(f554,plain,
    ( spl2_1
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_17 ),
    inference(avatar_split_clause,[],[f553,f360,f130,f125,f120,f110])).

fof(f110,plain,
    ( spl2_1
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f130,plain,
    ( spl2_5
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f553,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_17 ),
    inference(subsumption_resolution,[],[f552,f127])).

fof(f552,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_17 ),
    inference(subsumption_resolution,[],[f551,f122])).

fof(f551,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_5
    | ~ spl2_17 ),
    inference(subsumption_resolution,[],[f422,f132])).

fof(f132,plain,
    ( v2_pre_topc(sK0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f130])).

fof(f422,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ v2_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_17 ),
    inference(trivial_inequality_removal,[],[f421])).

fof(f421,plain,
    ( sK1 != sK1
    | v4_pre_topc(sK1,sK0)
    | ~ v2_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_17 ),
    inference(superposition,[],[f85,f362])).

fof(f362,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f360])).

fof(f85,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) != X1
      | v4_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
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

fof(f391,plain,
    ( spl2_16
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f386,f222,f353])).

fof(f386,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ spl2_9 ),
    inference(superposition,[],[f142,f224])).

fof(f142,plain,(
    ! [X0,X1] : m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0)) ),
    inference(backward_demodulation,[],[f106,f100])).

fof(f100,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f106,plain,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).

fof(f282,plain,
    ( spl2_14
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f281,f125,f120,f110,f277])).

fof(f281,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f272,f127])).

fof(f272,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl2_3 ),
    inference(resolution,[],[f82,f122])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | r1_tarski(k2_tops_1(X0,X1),X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => r1_tarski(k2_tops_1(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).

fof(f251,plain,
    ( spl2_12
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f246,f125,f120,f248])).

fof(f246,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f245,f127])).

fof(f245,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl2_3 ),
    inference(resolution,[],[f80,f122])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

fof(f133,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f67,f130])).

fof(f67,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | ~ v4_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f59,f61,f60])).

fof(f60,plain,
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

fof(f61,plain,
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

fof(f59,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f33])).

fof(f33,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

fof(f128,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f68,f125])).

fof(f68,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f62])).

fof(f123,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f69,f120])).

fof(f69,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f62])).

fof(f118,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f70,f114,f110])).

fof(f70,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f62])).

fof(f117,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f71,f114,f110])).

fof(f71,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f62])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:14:54 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.37  ipcrm: permission denied for id (821264387)
% 0.13/0.37  ipcrm: permission denied for id (821329926)
% 0.13/0.37  ipcrm: permission denied for id (821395464)
% 0.13/0.37  ipcrm: permission denied for id (821461001)
% 0.13/0.38  ipcrm: permission denied for id (821493770)
% 0.13/0.38  ipcrm: permission denied for id (821559309)
% 0.13/0.38  ipcrm: permission denied for id (821592078)
% 0.13/0.38  ipcrm: permission denied for id (821624847)
% 0.13/0.38  ipcrm: permission denied for id (821657616)
% 0.13/0.38  ipcrm: permission denied for id (821690385)
% 0.13/0.39  ipcrm: permission denied for id (821723154)
% 0.13/0.39  ipcrm: permission denied for id (821755924)
% 0.13/0.39  ipcrm: permission denied for id (821788693)
% 0.21/0.40  ipcrm: permission denied for id (821985308)
% 0.21/0.40  ipcrm: permission denied for id (822050847)
% 0.21/0.40  ipcrm: permission denied for id (822083616)
% 0.21/0.41  ipcrm: permission denied for id (822181924)
% 0.21/0.41  ipcrm: permission denied for id (822214693)
% 0.21/0.41  ipcrm: permission denied for id (822280231)
% 0.21/0.41  ipcrm: permission denied for id (822345769)
% 0.21/0.42  ipcrm: permission denied for id (822411307)
% 0.21/0.42  ipcrm: permission denied for id (822476845)
% 0.21/0.42  ipcrm: permission denied for id (822575152)
% 0.21/0.42  ipcrm: permission denied for id (822673458)
% 0.21/0.43  ipcrm: permission denied for id (822771765)
% 0.21/0.43  ipcrm: permission denied for id (822804534)
% 0.21/0.43  ipcrm: permission denied for id (822870072)
% 0.21/0.44  ipcrm: permission denied for id (822968381)
% 0.21/0.44  ipcrm: permission denied for id (823033919)
% 0.21/0.44  ipcrm: permission denied for id (823099458)
% 0.21/0.44  ipcrm: permission denied for id (823132227)
% 0.21/0.45  ipcrm: permission denied for id (823164996)
% 0.21/0.45  ipcrm: permission denied for id (823230534)
% 0.21/0.45  ipcrm: permission denied for id (823263303)
% 0.21/0.45  ipcrm: permission denied for id (823394379)
% 0.21/0.46  ipcrm: permission denied for id (823623761)
% 0.21/0.46  ipcrm: permission denied for id (823656530)
% 0.21/0.46  ipcrm: permission denied for id (823689299)
% 0.21/0.46  ipcrm: permission denied for id (823722068)
% 0.21/0.47  ipcrm: permission denied for id (823754837)
% 0.21/0.47  ipcrm: permission denied for id (823820375)
% 0.21/0.47  ipcrm: permission denied for id (823853145)
% 0.21/0.47  ipcrm: permission denied for id (823885914)
% 0.21/0.47  ipcrm: permission denied for id (823918683)
% 0.21/0.47  ipcrm: permission denied for id (823951452)
% 0.21/0.47  ipcrm: permission denied for id (823984221)
% 0.21/0.48  ipcrm: permission denied for id (824082528)
% 0.21/0.48  ipcrm: permission denied for id (824115297)
% 0.21/0.48  ipcrm: permission denied for id (824148066)
% 0.21/0.48  ipcrm: permission denied for id (824213604)
% 0.21/0.49  ipcrm: permission denied for id (824279142)
% 0.21/0.49  ipcrm: permission denied for id (824311911)
% 0.21/0.49  ipcrm: permission denied for id (824410218)
% 0.21/0.49  ipcrm: permission denied for id (824442987)
% 0.21/0.50  ipcrm: permission denied for id (824541295)
% 0.21/0.50  ipcrm: permission denied for id (824639602)
% 0.21/0.50  ipcrm: permission denied for id (824737908)
% 0.21/0.51  ipcrm: permission denied for id (824868985)
% 0.21/0.51  ipcrm: permission denied for id (824901754)
% 0.21/0.51  ipcrm: permission denied for id (824934523)
% 0.21/0.51  ipcrm: permission denied for id (824967292)
% 0.21/0.52  ipcrm: permission denied for id (825065599)
% 1.00/0.64  % (23013)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.00/0.65  % (23005)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.00/0.65  % (22998)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.00/0.65  % (22997)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.00/0.67  % (22989)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.00/0.67  % (22991)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.00/0.68  % (23003)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.00/0.68  % (22996)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.00/0.69  % (22994)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.00/0.69  % (23004)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.00/0.69  % (23007)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.00/0.69  % (22988)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.00/0.69  % (23012)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.00/0.70  % (23015)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.00/0.70  % (23000)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.00/0.70  % (23010)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.00/0.70  % (23011)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.00/0.70  % (22990)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.00/0.70  % (22987)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.00/0.70  % (22999)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.00/0.70  % (23002)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.00/0.71  % (23014)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.00/0.71  % (22993)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.00/0.71  % (23008)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.00/0.71  % (23016)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.00/0.71  % (23006)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.00/0.72  % (23001)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.70/0.72  % (22995)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.70/0.72  % (23009)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.70/0.72  % (22992)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 2.91/0.89  % (23008)Refutation found. Thanks to Tanya!
% 2.91/0.89  % SZS status Theorem for theBenchmark
% 2.91/0.90  % SZS output start Proof for theBenchmark
% 2.91/0.90  fof(f2503,plain,(
% 2.91/0.90    $false),
% 2.91/0.90    inference(avatar_sat_refutation,[],[f117,f118,f123,f128,f133,f251,f282,f391,f554,f560,f732,f864,f2042,f2064,f2069,f2083,f2201,f2211,f2495,f2501])).
% 2.91/0.90  fof(f2501,plain,(
% 2.91/0.90    spl2_17 | ~spl2_3 | ~spl2_4 | ~spl2_72),
% 2.91/0.90    inference(avatar_split_clause,[],[f2500,f2039,f125,f120,f360])).
% 2.91/0.90  fof(f360,plain,(
% 2.91/0.90    spl2_17 <=> sK1 = k2_pre_topc(sK0,sK1)),
% 2.91/0.90    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 2.91/0.90  fof(f120,plain,(
% 2.91/0.90    spl2_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.91/0.90    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 2.91/0.90  fof(f125,plain,(
% 2.91/0.90    spl2_4 <=> l1_pre_topc(sK0)),
% 2.91/0.90    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 2.91/0.90  fof(f2039,plain,(
% 2.91/0.90    spl2_72 <=> sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 2.91/0.90    introduced(avatar_definition,[new_symbols(naming,[spl2_72])])).
% 2.91/0.90  fof(f2500,plain,(
% 2.91/0.90    sK1 = k2_pre_topc(sK0,sK1) | (~spl2_3 | ~spl2_4 | ~spl2_72)),
% 2.91/0.90    inference(subsumption_resolution,[],[f2499,f127])).
% 2.91/0.90  fof(f127,plain,(
% 2.91/0.90    l1_pre_topc(sK0) | ~spl2_4),
% 2.91/0.90    inference(avatar_component_clause,[],[f125])).
% 2.91/0.90  fof(f2499,plain,(
% 2.91/0.90    sK1 = k2_pre_topc(sK0,sK1) | ~l1_pre_topc(sK0) | (~spl2_3 | ~spl2_72)),
% 2.91/0.90    inference(subsumption_resolution,[],[f2329,f122])).
% 2.91/0.90  fof(f122,plain,(
% 2.91/0.90    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_3),
% 2.91/0.90    inference(avatar_component_clause,[],[f120])).
% 2.91/0.90  fof(f2329,plain,(
% 2.91/0.90    sK1 = k2_pre_topc(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl2_72),
% 2.91/0.90    inference(superposition,[],[f2041,f336])).
% 2.91/0.90  fof(f336,plain,(
% 2.91/0.90    ( ! [X2,X3] : (k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2)) )),
% 2.91/0.90    inference(subsumption_resolution,[],[f333,f81])).
% 2.91/0.90  fof(f81,plain,(
% 2.91/0.90    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.91/0.90    inference(cnf_transformation,[],[f44])).
% 2.91/0.90  fof(f44,plain,(
% 2.91/0.90    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 2.91/0.90    inference(flattening,[],[f43])).
% 2.91/0.90  fof(f43,plain,(
% 2.91/0.90    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 2.91/0.90    inference(ennf_transformation,[],[f27])).
% 2.91/0.90  fof(f27,axiom,(
% 2.91/0.90    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.91/0.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 2.91/0.90  fof(f333,plain,(
% 2.91/0.90    ( ! [X2,X3] : (k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2) | ~m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))) )),
% 2.91/0.90    inference(duplicate_literal_removal,[],[f330])).
% 2.91/0.90  fof(f330,plain,(
% 2.91/0.90    ( ! [X2,X3] : (k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2) | ~m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) )),
% 2.91/0.90    inference(superposition,[],[f83,f102])).
% 2.91/0.90  fof(f102,plain,(
% 2.91/0.90    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.91/0.90    inference(cnf_transformation,[],[f57])).
% 2.91/0.90  fof(f57,plain,(
% 2.91/0.90    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.91/0.90    inference(flattening,[],[f56])).
% 2.91/0.90  fof(f56,plain,(
% 2.91/0.90    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 2.91/0.90    inference(ennf_transformation,[],[f20])).
% 2.91/0.90  fof(f20,axiom,(
% 2.91/0.90    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 2.91/0.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 2.91/0.90  fof(f83,plain,(
% 2.91/0.90    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.91/0.90    inference(cnf_transformation,[],[f47])).
% 2.91/0.90  fof(f47,plain,(
% 2.91/0.90    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.91/0.90    inference(ennf_transformation,[],[f30])).
% 2.91/0.90  fof(f30,axiom,(
% 2.91/0.90    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 2.91/0.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).
% 2.91/0.90  fof(f2041,plain,(
% 2.91/0.90    sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl2_72),
% 2.91/0.90    inference(avatar_component_clause,[],[f2039])).
% 2.91/0.90  fof(f2495,plain,(
% 2.91/0.90    ~spl2_3 | ~spl2_4 | spl2_49),
% 2.91/0.90    inference(avatar_contradiction_clause,[],[f2494])).
% 2.91/0.90  fof(f2494,plain,(
% 2.91/0.90    $false | (~spl2_3 | ~spl2_4 | spl2_49)),
% 2.91/0.90    inference(subsumption_resolution,[],[f2493,f127])).
% 2.91/0.90  fof(f2493,plain,(
% 2.91/0.90    ~l1_pre_topc(sK0) | (~spl2_3 | spl2_49)),
% 2.91/0.90    inference(subsumption_resolution,[],[f2491,f122])).
% 2.91/0.90  fof(f2491,plain,(
% 2.91/0.90    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl2_49),
% 2.91/0.90    inference(trivial_inequality_removal,[],[f2488])).
% 2.91/0.90  fof(f2488,plain,(
% 2.91/0.90    k1_tops_1(sK0,sK1) != k1_tops_1(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl2_49),
% 2.91/0.90    inference(superposition,[],[f1161,f323])).
% 2.91/0.90  fof(f323,plain,(
% 2.91/0.90    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.91/0.90    inference(duplicate_literal_removal,[],[f322])).
% 2.91/0.90  fof(f322,plain,(
% 2.91/0.90    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.91/0.90    inference(superposition,[],[f78,f79])).
% 2.91/0.90  fof(f79,plain,(
% 2.91/0.90    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.91/0.90    inference(cnf_transformation,[],[f41])).
% 2.91/0.90  fof(f41,plain,(
% 2.91/0.90    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.91/0.90    inference(ennf_transformation,[],[f32])).
% 2.91/0.90  fof(f32,axiom,(
% 2.91/0.90    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 2.91/0.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).
% 2.91/0.90  fof(f78,plain,(
% 2.91/0.90    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.91/0.90    inference(cnf_transformation,[],[f40])).
% 2.91/0.90  fof(f40,plain,(
% 2.91/0.90    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.91/0.90    inference(ennf_transformation,[],[f22])).
% 2.91/0.90  fof(f22,axiom,(
% 2.91/0.90    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 2.91/0.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 2.91/0.90  fof(f1161,plain,(
% 2.91/0.90    k1_tops_1(sK0,sK1) != k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | spl2_49),
% 2.91/0.90    inference(avatar_component_clause,[],[f1160])).
% 2.91/0.90  fof(f1160,plain,(
% 2.91/0.90    spl2_49 <=> k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 2.91/0.90    introduced(avatar_definition,[new_symbols(naming,[spl2_49])])).
% 2.91/0.90  fof(f2211,plain,(
% 2.91/0.90    ~spl2_14 | spl2_16),
% 2.91/0.90    inference(avatar_contradiction_clause,[],[f2210])).
% 2.91/0.90  fof(f2210,plain,(
% 2.91/0.90    $false | (~spl2_14 | spl2_16)),
% 2.91/0.90    inference(subsumption_resolution,[],[f2208,f279])).
% 2.91/0.90  fof(f279,plain,(
% 2.91/0.90    r1_tarski(k2_tops_1(sK0,sK1),sK1) | ~spl2_14),
% 2.91/0.90    inference(avatar_component_clause,[],[f277])).
% 2.91/0.90  fof(f277,plain,(
% 2.91/0.90    spl2_14 <=> r1_tarski(k2_tops_1(sK0,sK1),sK1)),
% 2.91/0.90    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 2.91/0.90  fof(f2208,plain,(
% 2.91/0.90    ~r1_tarski(k2_tops_1(sK0,sK1),sK1) | spl2_16),
% 2.91/0.90    inference(resolution,[],[f354,f87])).
% 2.91/0.90  fof(f87,plain,(
% 2.91/0.90    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.91/0.90    inference(cnf_transformation,[],[f65])).
% 2.91/0.90  fof(f65,plain,(
% 2.91/0.90    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.91/0.90    inference(nnf_transformation,[],[f25])).
% 2.91/0.90  fof(f25,axiom,(
% 2.91/0.90    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.91/0.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 2.91/0.90  fof(f354,plain,(
% 2.91/0.90    ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | spl2_16),
% 2.91/0.90    inference(avatar_component_clause,[],[f353])).
% 2.91/0.90  fof(f353,plain,(
% 2.91/0.90    spl2_16 <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1))),
% 2.91/0.90    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 2.91/0.90  fof(f2201,plain,(
% 2.91/0.90    ~spl2_9 | spl2_2 | ~spl2_3),
% 2.91/0.90    inference(avatar_split_clause,[],[f2200,f120,f114,f222])).
% 2.91/0.90  fof(f222,plain,(
% 2.91/0.90    spl2_9 <=> k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))),
% 2.91/0.90    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 2.91/0.90  fof(f114,plain,(
% 2.91/0.90    spl2_2 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),
% 2.91/0.90    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 2.91/0.90  fof(f2200,plain,(
% 2.91/0.90    k2_tops_1(sK0,sK1) != k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | (spl2_2 | ~spl2_3)),
% 2.91/0.90    inference(subsumption_resolution,[],[f2199,f122])).
% 2.91/0.90  fof(f2199,plain,(
% 2.91/0.90    k2_tops_1(sK0,sK1) != k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl2_2),
% 2.91/0.90    inference(superposition,[],[f116,f78])).
% 2.91/0.90  fof(f116,plain,(
% 2.91/0.90    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | spl2_2),
% 2.91/0.90    inference(avatar_component_clause,[],[f114])).
% 2.91/0.90  fof(f2083,plain,(
% 2.91/0.90    ~spl2_16 | spl2_50 | ~spl2_49),
% 2.91/0.90    inference(avatar_split_clause,[],[f1771,f1160,f1166,f353])).
% 2.91/0.90  fof(f1166,plain,(
% 2.91/0.90    spl2_50 <=> k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k1_tops_1(sK0,sK1))),
% 2.91/0.90    introduced(avatar_definition,[new_symbols(naming,[spl2_50])])).
% 2.91/0.90  fof(f1771,plain,(
% 2.91/0.90    k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k1_tops_1(sK0,sK1)) | ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | ~spl2_49),
% 2.91/0.90    inference(superposition,[],[f215,f1162])).
% 2.91/0.90  fof(f1162,plain,(
% 2.91/0.90    k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl2_49),
% 2.91/0.90    inference(avatar_component_clause,[],[f1160])).
% 2.91/0.90  fof(f215,plain,(
% 2.91/0.90    ( ! [X0,X1] : (k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.91/0.90    inference(duplicate_literal_removal,[],[f211])).
% 2.91/0.90  fof(f211,plain,(
% 2.91/0.90    ( ! [X0,X1] : (k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.91/0.90    inference(superposition,[],[f75,f76])).
% 2.91/0.90  fof(f76,plain,(
% 2.91/0.90    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.91/0.90    inference(cnf_transformation,[],[f38])).
% 2.91/0.90  fof(f38,plain,(
% 2.91/0.90    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.91/0.90    inference(ennf_transformation,[],[f16])).
% 2.91/0.90  fof(f16,axiom,(
% 2.91/0.90    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 2.91/0.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 2.91/0.90  fof(f75,plain,(
% 2.91/0.90    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.91/0.90    inference(cnf_transformation,[],[f37])).
% 2.91/0.90  fof(f37,plain,(
% 2.91/0.90    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.91/0.90    inference(ennf_transformation,[],[f19])).
% 2.91/0.90  fof(f19,axiom,(
% 2.91/0.90    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 2.91/0.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 2.91/0.90  fof(f2069,plain,(
% 2.91/0.90    ~spl2_16 | spl2_52 | ~spl2_29),
% 2.91/0.90    inference(avatar_split_clause,[],[f1157,f729,f1182,f353])).
% 2.91/0.90  fof(f1182,plain,(
% 2.91/0.90    spl2_52 <=> sK1 = k2_xboole_0(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))),
% 2.91/0.90    introduced(avatar_definition,[new_symbols(naming,[spl2_52])])).
% 2.91/0.90  fof(f729,plain,(
% 2.91/0.90    spl2_29 <=> k1_tops_1(sK0,sK1) = k3_subset_1(sK1,k2_tops_1(sK0,sK1))),
% 2.91/0.90    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).
% 2.91/0.90  fof(f1157,plain,(
% 2.91/0.90    sK1 = k2_xboole_0(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) | ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | ~spl2_29),
% 2.91/0.90    inference(superposition,[],[f304,f731])).
% 2.91/0.90  fof(f731,plain,(
% 2.91/0.90    k1_tops_1(sK0,sK1) = k3_subset_1(sK1,k2_tops_1(sK0,sK1)) | ~spl2_29),
% 2.91/0.90    inference(avatar_component_clause,[],[f729])).
% 2.91/0.90  fof(f304,plain,(
% 2.91/0.90    ( ! [X0,X1] : (k2_xboole_0(X1,k3_subset_1(X0,X1)) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.91/0.90    inference(subsumption_resolution,[],[f303,f88])).
% 2.91/0.90  fof(f88,plain,(
% 2.91/0.90    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.91/0.90    inference(cnf_transformation,[],[f50])).
% 2.91/0.90  fof(f50,plain,(
% 2.91/0.90    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.91/0.90    inference(ennf_transformation,[],[f17])).
% 2.91/0.90  fof(f17,axiom,(
% 2.91/0.90    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 2.91/0.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 2.91/0.90  fof(f303,plain,(
% 2.91/0.90    ( ! [X0,X1] : (k2_xboole_0(X1,k3_subset_1(X0,X1)) = X0 | ~m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.91/0.90    inference(duplicate_literal_removal,[],[f300])).
% 2.91/0.90  fof(f300,plain,(
% 2.91/0.90    ( ! [X0,X1] : (k2_xboole_0(X1,k3_subset_1(X0,X1)) = X0 | ~m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.91/0.90    inference(superposition,[],[f102,f252])).
% 2.91/0.90  fof(f252,plain,(
% 2.91/0.90    ( ! [X0,X1] : (k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.91/0.90    inference(forward_demodulation,[],[f97,f105])).
% 2.91/0.90  fof(f105,plain,(
% 2.91/0.90    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 2.91/0.90    inference(cnf_transformation,[],[f15])).
% 2.91/0.90  fof(f15,axiom,(
% 2.91/0.90    ! [X0] : k2_subset_1(X0) = X0),
% 2.91/0.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 2.91/0.90  fof(f97,plain,(
% 2.91/0.90    ( ! [X0,X1] : (k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.91/0.90    inference(cnf_transformation,[],[f55])).
% 2.91/0.90  fof(f55,plain,(
% 2.91/0.90    ! [X0,X1] : (k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.91/0.90    inference(ennf_transformation,[],[f23])).
% 2.91/0.90  fof(f23,axiom,(
% 2.91/0.90    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 2.91/0.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).
% 2.91/0.90  fof(f2064,plain,(
% 2.91/0.90    spl2_9 | ~spl2_28 | ~spl2_50),
% 2.91/0.90    inference(avatar_split_clause,[],[f2063,f1166,f725,f222])).
% 2.91/0.90  fof(f725,plain,(
% 2.91/0.90    spl2_28 <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1))),
% 2.91/0.90    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).
% 2.91/0.90  fof(f2063,plain,(
% 2.91/0.90    k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | (~spl2_28 | ~spl2_50)),
% 2.91/0.90    inference(subsumption_resolution,[],[f1983,f726])).
% 2.91/0.90  fof(f726,plain,(
% 2.91/0.90    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | ~spl2_28),
% 2.91/0.90    inference(avatar_component_clause,[],[f725])).
% 2.91/0.90  fof(f1983,plain,(
% 2.91/0.90    k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | ~spl2_50),
% 2.91/0.90    inference(superposition,[],[f1168,f76])).
% 2.91/0.90  fof(f1168,plain,(
% 2.91/0.90    k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k1_tops_1(sK0,sK1)) | ~spl2_50),
% 2.91/0.90    inference(avatar_component_clause,[],[f1166])).
% 2.91/0.90  fof(f2042,plain,(
% 2.91/0.90    spl2_72 | ~spl2_52),
% 2.91/0.90    inference(avatar_split_clause,[],[f2025,f1182,f2039])).
% 2.91/0.90  fof(f2025,plain,(
% 2.91/0.90    sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl2_52),
% 2.91/0.90    inference(superposition,[],[f1289,f1184])).
% 2.91/0.90  fof(f1184,plain,(
% 2.91/0.90    sK1 = k2_xboole_0(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) | ~spl2_52),
% 2.91/0.90    inference(avatar_component_clause,[],[f1182])).
% 2.91/0.90  fof(f1289,plain,(
% 2.91/0.90    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(k2_xboole_0(X0,X1),X0)) )),
% 2.91/0.90    inference(backward_demodulation,[],[f184,f642])).
% 2.91/0.90  fof(f642,plain,(
% 2.91/0.90    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.91/0.90    inference(subsumption_resolution,[],[f630,f96])).
% 2.91/0.90  fof(f96,plain,(
% 2.91/0.90    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.91/0.90    inference(cnf_transformation,[],[f8])).
% 2.91/0.90  fof(f8,axiom,(
% 2.91/0.90    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.91/0.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 2.91/0.90  fof(f630,plain,(
% 2.91/0.90    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0 | ~r1_tarski(k1_xboole_0,X0)) )),
% 2.91/0.90    inference(superposition,[],[f185,f103])).
% 2.91/0.90  fof(f103,plain,(
% 2.91/0.90    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.91/0.90    inference(cnf_transformation,[],[f5])).
% 2.91/0.90  fof(f5,axiom,(
% 2.91/0.90    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 2.91/0.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 2.91/0.90  fof(f185,plain,(
% 2.91/0.90    ( ! [X2,X3] : (k2_xboole_0(X3,X2) = k5_xboole_0(X3,k1_xboole_0) | ~r1_tarski(X2,X3)) )),
% 2.91/0.90    inference(superposition,[],[f99,f92])).
% 2.91/0.90  fof(f92,plain,(
% 2.91/0.90    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 2.91/0.90    inference(cnf_transformation,[],[f66])).
% 2.91/0.90  fof(f66,plain,(
% 2.91/0.90    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 2.91/0.90    inference(nnf_transformation,[],[f2])).
% 2.91/0.90  fof(f2,axiom,(
% 2.91/0.90    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 2.91/0.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 2.91/0.90  fof(f99,plain,(
% 2.91/0.90    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.91/0.90    inference(cnf_transformation,[],[f12])).
% 2.91/0.90  fof(f12,axiom,(
% 2.91/0.90    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.91/0.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 2.91/0.90  fof(f184,plain,(
% 2.91/0.90    ( ! [X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X0) = k5_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0)) )),
% 2.91/0.90    inference(superposition,[],[f99,f101])).
% 2.91/0.90  fof(f101,plain,(
% 2.91/0.90    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 2.91/0.90    inference(cnf_transformation,[],[f11])).
% 2.91/0.90  fof(f11,axiom,(
% 2.91/0.90    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 2.91/0.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 2.91/0.90  fof(f864,plain,(
% 2.91/0.90    ~spl2_12 | spl2_28),
% 2.91/0.90    inference(avatar_contradiction_clause,[],[f863])).
% 2.91/0.90  fof(f863,plain,(
% 2.91/0.90    $false | (~spl2_12 | spl2_28)),
% 2.91/0.90    inference(subsumption_resolution,[],[f861,f250])).
% 2.91/0.90  fof(f250,plain,(
% 2.91/0.90    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~spl2_12),
% 2.91/0.90    inference(avatar_component_clause,[],[f248])).
% 2.91/0.90  fof(f248,plain,(
% 2.91/0.90    spl2_12 <=> r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 2.91/0.90    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 2.91/0.90  fof(f861,plain,(
% 2.91/0.90    ~r1_tarski(k1_tops_1(sK0,sK1),sK1) | spl2_28),
% 2.91/0.90    inference(resolution,[],[f727,f87])).
% 2.91/0.90  fof(f727,plain,(
% 2.91/0.90    ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | spl2_28),
% 2.91/0.90    inference(avatar_component_clause,[],[f725])).
% 2.91/0.90  fof(f732,plain,(
% 2.91/0.90    ~spl2_28 | spl2_29 | ~spl2_9),
% 2.91/0.90    inference(avatar_split_clause,[],[f716,f222,f729,f725])).
% 2.91/0.90  fof(f716,plain,(
% 2.91/0.90    k1_tops_1(sK0,sK1) = k3_subset_1(sK1,k2_tops_1(sK0,sK1)) | ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | ~spl2_9),
% 2.91/0.90    inference(superposition,[],[f215,f224])).
% 2.91/0.90  fof(f224,plain,(
% 2.91/0.90    k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | ~spl2_9),
% 2.91/0.90    inference(avatar_component_clause,[],[f222])).
% 2.91/0.90  fof(f560,plain,(
% 2.91/0.90    spl2_9 | ~spl2_2 | ~spl2_3),
% 2.91/0.90    inference(avatar_split_clause,[],[f559,f120,f114,f222])).
% 2.91/0.90  fof(f559,plain,(
% 2.91/0.90    k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | (~spl2_2 | ~spl2_3)),
% 2.91/0.90    inference(subsumption_resolution,[],[f556,f122])).
% 2.91/0.90  fof(f556,plain,(
% 2.91/0.90    k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_2),
% 2.91/0.90    inference(superposition,[],[f78,f115])).
% 2.91/0.90  fof(f115,plain,(
% 2.91/0.90    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~spl2_2),
% 2.91/0.90    inference(avatar_component_clause,[],[f114])).
% 2.91/0.90  fof(f554,plain,(
% 2.91/0.90    spl2_1 | ~spl2_3 | ~spl2_4 | ~spl2_5 | ~spl2_17),
% 2.91/0.90    inference(avatar_split_clause,[],[f553,f360,f130,f125,f120,f110])).
% 2.91/0.90  fof(f110,plain,(
% 2.91/0.90    spl2_1 <=> v4_pre_topc(sK1,sK0)),
% 2.91/0.90    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 2.91/0.90  fof(f130,plain,(
% 2.91/0.90    spl2_5 <=> v2_pre_topc(sK0)),
% 2.91/0.90    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 2.91/0.90  fof(f553,plain,(
% 2.91/0.90    v4_pre_topc(sK1,sK0) | (~spl2_3 | ~spl2_4 | ~spl2_5 | ~spl2_17)),
% 2.91/0.90    inference(subsumption_resolution,[],[f552,f127])).
% 2.91/0.90  fof(f552,plain,(
% 2.91/0.90    v4_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | (~spl2_3 | ~spl2_5 | ~spl2_17)),
% 2.91/0.90    inference(subsumption_resolution,[],[f551,f122])).
% 2.91/0.90  fof(f551,plain,(
% 2.91/0.90    v4_pre_topc(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl2_5 | ~spl2_17)),
% 2.91/0.90    inference(subsumption_resolution,[],[f422,f132])).
% 2.91/0.90  fof(f132,plain,(
% 2.91/0.90    v2_pre_topc(sK0) | ~spl2_5),
% 2.91/0.90    inference(avatar_component_clause,[],[f130])).
% 2.91/0.90  fof(f422,plain,(
% 2.91/0.90    v4_pre_topc(sK1,sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl2_17),
% 2.91/0.90    inference(trivial_inequality_removal,[],[f421])).
% 2.91/0.90  fof(f421,plain,(
% 2.91/0.90    sK1 != sK1 | v4_pre_topc(sK1,sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl2_17),
% 2.91/0.90    inference(superposition,[],[f85,f362])).
% 2.91/0.90  fof(f362,plain,(
% 2.91/0.90    sK1 = k2_pre_topc(sK0,sK1) | ~spl2_17),
% 2.91/0.90    inference(avatar_component_clause,[],[f360])).
% 2.91/0.90  fof(f85,plain,(
% 2.91/0.90    ( ! [X0,X1] : (k2_pre_topc(X0,X1) != X1 | v4_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.91/0.90    inference(cnf_transformation,[],[f49])).
% 2.91/0.90  fof(f49,plain,(
% 2.91/0.90    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.91/0.90    inference(flattening,[],[f48])).
% 2.91/0.90  fof(f48,plain,(
% 2.91/0.90    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.91/0.90    inference(ennf_transformation,[],[f26])).
% 2.91/0.90  fof(f26,axiom,(
% 2.91/0.90    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 2.91/0.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).
% 2.91/0.90  fof(f391,plain,(
% 2.91/0.90    spl2_16 | ~spl2_9),
% 2.91/0.90    inference(avatar_split_clause,[],[f386,f222,f353])).
% 2.91/0.90  fof(f386,plain,(
% 2.91/0.90    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | ~spl2_9),
% 2.91/0.90    inference(superposition,[],[f142,f224])).
% 2.91/0.90  fof(f142,plain,(
% 2.91/0.90    ( ! [X0,X1] : (m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0))) )),
% 2.91/0.90    inference(backward_demodulation,[],[f106,f100])).
% 2.91/0.90  fof(f100,plain,(
% 2.91/0.90    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 2.91/0.90    inference(cnf_transformation,[],[f21])).
% 2.91/0.90  fof(f21,axiom,(
% 2.91/0.90    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 2.91/0.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 2.91/0.90  fof(f106,plain,(
% 2.91/0.90    ( ! [X0,X1] : (m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 2.91/0.90    inference(cnf_transformation,[],[f18])).
% 2.91/0.90  fof(f18,axiom,(
% 2.91/0.90    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))),
% 2.91/0.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).
% 2.91/0.90  fof(f282,plain,(
% 2.91/0.90    spl2_14 | ~spl2_1 | ~spl2_3 | ~spl2_4),
% 2.91/0.90    inference(avatar_split_clause,[],[f281,f125,f120,f110,f277])).
% 2.91/0.90  fof(f281,plain,(
% 2.91/0.90    ~v4_pre_topc(sK1,sK0) | r1_tarski(k2_tops_1(sK0,sK1),sK1) | (~spl2_3 | ~spl2_4)),
% 2.91/0.90    inference(subsumption_resolution,[],[f272,f127])).
% 2.91/0.90  fof(f272,plain,(
% 2.91/0.90    ~v4_pre_topc(sK1,sK0) | r1_tarski(k2_tops_1(sK0,sK1),sK1) | ~l1_pre_topc(sK0) | ~spl2_3),
% 2.91/0.90    inference(resolution,[],[f82,f122])).
% 2.91/0.90  fof(f82,plain,(
% 2.91/0.90    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | r1_tarski(k2_tops_1(X0,X1),X1) | ~l1_pre_topc(X0)) )),
% 2.91/0.90    inference(cnf_transformation,[],[f46])).
% 2.91/0.90  fof(f46,plain,(
% 2.91/0.90    ! [X0] : (! [X1] : (r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.91/0.90    inference(flattening,[],[f45])).
% 2.91/0.90  fof(f45,plain,(
% 2.91/0.90    ! [X0] : (! [X1] : ((r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.91/0.90    inference(ennf_transformation,[],[f31])).
% 2.91/0.90  fof(f31,axiom,(
% 2.91/0.90    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => r1_tarski(k2_tops_1(X0,X1),X1))))),
% 2.91/0.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).
% 2.91/0.90  fof(f251,plain,(
% 2.91/0.90    spl2_12 | ~spl2_3 | ~spl2_4),
% 2.91/0.90    inference(avatar_split_clause,[],[f246,f125,f120,f248])).
% 2.91/0.90  fof(f246,plain,(
% 2.91/0.90    r1_tarski(k1_tops_1(sK0,sK1),sK1) | (~spl2_3 | ~spl2_4)),
% 2.91/0.90    inference(subsumption_resolution,[],[f245,f127])).
% 2.91/0.90  fof(f245,plain,(
% 2.91/0.90    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~l1_pre_topc(sK0) | ~spl2_3),
% 2.91/0.90    inference(resolution,[],[f80,f122])).
% 2.91/0.90  fof(f80,plain,(
% 2.91/0.90    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k1_tops_1(X0,X1),X1) | ~l1_pre_topc(X0)) )),
% 2.91/0.90    inference(cnf_transformation,[],[f42])).
% 2.91/0.90  fof(f42,plain,(
% 2.91/0.90    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.91/0.90    inference(ennf_transformation,[],[f28])).
% 2.91/0.90  fof(f28,axiom,(
% 2.91/0.90    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 2.91/0.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).
% 2.91/0.90  fof(f133,plain,(
% 2.91/0.90    spl2_5),
% 2.91/0.90    inference(avatar_split_clause,[],[f67,f130])).
% 2.91/0.90  fof(f67,plain,(
% 2.91/0.90    v2_pre_topc(sK0)),
% 2.91/0.90    inference(cnf_transformation,[],[f62])).
% 2.91/0.90  fof(f62,plain,(
% 2.91/0.90    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 2.91/0.90    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f59,f61,f60])).
% 2.91/0.90  fof(f60,plain,(
% 2.91/0.90    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 2.91/0.90    introduced(choice_axiom,[])).
% 2.91/0.90  fof(f61,plain,(
% 2.91/0.90    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.91/0.90    introduced(choice_axiom,[])).
% 2.91/0.90  fof(f59,plain,(
% 2.91/0.90    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.91/0.90    inference(flattening,[],[f58])).
% 2.91/0.90  fof(f58,plain,(
% 2.91/0.90    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.91/0.90    inference(nnf_transformation,[],[f36])).
% 2.91/0.90  fof(f36,plain,(
% 2.91/0.90    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.91/0.90    inference(flattening,[],[f35])).
% 2.91/0.90  fof(f35,plain,(
% 2.91/0.90    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 2.91/0.90    inference(ennf_transformation,[],[f34])).
% 2.91/0.90  fof(f34,negated_conjecture,(
% 2.91/0.90    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 2.91/0.90    inference(negated_conjecture,[],[f33])).
% 2.91/0.90  fof(f33,conjecture,(
% 2.91/0.90    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 2.91/0.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).
% 2.91/0.90  fof(f128,plain,(
% 2.91/0.90    spl2_4),
% 2.91/0.90    inference(avatar_split_clause,[],[f68,f125])).
% 2.91/0.90  fof(f68,plain,(
% 2.91/0.90    l1_pre_topc(sK0)),
% 2.91/0.90    inference(cnf_transformation,[],[f62])).
% 2.91/0.90  fof(f123,plain,(
% 2.91/0.90    spl2_3),
% 2.91/0.90    inference(avatar_split_clause,[],[f69,f120])).
% 2.91/0.90  fof(f69,plain,(
% 2.91/0.90    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.91/0.90    inference(cnf_transformation,[],[f62])).
% 2.91/0.90  fof(f118,plain,(
% 2.91/0.90    spl2_1 | spl2_2),
% 2.91/0.90    inference(avatar_split_clause,[],[f70,f114,f110])).
% 2.91/0.90  fof(f70,plain,(
% 2.91/0.90    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)),
% 2.91/0.90    inference(cnf_transformation,[],[f62])).
% 2.91/0.90  fof(f117,plain,(
% 2.91/0.90    ~spl2_1 | ~spl2_2),
% 2.91/0.90    inference(avatar_split_clause,[],[f71,f114,f110])).
% 2.91/0.90  fof(f71,plain,(
% 2.91/0.90    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)),
% 2.91/0.90    inference(cnf_transformation,[],[f62])).
% 2.91/0.90  % SZS output end Proof for theBenchmark
% 2.91/0.90  % (23008)------------------------------
% 2.91/0.90  % (23008)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.91/0.90  % (23008)Termination reason: Refutation
% 2.91/0.90  
% 2.91/0.90  % (23008)Memory used [KB]: 8059
% 2.91/0.90  % (23008)Time elapsed: 0.288 s
% 2.91/0.90  % (23008)------------------------------
% 2.91/0.90  % (23008)------------------------------
% 3.09/0.91  % (22851)Success in time 0.546 s
%------------------------------------------------------------------------------
