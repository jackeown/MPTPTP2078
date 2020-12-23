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
% DateTime   : Thu Dec  3 13:11:40 EST 2020

% Result     : Theorem 1.37s
% Output     : Refutation 1.37s
% Verified   : 
% Statistics : Number of formulae       :  188 ( 320 expanded)
%              Number of leaves         :   45 ( 126 expanded)
%              Depth                    :   11
%              Number of atoms          :  561 (1009 expanded)
%              Number of equality atoms :  113 ( 223 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f722,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f96,f97,f102,f107,f112,f126,f163,f213,f243,f313,f357,f385,f430,f442,f448,f455,f462,f463,f546,f570,f683,f702,f721])).

fof(f721,plain,
    ( sK1 != k1_tops_1(sK0,sK1)
    | v3_pre_topc(sK1,sK0)
    | ~ v3_pre_topc(k1_tops_1(sK0,sK1),sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f702,plain,
    ( spl2_31
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_44 ),
    inference(avatar_split_clause,[],[f701,f678,f104,f99,f382])).

fof(f382,plain,
    ( spl2_31
  <=> sK1 = k1_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).

fof(f99,plain,
    ( spl2_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f104,plain,
    ( spl2_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f678,plain,
    ( spl2_44
  <=> sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_44])])).

fof(f701,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_44 ),
    inference(subsumption_resolution,[],[f700,f106])).

fof(f106,plain,
    ( l1_pre_topc(sK0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f104])).

fof(f700,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl2_3
    | ~ spl2_44 ),
    inference(subsumption_resolution,[],[f691,f101])).

fof(f101,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f99])).

fof(f691,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_44 ),
    inference(superposition,[],[f265,f680])).

fof(f680,plain,
    ( sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_44 ),
    inference(avatar_component_clause,[],[f678])).

fof(f265,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f264])).

fof(f264,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(superposition,[],[f61,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f683,plain,
    ( spl2_44
    | ~ spl2_27
    | ~ spl2_40 ),
    inference(avatar_split_clause,[],[f682,f543,f332,f678])).

fof(f332,plain,
    ( spl2_27
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).

fof(f543,plain,
    ( spl2_40
  <=> sK1 = k7_subset_1(k2_pre_topc(sK0,sK1),sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_40])])).

fof(f682,plain,
    ( sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_27
    | ~ spl2_40 ),
    inference(subsumption_resolution,[],[f675,f333])).

fof(f333,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl2_27 ),
    inference(avatar_component_clause,[],[f332])).

fof(f675,plain,
    ( sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl2_40 ),
    inference(superposition,[],[f61,f545])).

fof(f545,plain,
    ( sK1 = k7_subset_1(k2_pre_topc(sK0,sK1),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_40 ),
    inference(avatar_component_clause,[],[f543])).

fof(f570,plain,(
    ~ spl2_39 ),
    inference(avatar_contradiction_clause,[],[f559])).

fof(f559,plain,
    ( $false
    | ~ spl2_39 ),
    inference(unit_resulting_resolution,[],[f127,f541,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f541,plain,
    ( ! [X1] : ~ m1_subset_1(X1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl2_39 ),
    inference(avatar_component_clause,[],[f540])).

fof(f540,plain,
    ( spl2_39
  <=> ! [X1] : ~ m1_subset_1(X1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_39])])).

fof(f127,plain,(
    ! [X0,X1] : m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0)) ),
    inference(backward_demodulation,[],[f85,f77])).

fof(f77,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f85,plain,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).

fof(f546,plain,
    ( spl2_39
    | spl2_40
    | ~ spl2_24
    | ~ spl2_28 ),
    inference(avatar_split_clause,[],[f538,f336,f310,f543,f540])).

fof(f310,plain,
    ( spl2_24
  <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).

fof(f336,plain,
    ( spl2_28
  <=> sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).

fof(f538,plain,
    ( ! [X1] :
        ( sK1 = k7_subset_1(k2_pre_topc(sK0,sK1),sK1,k2_tops_1(sK0,sK1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) )
    | ~ spl2_24
    | ~ spl2_28 ),
    inference(subsumption_resolution,[],[f522,f312])).

fof(f312,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl2_24 ),
    inference(avatar_component_clause,[],[f310])).

fof(f522,plain,
    ( ! [X1] :
        ( sK1 = k7_subset_1(k2_pre_topc(sK0,sK1),sK1,k2_tops_1(sK0,sK1))
        | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) )
    | ~ spl2_28 ),
    inference(superposition,[],[f289,f338])).

fof(f338,plain,
    ( sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))
    | ~ spl2_28 ),
    inference(avatar_component_clause,[],[f336])).

fof(f289,plain,(
    ! [X4,X5,X3] :
      ( k3_subset_1(X3,X4) = k7_subset_1(X3,k3_subset_1(X3,X4),X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(X3)) ) ),
    inference(subsumption_resolution,[],[f285,f75])).

fof(f285,plain,(
    ! [X4,X5,X3] :
      ( k3_subset_1(X3,X4) = k7_subset_1(X3,k3_subset_1(X3,X4),X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
      | ~ m1_subset_1(k3_subset_1(X3,X4),k1_zfmisc_1(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(X3)) ) ),
    inference(superposition,[],[f68,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k9_subset_1)).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_subset_1)).

fof(f463,plain,
    ( spl2_29
    | ~ spl2_34 ),
    inference(avatar_split_clause,[],[f458,f424,f354])).

fof(f354,plain,
    ( spl2_29
  <=> r1_tarski(sK1,k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).

fof(f424,plain,
    ( spl2_34
  <=> k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).

fof(f458,plain,
    ( r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | ~ spl2_34 ),
    inference(superposition,[],[f174,f426])).

fof(f426,plain,
    ( k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_pre_topc(sK0,sK1))
    | ~ spl2_34 ),
    inference(avatar_component_clause,[],[f424])).

fof(f174,plain,(
    ! [X0,X1] : r1_tarski(X1,k2_xboole_0(X1,X0)) ),
    inference(superposition,[],[f171,f65])).

fof(f65,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f171,plain,(
    ! [X2,X3] : r1_tarski(X2,k2_xboole_0(X3,X2)) ),
    inference(forward_demodulation,[],[f170,f64])).

fof(f64,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f170,plain,(
    ! [X2,X3] : r1_tarski(X2,k2_xboole_0(X3,k4_xboole_0(X2,X3))) ),
    inference(resolution,[],[f76,f86])).

fof(f86,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k4_xboole_0(X0,X1),X2)
      | r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f462,plain,
    ( ~ spl2_27
    | spl2_28
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f450,f201,f336,f332])).

fof(f201,plain,
    ( spl2_14
  <=> k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f450,plain,
    ( sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl2_14 ),
    inference(superposition,[],[f186,f203])).

fof(f203,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f201])).

fof(f186,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f180])).

fof(f180,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f62,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f62,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f455,plain,
    ( spl2_23
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f453,f201,f305])).

fof(f305,plain,
    ( spl2_23
  <=> k2_xboole_0(sK1,k2_pre_topc(sK0,sK1)) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).

fof(f453,plain,
    ( k2_xboole_0(sK1,k2_pre_topc(sK0,sK1)) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_14 ),
    inference(superposition,[],[f64,f203])).

fof(f448,plain,
    ( spl2_14
    | ~ spl2_2
    | ~ spl2_13 ),
    inference(avatar_split_clause,[],[f447,f197,f93,f201])).

fof(f93,plain,
    ( spl2_2
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f197,plain,
    ( spl2_13
  <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f447,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl2_2
    | ~ spl2_13 ),
    inference(subsumption_resolution,[],[f444,f198])).

fof(f198,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f197])).

fof(f444,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_2 ),
    inference(superposition,[],[f61,f94])).

fof(f94,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f93])).

fof(f442,plain,
    ( spl2_2
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_31 ),
    inference(avatar_contradiction_clause,[],[f441])).

fof(f441,plain,
    ( $false
    | spl2_2
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_31 ),
    inference(subsumption_resolution,[],[f440,f106])).

fof(f440,plain,
    ( ~ l1_pre_topc(sK0)
    | spl2_2
    | ~ spl2_3
    | ~ spl2_31 ),
    inference(subsumption_resolution,[],[f439,f101])).

fof(f439,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl2_2
    | ~ spl2_31 ),
    inference(subsumption_resolution,[],[f436,f95])).

fof(f95,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f93])).

fof(f436,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_31 ),
    inference(superposition,[],[f66,f384])).

fof(f384,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ spl2_31 ),
    inference(avatar_component_clause,[],[f382])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

fof(f430,plain,
    ( spl2_34
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_23 ),
    inference(avatar_split_clause,[],[f429,f305,f104,f99,f424])).

fof(f429,plain,
    ( k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_pre_topc(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_23 ),
    inference(subsumption_resolution,[],[f428,f106])).

fof(f428,plain,
    ( k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_pre_topc(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_3
    | ~ spl2_23 ),
    inference(subsumption_resolution,[],[f420,f101])).

fof(f420,plain,
    ( k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_pre_topc(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_23 ),
    inference(superposition,[],[f307,f281])).

fof(f281,plain,(
    ! [X2,X3] :
      ( k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2) ) ),
    inference(subsumption_resolution,[],[f280,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f280,plain,(
    ! [X2,X3] :
      ( k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) ) ),
    inference(duplicate_literal_removal,[],[f277])).

fof(f277,plain,(
    ! [X2,X3] :
      ( k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ) ),
    inference(superposition,[],[f70,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f70,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

fof(f307,plain,
    ( k2_xboole_0(sK1,k2_pre_topc(sK0,sK1)) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_23 ),
    inference(avatar_component_clause,[],[f305])).

fof(f385,plain,
    ( ~ spl2_1
    | spl2_31
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f380,f124,f104,f99,f382,f89])).

fof(f89,plain,
    ( spl2_1
  <=> v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f124,plain,
    ( spl2_9
  <=> ! [X1,X3] :
        ( k1_tops_1(X1,X3) = X3
        | ~ l1_pre_topc(X1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ v3_pre_topc(X3,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f380,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ v3_pre_topc(sK1,sK0)
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_9 ),
    inference(subsumption_resolution,[],[f250,f106])).

fof(f250,plain,
    ( ~ l1_pre_topc(sK0)
    | sK1 = k1_tops_1(sK0,sK1)
    | ~ v3_pre_topc(sK1,sK0)
    | ~ spl2_3
    | ~ spl2_9 ),
    inference(resolution,[],[f125,f101])).

fof(f125,plain,
    ( ! [X3,X1] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ l1_pre_topc(X1)
        | k1_tops_1(X1,X3) = X3
        | ~ v3_pre_topc(X3,X1) )
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f124])).

fof(f357,plain,
    ( ~ spl2_29
    | spl2_27 ),
    inference(avatar_split_clause,[],[f352,f332,f354])).

fof(f352,plain,
    ( ~ r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | spl2_27 ),
    inference(resolution,[],[f334,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f334,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | spl2_27 ),
    inference(avatar_component_clause,[],[f332])).

fof(f313,plain,
    ( spl2_24
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f298,f201,f310])).

fof(f298,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl2_14 ),
    inference(superposition,[],[f127,f203])).

fof(f243,plain,
    ( spl2_17
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f238,f109,f104,f99,f240])).

fof(f240,plain,
    ( spl2_17
  <=> v3_pre_topc(k1_tops_1(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f109,plain,
    ( spl2_5
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f238,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f237,f111])).

fof(f111,plain,
    ( v2_pre_topc(sK0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f109])).

fof(f237,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f227,f106])).

fof(f227,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl2_3 ),
    inference(resolution,[],[f72,f101])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

fof(f213,plain,
    ( ~ spl2_3
    | ~ spl2_4
    | spl2_13 ),
    inference(avatar_contradiction_clause,[],[f212])).

fof(f212,plain,
    ( $false
    | ~ spl2_3
    | ~ spl2_4
    | spl2_13 ),
    inference(subsumption_resolution,[],[f211,f106])).

fof(f211,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl2_3
    | spl2_13 ),
    inference(subsumption_resolution,[],[f208,f101])).

fof(f208,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl2_13 ),
    inference(resolution,[],[f199,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f199,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_13 ),
    inference(avatar_component_clause,[],[f197])).

fof(f163,plain,
    ( ~ spl2_4
    | ~ spl2_5
    | ~ spl2_8 ),
    inference(avatar_contradiction_clause,[],[f158])).

fof(f158,plain,
    ( $false
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_8 ),
    inference(unit_resulting_resolution,[],[f106,f111,f127,f122])).

fof(f122,plain,
    ( ! [X2,X0] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl2_8
  <=> ! [X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f126,plain,
    ( spl2_8
    | spl2_9 ),
    inference(avatar_split_clause,[],[f73,f124,f121])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_tops_1(X1,X3) = X3
      | ~ v3_pre_topc(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v3_pre_topc(X2,X0)
                      | k1_tops_1(X0,X2) != X2 )
                    & ( k1_tops_1(X1,X3) = X3
                      | ~ v3_pre_topc(X3,X1) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v3_pre_topc(X2,X0)
                      | k1_tops_1(X0,X2) != X2 )
                    & ( k1_tops_1(X1,X3) = X3
                      | ~ v3_pre_topc(X3,X1) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( k1_tops_1(X0,X2) = X2
                     => v3_pre_topc(X2,X0) )
                    & ( v3_pre_topc(X3,X1)
                     => k1_tops_1(X1,X3) = X3 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tops_1)).

fof(f112,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f56,f109])).

fof(f56,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
      | ~ v3_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
      | v3_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f49,f51,f50])).

fof(f50,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
              | ~ v3_pre_topc(X1,X0) )
            & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
              | v3_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ( k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
            | ~ v3_pre_topc(X1,sK0) )
          & ( k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
            | v3_pre_topc(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( ? [X1] :
        ( ( k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
          | ~ v3_pre_topc(X1,sK0) )
        & ( k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
          | v3_pre_topc(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
        | ~ v3_pre_topc(sK1,sK0) )
      & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
        | v3_pre_topc(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f24,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_1)).

fof(f107,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f57,f104])).

fof(f57,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f102,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f58,f99])).

fof(f58,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f52])).

fof(f97,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f59,f93,f89])).

fof(f59,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f96,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f60,f93,f89])).

fof(f60,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f52])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:01:14 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (6322)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.17/0.52  % (6330)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.17/0.53  % (6320)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.17/0.53  % (6319)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.17/0.53  % (6329)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.17/0.54  % (6328)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.17/0.54  % (6327)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.37/0.54  % (6315)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.37/0.54  % (6327)Refutation not found, incomplete strategy% (6327)------------------------------
% 1.37/0.54  % (6327)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.54  % (6327)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.54  
% 1.37/0.54  % (6327)Memory used [KB]: 10618
% 1.37/0.54  % (6327)Time elapsed: 0.119 s
% 1.37/0.54  % (6327)------------------------------
% 1.37/0.54  % (6327)------------------------------
% 1.37/0.54  % (6337)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.37/0.54  % (6321)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.37/0.54  % (6335)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.37/0.54  % (6326)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.37/0.55  % (6336)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.37/0.55  % (6313)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.37/0.55  % (6321)Refutation not found, incomplete strategy% (6321)------------------------------
% 1.37/0.55  % (6321)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.55  % (6316)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.37/0.56  % (6318)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.37/0.56  % (6321)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.56  
% 1.37/0.56  % (6321)Memory used [KB]: 10874
% 1.37/0.56  % (6321)Time elapsed: 0.129 s
% 1.37/0.56  % (6321)------------------------------
% 1.37/0.56  % (6321)------------------------------
% 1.37/0.56  % (6339)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.37/0.56  % (6312)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.37/0.56  % (6332)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.37/0.56  % (6334)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.37/0.56  % (6338)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.37/0.56  % (6331)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.37/0.56  % (6323)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.37/0.57  % (6325)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.37/0.57  % (6324)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.37/0.57  % (6311)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.37/0.57  % (6333)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.37/0.57  % (6340)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.37/0.57  % (6340)Refutation not found, incomplete strategy% (6340)------------------------------
% 1.37/0.57  % (6340)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.57  % (6340)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.57  
% 1.37/0.57  % (6340)Memory used [KB]: 1663
% 1.37/0.57  % (6340)Time elapsed: 0.147 s
% 1.37/0.57  % (6340)------------------------------
% 1.37/0.57  % (6340)------------------------------
% 1.37/0.58  % (6314)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.37/0.58  % (6317)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.37/0.58  % (6339)Refutation not found, incomplete strategy% (6339)------------------------------
% 1.37/0.58  % (6339)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.58  % (6339)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.58  
% 1.37/0.58  % (6339)Memory used [KB]: 10874
% 1.37/0.58  % (6339)Time elapsed: 0.173 s
% 1.37/0.58  % (6339)------------------------------
% 1.37/0.58  % (6339)------------------------------
% 1.37/0.61  % (6332)Refutation found. Thanks to Tanya!
% 1.37/0.61  % SZS status Theorem for theBenchmark
% 1.37/0.61  % SZS output start Proof for theBenchmark
% 1.37/0.61  fof(f722,plain,(
% 1.37/0.61    $false),
% 1.37/0.61    inference(avatar_sat_refutation,[],[f96,f97,f102,f107,f112,f126,f163,f213,f243,f313,f357,f385,f430,f442,f448,f455,f462,f463,f546,f570,f683,f702,f721])).
% 1.37/0.61  fof(f721,plain,(
% 1.37/0.61    sK1 != k1_tops_1(sK0,sK1) | v3_pre_topc(sK1,sK0) | ~v3_pre_topc(k1_tops_1(sK0,sK1),sK0)),
% 1.37/0.61    introduced(theory_tautology_sat_conflict,[])).
% 1.37/0.61  fof(f702,plain,(
% 1.37/0.61    spl2_31 | ~spl2_3 | ~spl2_4 | ~spl2_44),
% 1.37/0.61    inference(avatar_split_clause,[],[f701,f678,f104,f99,f382])).
% 1.37/0.61  fof(f382,plain,(
% 1.37/0.61    spl2_31 <=> sK1 = k1_tops_1(sK0,sK1)),
% 1.37/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).
% 1.37/0.61  fof(f99,plain,(
% 1.37/0.61    spl2_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.37/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 1.37/0.61  fof(f104,plain,(
% 1.37/0.61    spl2_4 <=> l1_pre_topc(sK0)),
% 1.37/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 1.37/0.61  fof(f678,plain,(
% 1.37/0.61    spl2_44 <=> sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 1.37/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_44])])).
% 1.37/0.61  fof(f701,plain,(
% 1.37/0.61    sK1 = k1_tops_1(sK0,sK1) | (~spl2_3 | ~spl2_4 | ~spl2_44)),
% 1.37/0.61    inference(subsumption_resolution,[],[f700,f106])).
% 1.37/0.61  fof(f106,plain,(
% 1.37/0.61    l1_pre_topc(sK0) | ~spl2_4),
% 1.37/0.61    inference(avatar_component_clause,[],[f104])).
% 1.37/0.61  fof(f700,plain,(
% 1.37/0.61    sK1 = k1_tops_1(sK0,sK1) | ~l1_pre_topc(sK0) | (~spl2_3 | ~spl2_44)),
% 1.37/0.61    inference(subsumption_resolution,[],[f691,f101])).
% 1.37/0.61  fof(f101,plain,(
% 1.37/0.61    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_3),
% 1.37/0.61    inference(avatar_component_clause,[],[f99])).
% 1.37/0.61  fof(f691,plain,(
% 1.37/0.61    sK1 = k1_tops_1(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl2_44),
% 1.37/0.61    inference(superposition,[],[f265,f680])).
% 1.37/0.61  fof(f680,plain,(
% 1.37/0.61    sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl2_44),
% 1.37/0.61    inference(avatar_component_clause,[],[f678])).
% 1.37/0.61  fof(f265,plain,(
% 1.37/0.61    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.37/0.61    inference(duplicate_literal_removal,[],[f264])).
% 1.37/0.61  fof(f264,plain,(
% 1.37/0.61    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.37/0.61    inference(superposition,[],[f61,f67])).
% 1.37/0.61  fof(f67,plain,(
% 1.37/0.61    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.37/0.61    inference(cnf_transformation,[],[f32])).
% 1.37/0.61  fof(f32,plain,(
% 1.37/0.61    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.37/0.61    inference(ennf_transformation,[],[f23])).
% 1.37/0.61  fof(f23,axiom,(
% 1.37/0.61    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 1.37/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).
% 1.37/0.61  fof(f61,plain,(
% 1.37/0.61    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.37/0.61    inference(cnf_transformation,[],[f28])).
% 1.37/0.61  fof(f28,plain,(
% 1.37/0.61    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.37/0.61    inference(ennf_transformation,[],[f13])).
% 1.37/0.61  fof(f13,axiom,(
% 1.37/0.61    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 1.37/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 1.37/0.61  fof(f683,plain,(
% 1.37/0.61    spl2_44 | ~spl2_27 | ~spl2_40),
% 1.37/0.61    inference(avatar_split_clause,[],[f682,f543,f332,f678])).
% 1.37/0.61  fof(f332,plain,(
% 1.37/0.61    spl2_27 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))),
% 1.37/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).
% 1.37/0.61  fof(f543,plain,(
% 1.37/0.61    spl2_40 <=> sK1 = k7_subset_1(k2_pre_topc(sK0,sK1),sK1,k2_tops_1(sK0,sK1))),
% 1.37/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_40])])).
% 1.37/0.61  fof(f682,plain,(
% 1.37/0.61    sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | (~spl2_27 | ~spl2_40)),
% 1.37/0.61    inference(subsumption_resolution,[],[f675,f333])).
% 1.37/0.61  fof(f333,plain,(
% 1.37/0.61    m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~spl2_27),
% 1.37/0.61    inference(avatar_component_clause,[],[f332])).
% 1.37/0.61  fof(f675,plain,(
% 1.37/0.61    sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~spl2_40),
% 1.37/0.61    inference(superposition,[],[f61,f545])).
% 1.37/0.61  fof(f545,plain,(
% 1.37/0.61    sK1 = k7_subset_1(k2_pre_topc(sK0,sK1),sK1,k2_tops_1(sK0,sK1)) | ~spl2_40),
% 1.37/0.61    inference(avatar_component_clause,[],[f543])).
% 1.37/0.61  fof(f570,plain,(
% 1.37/0.61    ~spl2_39),
% 1.37/0.61    inference(avatar_contradiction_clause,[],[f559])).
% 1.37/0.61  fof(f559,plain,(
% 1.37/0.61    $false | ~spl2_39),
% 1.37/0.61    inference(unit_resulting_resolution,[],[f127,f541,f75])).
% 1.37/0.61  fof(f75,plain,(
% 1.37/0.61    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.37/0.61    inference(cnf_transformation,[],[f43])).
% 1.37/0.61  fof(f43,plain,(
% 1.37/0.61    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.37/0.61    inference(ennf_transformation,[],[f7])).
% 1.37/0.61  fof(f7,axiom,(
% 1.37/0.61    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.37/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 1.37/0.61  fof(f541,plain,(
% 1.37/0.61    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))) ) | ~spl2_39),
% 1.37/0.61    inference(avatar_component_clause,[],[f540])).
% 1.37/0.61  fof(f540,plain,(
% 1.37/0.61    spl2_39 <=> ! [X1] : ~m1_subset_1(X1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))),
% 1.37/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_39])])).
% 1.37/0.61  fof(f127,plain,(
% 1.37/0.61    ( ! [X0,X1] : (m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0))) )),
% 1.37/0.61    inference(backward_demodulation,[],[f85,f77])).
% 1.37/0.61  fof(f77,plain,(
% 1.37/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 1.37/0.61    inference(cnf_transformation,[],[f12])).
% 1.37/0.61  fof(f12,axiom,(
% 1.37/0.61    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 1.37/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 1.37/0.61  fof(f85,plain,(
% 1.37/0.61    ( ! [X0,X1] : (m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 1.37/0.61    inference(cnf_transformation,[],[f8])).
% 1.37/0.61  fof(f8,axiom,(
% 1.37/0.61    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))),
% 1.37/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).
% 1.37/0.61  fof(f546,plain,(
% 1.37/0.61    spl2_39 | spl2_40 | ~spl2_24 | ~spl2_28),
% 1.37/0.61    inference(avatar_split_clause,[],[f538,f336,f310,f543,f540])).
% 1.37/0.61  fof(f310,plain,(
% 1.37/0.61    spl2_24 <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))),
% 1.37/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).
% 1.37/0.61  fof(f336,plain,(
% 1.37/0.61    spl2_28 <=> sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))),
% 1.37/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).
% 1.37/0.61  fof(f538,plain,(
% 1.37/0.61    ( ! [X1] : (sK1 = k7_subset_1(k2_pre_topc(sK0,sK1),sK1,k2_tops_1(sK0,sK1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))) ) | (~spl2_24 | ~spl2_28)),
% 1.37/0.61    inference(subsumption_resolution,[],[f522,f312])).
% 1.37/0.61  fof(f312,plain,(
% 1.37/0.61    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~spl2_24),
% 1.37/0.61    inference(avatar_component_clause,[],[f310])).
% 1.37/0.61  fof(f522,plain,(
% 1.37/0.61    ( ! [X1] : (sK1 = k7_subset_1(k2_pre_topc(sK0,sK1),sK1,k2_tops_1(sK0,sK1)) | ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))) ) | ~spl2_28),
% 1.37/0.61    inference(superposition,[],[f289,f338])).
% 1.37/0.61  fof(f338,plain,(
% 1.37/0.61    sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) | ~spl2_28),
% 1.37/0.61    inference(avatar_component_clause,[],[f336])).
% 1.37/0.61  fof(f289,plain,(
% 1.37/0.61    ( ! [X4,X5,X3] : (k3_subset_1(X3,X4) = k7_subset_1(X3,k3_subset_1(X3,X4),X4) | ~m1_subset_1(X4,k1_zfmisc_1(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(X3))) )),
% 1.37/0.61    inference(subsumption_resolution,[],[f285,f75])).
% 1.37/0.61  fof(f285,plain,(
% 1.37/0.61    ( ! [X4,X5,X3] : (k3_subset_1(X3,X4) = k7_subset_1(X3,k3_subset_1(X3,X4),X4) | ~m1_subset_1(X4,k1_zfmisc_1(X3)) | ~m1_subset_1(k3_subset_1(X3,X4),k1_zfmisc_1(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(X3))) )),
% 1.37/0.61    inference(superposition,[],[f68,f79])).
% 1.37/0.61  fof(f79,plain,(
% 1.37/0.61    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X1) = X1 | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 1.37/0.61    inference(cnf_transformation,[],[f47])).
% 1.37/0.61  fof(f47,plain,(
% 1.37/0.61    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X1) = X1 | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.37/0.61    inference(ennf_transformation,[],[f9])).
% 1.37/0.61  fof(f9,axiom,(
% 1.37/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X1) = X1)),
% 1.37/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k9_subset_1)).
% 1.37/0.61  fof(f68,plain,(
% 1.37/0.61    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.37/0.61    inference(cnf_transformation,[],[f33])).
% 1.37/0.61  fof(f33,plain,(
% 1.37/0.61    ! [X0,X1] : (! [X2] : (k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.37/0.61    inference(ennf_transformation,[],[f14])).
% 1.37/0.61  fof(f14,axiom,(
% 1.37/0.61    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))))),
% 1.37/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_subset_1)).
% 1.37/0.61  fof(f463,plain,(
% 1.37/0.61    spl2_29 | ~spl2_34),
% 1.37/0.61    inference(avatar_split_clause,[],[f458,f424,f354])).
% 1.37/0.61  fof(f354,plain,(
% 1.37/0.61    spl2_29 <=> r1_tarski(sK1,k2_pre_topc(sK0,sK1))),
% 1.37/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).
% 1.37/0.61  fof(f424,plain,(
% 1.37/0.61    spl2_34 <=> k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_pre_topc(sK0,sK1))),
% 1.37/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).
% 1.37/0.61  fof(f458,plain,(
% 1.37/0.61    r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | ~spl2_34),
% 1.37/0.61    inference(superposition,[],[f174,f426])).
% 1.37/0.61  fof(f426,plain,(
% 1.37/0.61    k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_pre_topc(sK0,sK1)) | ~spl2_34),
% 1.37/0.61    inference(avatar_component_clause,[],[f424])).
% 1.37/0.61  fof(f174,plain,(
% 1.37/0.61    ( ! [X0,X1] : (r1_tarski(X1,k2_xboole_0(X1,X0))) )),
% 1.37/0.61    inference(superposition,[],[f171,f65])).
% 1.37/0.61  fof(f65,plain,(
% 1.37/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.37/0.61    inference(cnf_transformation,[],[f1])).
% 1.37/0.61  fof(f1,axiom,(
% 1.37/0.61    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.37/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.37/0.61  fof(f171,plain,(
% 1.37/0.61    ( ! [X2,X3] : (r1_tarski(X2,k2_xboole_0(X3,X2))) )),
% 1.37/0.61    inference(forward_demodulation,[],[f170,f64])).
% 1.37/0.61  fof(f64,plain,(
% 1.37/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.37/0.61    inference(cnf_transformation,[],[f4])).
% 1.37/0.61  fof(f4,axiom,(
% 1.37/0.61    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.37/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 1.37/0.61  fof(f170,plain,(
% 1.37/0.61    ( ! [X2,X3] : (r1_tarski(X2,k2_xboole_0(X3,k4_xboole_0(X2,X3)))) )),
% 1.37/0.61    inference(resolution,[],[f76,f86])).
% 1.37/0.61  fof(f86,plain,(
% 1.37/0.61    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.37/0.61    inference(equality_resolution,[],[f83])).
% 1.37/0.61  fof(f83,plain,(
% 1.37/0.61    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.37/0.61    inference(cnf_transformation,[],[f55])).
% 1.37/0.61  fof(f55,plain,(
% 1.37/0.61    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.37/0.61    inference(flattening,[],[f54])).
% 1.37/0.61  fof(f54,plain,(
% 1.37/0.61    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.37/0.61    inference(nnf_transformation,[],[f2])).
% 1.37/0.61  fof(f2,axiom,(
% 1.37/0.61    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.37/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.37/0.61  fof(f76,plain,(
% 1.37/0.61    ( ! [X2,X0,X1] : (~r1_tarski(k4_xboole_0(X0,X1),X2) | r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 1.37/0.61    inference(cnf_transformation,[],[f44])).
% 1.37/0.61  fof(f44,plain,(
% 1.37/0.61    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 1.37/0.61    inference(ennf_transformation,[],[f5])).
% 1.37/0.61  fof(f5,axiom,(
% 1.37/0.61    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 1.37/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).
% 1.37/0.61  fof(f462,plain,(
% 1.37/0.61    ~spl2_27 | spl2_28 | ~spl2_14),
% 1.37/0.61    inference(avatar_split_clause,[],[f450,f201,f336,f332])).
% 1.37/0.61  fof(f201,plain,(
% 1.37/0.61    spl2_14 <=> k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)),
% 1.37/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 1.37/0.61  fof(f450,plain,(
% 1.37/0.61    sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~spl2_14),
% 1.37/0.61    inference(superposition,[],[f186,f203])).
% 1.37/0.61  fof(f203,plain,(
% 1.37/0.61    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~spl2_14),
% 1.37/0.61    inference(avatar_component_clause,[],[f201])).
% 1.37/0.61  fof(f186,plain,(
% 1.37/0.61    ( ! [X0,X1] : (k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.37/0.61    inference(duplicate_literal_removal,[],[f180])).
% 1.37/0.61  fof(f180,plain,(
% 1.37/0.61    ( ! [X0,X1] : (k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.37/0.61    inference(superposition,[],[f62,f63])).
% 1.37/0.61  fof(f63,plain,(
% 1.37/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.37/0.61    inference(cnf_transformation,[],[f30])).
% 1.37/0.61  fof(f30,plain,(
% 1.37/0.61    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.37/0.61    inference(ennf_transformation,[],[f6])).
% 1.37/0.61  fof(f6,axiom,(
% 1.37/0.61    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.37/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 1.37/0.61  fof(f62,plain,(
% 1.37/0.61    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.37/0.61    inference(cnf_transformation,[],[f29])).
% 1.37/0.61  fof(f29,plain,(
% 1.37/0.61    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.37/0.61    inference(ennf_transformation,[],[f10])).
% 1.37/0.61  fof(f10,axiom,(
% 1.37/0.61    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 1.37/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 1.37/0.61  fof(f455,plain,(
% 1.37/0.61    spl2_23 | ~spl2_14),
% 1.37/0.61    inference(avatar_split_clause,[],[f453,f201,f305])).
% 1.37/0.61  fof(f305,plain,(
% 1.37/0.61    spl2_23 <=> k2_xboole_0(sK1,k2_pre_topc(sK0,sK1)) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 1.37/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).
% 1.37/0.61  fof(f453,plain,(
% 1.37/0.61    k2_xboole_0(sK1,k2_pre_topc(sK0,sK1)) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl2_14),
% 1.37/0.61    inference(superposition,[],[f64,f203])).
% 1.37/0.61  fof(f448,plain,(
% 1.37/0.61    spl2_14 | ~spl2_2 | ~spl2_13),
% 1.37/0.61    inference(avatar_split_clause,[],[f447,f197,f93,f201])).
% 1.37/0.61  fof(f93,plain,(
% 1.37/0.61    spl2_2 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)),
% 1.37/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 1.37/0.61  fof(f197,plain,(
% 1.37/0.61    spl2_13 <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.37/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 1.37/0.61  fof(f447,plain,(
% 1.37/0.61    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | (~spl2_2 | ~spl2_13)),
% 1.37/0.61    inference(subsumption_resolution,[],[f444,f198])).
% 1.37/0.61  fof(f198,plain,(
% 1.37/0.61    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_13),
% 1.37/0.61    inference(avatar_component_clause,[],[f197])).
% 1.37/0.61  fof(f444,plain,(
% 1.37/0.61    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_2),
% 1.37/0.61    inference(superposition,[],[f61,f94])).
% 1.37/0.61  fof(f94,plain,(
% 1.37/0.61    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~spl2_2),
% 1.37/0.61    inference(avatar_component_clause,[],[f93])).
% 1.37/0.61  fof(f442,plain,(
% 1.37/0.61    spl2_2 | ~spl2_3 | ~spl2_4 | ~spl2_31),
% 1.37/0.61    inference(avatar_contradiction_clause,[],[f441])).
% 1.37/0.61  fof(f441,plain,(
% 1.37/0.61    $false | (spl2_2 | ~spl2_3 | ~spl2_4 | ~spl2_31)),
% 1.37/0.61    inference(subsumption_resolution,[],[f440,f106])).
% 1.37/0.61  fof(f440,plain,(
% 1.37/0.61    ~l1_pre_topc(sK0) | (spl2_2 | ~spl2_3 | ~spl2_31)),
% 1.37/0.61    inference(subsumption_resolution,[],[f439,f101])).
% 1.37/0.61  fof(f439,plain,(
% 1.37/0.61    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (spl2_2 | ~spl2_31)),
% 1.37/0.61    inference(subsumption_resolution,[],[f436,f95])).
% 1.37/0.61  fof(f95,plain,(
% 1.37/0.61    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | spl2_2),
% 1.37/0.61    inference(avatar_component_clause,[],[f93])).
% 1.37/0.61  fof(f436,plain,(
% 1.37/0.61    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl2_31),
% 1.37/0.61    inference(superposition,[],[f66,f384])).
% 1.37/0.61  fof(f384,plain,(
% 1.37/0.61    sK1 = k1_tops_1(sK0,sK1) | ~spl2_31),
% 1.37/0.61    inference(avatar_component_clause,[],[f382])).
% 1.37/0.61  fof(f66,plain,(
% 1.37/0.61    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.37/0.61    inference(cnf_transformation,[],[f31])).
% 1.37/0.61  fof(f31,plain,(
% 1.37/0.61    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.37/0.61    inference(ennf_transformation,[],[f20])).
% 1.37/0.61  fof(f20,axiom,(
% 1.37/0.61    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 1.37/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).
% 1.37/0.61  fof(f430,plain,(
% 1.37/0.61    spl2_34 | ~spl2_3 | ~spl2_4 | ~spl2_23),
% 1.37/0.61    inference(avatar_split_clause,[],[f429,f305,f104,f99,f424])).
% 1.37/0.61  fof(f429,plain,(
% 1.37/0.61    k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_pre_topc(sK0,sK1)) | (~spl2_3 | ~spl2_4 | ~spl2_23)),
% 1.37/0.61    inference(subsumption_resolution,[],[f428,f106])).
% 1.37/0.61  fof(f428,plain,(
% 1.37/0.61    k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_pre_topc(sK0,sK1)) | ~l1_pre_topc(sK0) | (~spl2_3 | ~spl2_23)),
% 1.37/0.61    inference(subsumption_resolution,[],[f420,f101])).
% 1.37/0.61  fof(f420,plain,(
% 1.37/0.61    k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_pre_topc(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl2_23),
% 1.37/0.61    inference(superposition,[],[f307,f281])).
% 1.37/0.61  fof(f281,plain,(
% 1.37/0.61    ( ! [X2,X3] : (k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2)) )),
% 1.37/0.61    inference(subsumption_resolution,[],[f280,f71])).
% 1.37/0.61  fof(f71,plain,(
% 1.37/0.61    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.37/0.61    inference(cnf_transformation,[],[f38])).
% 1.37/0.61  fof(f38,plain,(
% 1.37/0.61    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 1.37/0.61    inference(flattening,[],[f37])).
% 1.37/0.61  fof(f37,plain,(
% 1.37/0.61    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 1.37/0.61    inference(ennf_transformation,[],[f18])).
% 1.37/0.61  fof(f18,axiom,(
% 1.37/0.61    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 1.37/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 1.37/0.61  fof(f280,plain,(
% 1.37/0.61    ( ! [X2,X3] : (k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2) | ~m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))) )),
% 1.37/0.61    inference(duplicate_literal_removal,[],[f277])).
% 1.37/0.61  fof(f277,plain,(
% 1.37/0.61    ( ! [X2,X3] : (k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2) | ~m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) )),
% 1.37/0.61    inference(superposition,[],[f70,f78])).
% 1.37/0.61  fof(f78,plain,(
% 1.37/0.61    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.37/0.61    inference(cnf_transformation,[],[f46])).
% 1.37/0.61  fof(f46,plain,(
% 1.37/0.61    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.37/0.61    inference(flattening,[],[f45])).
% 1.37/0.61  fof(f45,plain,(
% 1.37/0.61    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 1.37/0.61    inference(ennf_transformation,[],[f11])).
% 1.37/0.61  fof(f11,axiom,(
% 1.37/0.61    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 1.37/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 1.37/0.61  fof(f70,plain,(
% 1.37/0.61    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.37/0.61    inference(cnf_transformation,[],[f36])).
% 1.37/0.61  fof(f36,plain,(
% 1.37/0.61    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.37/0.61    inference(ennf_transformation,[],[f22])).
% 1.37/0.61  fof(f22,axiom,(
% 1.37/0.61    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 1.37/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).
% 1.37/0.61  fof(f307,plain,(
% 1.37/0.61    k2_xboole_0(sK1,k2_pre_topc(sK0,sK1)) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl2_23),
% 1.37/0.61    inference(avatar_component_clause,[],[f305])).
% 1.37/0.61  fof(f385,plain,(
% 1.37/0.61    ~spl2_1 | spl2_31 | ~spl2_3 | ~spl2_4 | ~spl2_9),
% 1.37/0.61    inference(avatar_split_clause,[],[f380,f124,f104,f99,f382,f89])).
% 1.37/0.61  fof(f89,plain,(
% 1.37/0.61    spl2_1 <=> v3_pre_topc(sK1,sK0)),
% 1.37/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 1.37/0.61  fof(f124,plain,(
% 1.37/0.61    spl2_9 <=> ! [X1,X3] : (k1_tops_1(X1,X3) = X3 | ~l1_pre_topc(X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~v3_pre_topc(X3,X1))),
% 1.37/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 1.37/0.61  fof(f380,plain,(
% 1.37/0.61    sK1 = k1_tops_1(sK0,sK1) | ~v3_pre_topc(sK1,sK0) | (~spl2_3 | ~spl2_4 | ~spl2_9)),
% 1.37/0.61    inference(subsumption_resolution,[],[f250,f106])).
% 1.37/0.61  fof(f250,plain,(
% 1.37/0.61    ~l1_pre_topc(sK0) | sK1 = k1_tops_1(sK0,sK1) | ~v3_pre_topc(sK1,sK0) | (~spl2_3 | ~spl2_9)),
% 1.37/0.61    inference(resolution,[],[f125,f101])).
% 1.37/0.62  fof(f125,plain,(
% 1.37/0.62    ( ! [X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1)) ) | ~spl2_9),
% 1.37/0.62    inference(avatar_component_clause,[],[f124])).
% 1.37/0.62  fof(f357,plain,(
% 1.37/0.62    ~spl2_29 | spl2_27),
% 1.37/0.62    inference(avatar_split_clause,[],[f352,f332,f354])).
% 1.37/0.62  fof(f352,plain,(
% 1.37/0.62    ~r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | spl2_27),
% 1.37/0.62    inference(resolution,[],[f334,f81])).
% 1.37/0.62  fof(f81,plain,(
% 1.37/0.62    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.37/0.62    inference(cnf_transformation,[],[f53])).
% 1.37/0.62  fof(f53,plain,(
% 1.37/0.62    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.37/0.62    inference(nnf_transformation,[],[f16])).
% 1.37/0.62  fof(f16,axiom,(
% 1.37/0.62    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.37/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.37/0.62  fof(f334,plain,(
% 1.37/0.62    ~m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | spl2_27),
% 1.37/0.62    inference(avatar_component_clause,[],[f332])).
% 1.37/0.62  fof(f313,plain,(
% 1.37/0.62    spl2_24 | ~spl2_14),
% 1.37/0.62    inference(avatar_split_clause,[],[f298,f201,f310])).
% 1.37/0.62  fof(f298,plain,(
% 1.37/0.62    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~spl2_14),
% 1.37/0.62    inference(superposition,[],[f127,f203])).
% 1.37/0.62  fof(f243,plain,(
% 1.37/0.62    spl2_17 | ~spl2_3 | ~spl2_4 | ~spl2_5),
% 1.37/0.62    inference(avatar_split_clause,[],[f238,f109,f104,f99,f240])).
% 1.37/0.62  fof(f240,plain,(
% 1.37/0.62    spl2_17 <=> v3_pre_topc(k1_tops_1(sK0,sK1),sK0)),
% 1.37/0.62    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 1.37/0.62  fof(f109,plain,(
% 1.37/0.62    spl2_5 <=> v2_pre_topc(sK0)),
% 1.37/0.62    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 1.37/0.62  fof(f238,plain,(
% 1.37/0.62    v3_pre_topc(k1_tops_1(sK0,sK1),sK0) | (~spl2_3 | ~spl2_4 | ~spl2_5)),
% 1.37/0.62    inference(subsumption_resolution,[],[f237,f111])).
% 1.37/0.62  fof(f111,plain,(
% 1.37/0.62    v2_pre_topc(sK0) | ~spl2_5),
% 1.37/0.62    inference(avatar_component_clause,[],[f109])).
% 1.37/0.62  fof(f237,plain,(
% 1.37/0.62    v3_pre_topc(k1_tops_1(sK0,sK1),sK0) | ~v2_pre_topc(sK0) | (~spl2_3 | ~spl2_4)),
% 1.37/0.62    inference(subsumption_resolution,[],[f227,f106])).
% 1.37/0.62  fof(f227,plain,(
% 1.37/0.62    v3_pre_topc(k1_tops_1(sK0,sK1),sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~spl2_3),
% 1.37/0.62    inference(resolution,[],[f72,f101])).
% 1.37/0.62  fof(f72,plain,(
% 1.37/0.62    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(k1_tops_1(X0,X1),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.37/0.62    inference(cnf_transformation,[],[f40])).
% 1.37/0.62  fof(f40,plain,(
% 1.37/0.62    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.37/0.62    inference(flattening,[],[f39])).
% 1.37/0.62  fof(f39,plain,(
% 1.37/0.62    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.37/0.62    inference(ennf_transformation,[],[f19])).
% 1.37/0.62  fof(f19,axiom,(
% 1.37/0.62    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 1.37/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).
% 1.37/0.62  fof(f213,plain,(
% 1.37/0.62    ~spl2_3 | ~spl2_4 | spl2_13),
% 1.37/0.62    inference(avatar_contradiction_clause,[],[f212])).
% 1.37/0.62  fof(f212,plain,(
% 1.37/0.62    $false | (~spl2_3 | ~spl2_4 | spl2_13)),
% 1.37/0.62    inference(subsumption_resolution,[],[f211,f106])).
% 1.37/0.62  fof(f211,plain,(
% 1.37/0.62    ~l1_pre_topc(sK0) | (~spl2_3 | spl2_13)),
% 1.37/0.62    inference(subsumption_resolution,[],[f208,f101])).
% 1.37/0.62  fof(f208,plain,(
% 1.37/0.62    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl2_13),
% 1.37/0.62    inference(resolution,[],[f199,f69])).
% 1.37/0.62  fof(f69,plain,(
% 1.37/0.62    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.37/0.62    inference(cnf_transformation,[],[f35])).
% 1.37/0.62  fof(f35,plain,(
% 1.37/0.62    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 1.37/0.62    inference(flattening,[],[f34])).
% 1.37/0.62  fof(f34,plain,(
% 1.37/0.62    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 1.37/0.62    inference(ennf_transformation,[],[f17])).
% 1.37/0.62  fof(f17,axiom,(
% 1.37/0.62    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 1.37/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 1.37/0.62  fof(f199,plain,(
% 1.37/0.62    ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl2_13),
% 1.37/0.62    inference(avatar_component_clause,[],[f197])).
% 1.37/0.62  fof(f163,plain,(
% 1.37/0.62    ~spl2_4 | ~spl2_5 | ~spl2_8),
% 1.37/0.62    inference(avatar_contradiction_clause,[],[f158])).
% 1.37/0.62  fof(f158,plain,(
% 1.37/0.62    $false | (~spl2_4 | ~spl2_5 | ~spl2_8)),
% 1.37/0.62    inference(unit_resulting_resolution,[],[f106,f111,f127,f122])).
% 1.37/0.62  fof(f122,plain,(
% 1.37/0.62    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0)) ) | ~spl2_8),
% 1.37/0.62    inference(avatar_component_clause,[],[f121])).
% 1.37/0.62  fof(f121,plain,(
% 1.37/0.62    spl2_8 <=> ! [X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0))),
% 1.37/0.62    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 1.37/0.62  fof(f126,plain,(
% 1.37/0.62    spl2_8 | spl2_9),
% 1.37/0.62    inference(avatar_split_clause,[],[f73,f124,f121])).
% 1.37/0.62  fof(f73,plain,(
% 1.37/0.62    ( ! [X2,X0,X3,X1] : (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.37/0.62    inference(cnf_transformation,[],[f42])).
% 1.37/0.62  fof(f42,plain,(
% 1.37/0.62    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.37/0.62    inference(flattening,[],[f41])).
% 1.37/0.62  fof(f41,plain,(
% 1.37/0.62    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.37/0.62    inference(ennf_transformation,[],[f21])).
% 1.37/0.62  fof(f21,axiom,(
% 1.37/0.62    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((k1_tops_1(X0,X2) = X2 => v3_pre_topc(X2,X0)) & (v3_pre_topc(X3,X1) => k1_tops_1(X1,X3) = X3))))))),
% 1.37/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tops_1)).
% 1.37/0.62  fof(f112,plain,(
% 1.37/0.62    spl2_5),
% 1.37/0.62    inference(avatar_split_clause,[],[f56,f109])).
% 1.37/0.62  fof(f56,plain,(
% 1.37/0.62    v2_pre_topc(sK0)),
% 1.37/0.62    inference(cnf_transformation,[],[f52])).
% 1.37/0.62  fof(f52,plain,(
% 1.37/0.62    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 1.37/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f49,f51,f50])).
% 1.37/0.62  fof(f50,plain,(
% 1.37/0.62    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | ~v3_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 1.37/0.62    introduced(choice_axiom,[])).
% 1.37/0.62  fof(f51,plain,(
% 1.37/0.62    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | ~v3_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.37/0.62    introduced(choice_axiom,[])).
% 1.37/0.62  fof(f49,plain,(
% 1.37/0.62    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.37/0.62    inference(flattening,[],[f48])).
% 1.37/0.62  fof(f48,plain,(
% 1.37/0.62    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.37/0.62    inference(nnf_transformation,[],[f27])).
% 1.37/0.62  fof(f27,plain,(
% 1.37/0.62    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.37/0.62    inference(flattening,[],[f26])).
% 1.37/0.62  fof(f26,plain,(
% 1.37/0.62    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 1.37/0.62    inference(ennf_transformation,[],[f25])).
% 1.37/0.62  fof(f25,negated_conjecture,(
% 1.37/0.62    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 1.37/0.62    inference(negated_conjecture,[],[f24])).
% 1.37/0.62  fof(f24,conjecture,(
% 1.37/0.62    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 1.37/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_1)).
% 1.37/0.62  fof(f107,plain,(
% 1.37/0.62    spl2_4),
% 1.37/0.62    inference(avatar_split_clause,[],[f57,f104])).
% 1.37/0.62  fof(f57,plain,(
% 1.37/0.62    l1_pre_topc(sK0)),
% 1.37/0.62    inference(cnf_transformation,[],[f52])).
% 1.37/0.62  fof(f102,plain,(
% 1.37/0.62    spl2_3),
% 1.37/0.62    inference(avatar_split_clause,[],[f58,f99])).
% 1.37/0.62  fof(f58,plain,(
% 1.37/0.62    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.37/0.62    inference(cnf_transformation,[],[f52])).
% 1.37/0.62  fof(f97,plain,(
% 1.37/0.62    spl2_1 | spl2_2),
% 1.37/0.62    inference(avatar_split_clause,[],[f59,f93,f89])).
% 1.37/0.62  fof(f59,plain,(
% 1.37/0.62    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)),
% 1.37/0.62    inference(cnf_transformation,[],[f52])).
% 1.37/0.62  fof(f96,plain,(
% 1.37/0.62    ~spl2_1 | ~spl2_2),
% 1.37/0.62    inference(avatar_split_clause,[],[f60,f93,f89])).
% 1.37/0.62  fof(f60,plain,(
% 1.37/0.62    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)),
% 1.37/0.62    inference(cnf_transformation,[],[f52])).
% 1.37/0.62  % SZS output end Proof for theBenchmark
% 1.37/0.62  % (6332)------------------------------
% 1.37/0.62  % (6332)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.62  % (6332)Termination reason: Refutation
% 1.37/0.62  
% 1.37/0.62  % (6332)Memory used [KB]: 6652
% 1.37/0.62  % (6332)Time elapsed: 0.177 s
% 1.37/0.62  % (6332)------------------------------
% 1.37/0.62  % (6332)------------------------------
% 1.37/0.62  % (6310)Success in time 0.249 s
%------------------------------------------------------------------------------
