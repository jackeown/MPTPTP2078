%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:23 EST 2020

% Result     : Theorem 7.01s
% Output     : Refutation 7.01s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 421 expanded)
%              Number of leaves         :   24 ( 143 expanded)
%              Depth                    :   13
%              Number of atoms          :  315 (1160 expanded)
%              Number of equality atoms :   58 ( 217 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11256,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f65,f70,f75,f80,f85,f276,f4663,f7021,f10522,f11244])).

fof(f11244,plain,
    ( spl4_3
    | ~ spl4_29 ),
    inference(avatar_contradiction_clause,[],[f11243])).

fof(f11243,plain,
    ( $false
    | spl4_3
    | ~ spl4_29 ),
    inference(subsumption_resolution,[],[f11242,f59])).

fof(f59,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
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

fof(f11242,plain,
    ( ~ r1_tarski(sK1,sK1)
    | spl4_3
    | ~ spl4_29 ),
    inference(forward_demodulation,[],[f11203,f362])).

fof(f362,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(backward_demodulation,[],[f140,f361])).

fof(f361,plain,(
    ! [X0] : k1_xboole_0 = k6_subset_1(X0,X0) ),
    inference(forward_demodulation,[],[f344,f207])).

fof(f207,plain,(
    k1_xboole_0 = k2_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f206,f91])).

fof(f91,plain,(
    ! [X0] : k1_xboole_0 = k6_subset_1(k1_xboole_0,X0) ),
    inference(unit_resulting_resolution,[],[f39,f55,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f55,plain,(
    ! [X0,X1] : r1_tarski(k6_subset_1(X0,X1),X0) ),
    inference(definition_unfolding,[],[f41,f42])).

fof(f42,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f41,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f39,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f206,plain,(
    ! [X0] : k1_xboole_0 = k2_xboole_0(k6_subset_1(k1_xboole_0,X0),k1_xboole_0) ),
    inference(forward_demodulation,[],[f199,f91])).

fof(f199,plain,(
    ! [X0,X1] : k1_xboole_0 = k2_xboole_0(k6_subset_1(k1_xboole_0,X0),k6_subset_1(k1_xboole_0,X1)) ),
    inference(unit_resulting_resolution,[],[f55,f55,f39,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,sK3(X0,X1,X2))
      | k2_xboole_0(X0,X2) = X1
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X2) = X1
      | ( ~ r1_tarski(X1,sK3(X0,X1,X2))
        & r1_tarski(X2,sK3(X0,X1,X2))
        & r1_tarski(X0,sK3(X0,X1,X2)) )
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f27,f32])).

fof(f32,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_tarski(X1,X3)
          & r1_tarski(X2,X3)
          & r1_tarski(X0,X3) )
     => ( ~ r1_tarski(X1,sK3(X0,X1,X2))
        & r1_tarski(X2,sK3(X0,X1,X2))
        & r1_tarski(X0,sK3(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X2) = X1
      | ? [X3] :
          ( ~ r1_tarski(X1,X3)
          & r1_tarski(X2,X3)
          & r1_tarski(X0,X3) )
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X2) = X1
      | ? [X3] :
          ( ~ r1_tarski(X1,X3)
          & r1_tarski(X2,X3)
          & r1_tarski(X0,X3) )
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ( r1_tarski(X2,X3)
              & r1_tarski(X0,X3) )
           => r1_tarski(X1,X3) )
        & r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => k2_xboole_0(X0,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_xboole_1)).

fof(f344,plain,(
    ! [X0] : k6_subset_1(X0,X0) = k2_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f39,f39,f152,f54])).

fof(f152,plain,(
    ! [X0,X1] : r1_tarski(k6_subset_1(X0,X0),X1) ),
    inference(unit_resulting_resolution,[],[f40,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k6_subset_1(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(definition_unfolding,[],[f48,f42])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f40,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f140,plain,(
    ! [X0] : k2_xboole_0(X0,k6_subset_1(X0,X0)) = X0 ),
    inference(unit_resulting_resolution,[],[f59,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,k6_subset_1(X1,X0)) = X1 ) ),
    inference(definition_unfolding,[],[f43,f42])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_xboole_1)).

fof(f11203,plain,
    ( ~ r1_tarski(k2_xboole_0(sK1,k1_xboole_0),sK1)
    | spl4_3
    | ~ spl4_29 ),
    inference(superposition,[],[f868,f10521])).

fof(f10521,plain,
    ( k1_xboole_0 = k6_subset_1(sK0,sK1)
    | ~ spl4_29 ),
    inference(avatar_component_clause,[],[f10519])).

fof(f10519,plain,
    ( spl4_29
  <=> k1_xboole_0 = k6_subset_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).

fof(f868,plain,
    ( ! [X0] : ~ r1_tarski(k2_xboole_0(X0,k6_subset_1(sK0,X0)),sK1)
    | spl4_3 ),
    inference(unit_resulting_resolution,[],[f74,f161,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f161,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X1,k6_subset_1(X0,X1))) ),
    inference(unit_resulting_resolution,[],[f59,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k6_subset_1(X0,X1),X2)
      | r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(definition_unfolding,[],[f49,f42])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f74,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl4_3
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f10522,plain,
    ( spl4_29
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_22
    | ~ spl4_25 ),
    inference(avatar_split_clause,[],[f10430,f7018,f4660,f77,f67,f62,f10519])).

fof(f62,plain,
    ( spl4_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f67,plain,
    ( spl4_2
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f77,plain,
    ( spl4_4
  <=> r1_tarski(sK0,k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f4660,plain,
    ( spl4_22
  <=> k1_xboole_0 = k9_relat_1(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f7018,plain,
    ( spl4_25
  <=> k1_xboole_0 = k10_relat_1(sK2,k6_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f10430,plain,
    ( k1_xboole_0 = k6_subset_1(sK0,sK1)
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_22
    | ~ spl4_25 ),
    inference(forward_demodulation,[],[f10426,f4662])).

fof(f4662,plain,
    ( k1_xboole_0 = k9_relat_1(sK2,k1_xboole_0)
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f4660])).

fof(f10426,plain,
    ( k6_subset_1(sK0,sK1) = k9_relat_1(sK2,k1_xboole_0)
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_25 ),
    inference(superposition,[],[f254,f7020])).

fof(f7020,plain,
    ( k1_xboole_0 = k10_relat_1(sK2,k6_subset_1(sK0,sK1))
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f7018])).

fof(f254,plain,
    ( ! [X0] : k6_subset_1(sK0,X0) = k9_relat_1(sK2,k10_relat_1(sK2,k6_subset_1(sK0,X0)))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f64,f69,f127,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

fof(f127,plain,
    ( ! [X0] : r1_tarski(k6_subset_1(sK0,X0),k2_relat_1(sK2))
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f55,f79,f51])).

fof(f79,plain,
    ( r1_tarski(sK0,k2_relat_1(sK2))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f77])).

fof(f69,plain,
    ( v1_funct_1(sK2)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f67])).

fof(f64,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f62])).

fof(f7021,plain,
    ( spl4_25
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f3817,f82,f67,f62,f7018])).

fof(f82,plain,
    ( spl4_5
  <=> r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f3817,plain,
    ( k1_xboole_0 = k10_relat_1(sK2,k6_subset_1(sK0,sK1))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f3728,f1031])).

fof(f1031,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(unit_resulting_resolution,[],[f39,f213])).

fof(f213,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X2,X3)
      | k2_xboole_0(X2,X3) = X3 ) ),
    inference(subsumption_resolution,[],[f204,f59])).

fof(f204,plain,(
    ! [X2,X3] :
      ( k2_xboole_0(X2,X3) = X3
      | ~ r1_tarski(X3,X3)
      | ~ r1_tarski(X2,X3) ) ),
    inference(duplicate_literal_removal,[],[f201])).

fof(f201,plain,(
    ! [X2,X3] :
      ( k2_xboole_0(X2,X3) = X3
      | ~ r1_tarski(X3,X3)
      | ~ r1_tarski(X2,X3)
      | k2_xboole_0(X2,X3) = X3
      | ~ r1_tarski(X3,X3)
      | ~ r1_tarski(X2,X3) ) ),
    inference(resolution,[],[f54,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,sK3(X0,X1,X2))
      | k2_xboole_0(X0,X2) = X1
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f3728,plain,
    ( k2_xboole_0(k1_xboole_0,k1_xboole_0) = k10_relat_1(sK2,k6_subset_1(sK0,sK1))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_5 ),
    inference(unit_resulting_resolution,[],[f39,f39,f522,f54])).

fof(f522,plain,
    ( ! [X0] : r1_tarski(k10_relat_1(sK2,k6_subset_1(sK0,sK1)),X0)
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f510,f180])).

fof(f180,plain,
    ( ! [X0,X1] : k10_relat_1(sK2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1))
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f64,f69,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_funct_1)).

fof(f510,plain,
    ( ! [X0] : r1_tarski(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),X0)
    | ~ spl4_5 ),
    inference(unit_resulting_resolution,[],[f112,f57])).

fof(f112,plain,
    ( ! [X0] : r1_tarski(k10_relat_1(sK2,sK0),k2_xboole_0(k10_relat_1(sK2,sK1),X0))
    | ~ spl4_5 ),
    inference(unit_resulting_resolution,[],[f84,f40,f51])).

fof(f84,plain,
    ( r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f82])).

fof(f4663,plain,
    ( spl4_22
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f4653,f273,f67,f62,f4660])).

fof(f273,plain,
    ( spl4_9
  <=> k1_xboole_0 = k9_relat_1(sK2,k10_relat_1(sK2,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f4653,plain,
    ( k1_xboole_0 = k9_relat_1(sK2,k1_xboole_0)
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_9 ),
    inference(backward_demodulation,[],[f275,f4652])).

fof(f4652,plain,
    ( k1_xboole_0 = k10_relat_1(sK2,k1_xboole_0)
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f4620,f361])).

fof(f4620,plain,
    ( ! [X1] : k1_xboole_0 = k10_relat_1(sK2,k6_subset_1(X1,X1))
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(superposition,[],[f361,f180])).

fof(f275,plain,
    ( k1_xboole_0 = k9_relat_1(sK2,k10_relat_1(sK2,k1_xboole_0))
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f273])).

fof(f276,plain,
    ( spl4_9
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f168,f67,f62,f273])).

fof(f168,plain,
    ( k1_xboole_0 = k9_relat_1(sK2,k10_relat_1(sK2,k1_xboole_0))
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f64,f69,f39,f44])).

fof(f85,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f36,f82])).

fof(f36,plain,(
    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ~ r1_tarski(sK0,sK1)
    & r1_tarski(sK0,k2_relat_1(sK2))
    & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f28])).

fof(f28,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,X1)
        & r1_tarski(X0,k2_relat_1(X2))
        & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(sK0,sK1)
      & r1_tarski(sK0,k2_relat_1(sK2))
      & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_tarski(X0,k2_relat_1(X2))
      & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_tarski(X0,k2_relat_1(X2))
      & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( r1_tarski(X0,k2_relat_1(X2))
            & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) )
         => r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(X0,k2_relat_1(X2))
          & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_funct_1)).

fof(f80,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f37,f77])).

fof(f37,plain,(
    r1_tarski(sK0,k2_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f29])).

fof(f75,plain,(
    ~ spl4_3 ),
    inference(avatar_split_clause,[],[f38,f72])).

fof(f38,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f70,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f35,f67])).

fof(f35,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f65,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f34,f62])).

fof(f34,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:26:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.54  % (3607)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.54  % (3599)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.59  % (3595)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.59  % (3593)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.59  % (3596)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.60  % (3598)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.60  % (3600)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.61  % (3597)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.61  % (3615)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.61  % (3594)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.61  % (3619)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.61  % (3593)Refutation not found, incomplete strategy% (3593)------------------------------
% 0.21/0.61  % (3593)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.61  % (3593)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.61  
% 0.21/0.61  % (3593)Memory used [KB]: 1663
% 0.21/0.61  % (3593)Time elapsed: 0.165 s
% 0.21/0.61  % (3593)------------------------------
% 0.21/0.61  % (3593)------------------------------
% 0.21/0.62  % (3592)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.62  % (3603)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.62  % (3614)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.91/0.63  % (3617)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.91/0.63  % (3611)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.91/0.63  % (3620)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.91/0.63  % (3601)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.91/0.63  % (3621)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.91/0.64  % (3605)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.91/0.64  % (3612)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.91/0.64  % (3606)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 2.17/0.64  % (3613)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 2.17/0.64  % (3604)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 2.17/0.64  % (3608)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 2.17/0.65  % (3609)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 2.17/0.65  % (3618)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 2.29/0.66  % (3616)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 2.29/0.67  % (3602)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 2.29/0.68  % (3610)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 3.02/0.79  % (3592)Refutation not found, incomplete strategy% (3592)------------------------------
% 3.02/0.79  % (3592)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.02/0.79  % (3592)Termination reason: Refutation not found, incomplete strategy
% 3.02/0.79  
% 3.02/0.79  % (3592)Memory used [KB]: 1663
% 3.02/0.79  % (3592)Time elapsed: 0.355 s
% 3.02/0.79  % (3592)------------------------------
% 3.02/0.79  % (3592)------------------------------
% 3.02/0.80  % (3595)Refutation not found, incomplete strategy% (3595)------------------------------
% 3.02/0.80  % (3595)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.02/0.80  % (3595)Termination reason: Refutation not found, incomplete strategy
% 3.02/0.80  
% 3.02/0.80  % (3595)Memory used [KB]: 6140
% 3.02/0.80  % (3595)Time elapsed: 0.349 s
% 3.02/0.80  % (3595)------------------------------
% 3.02/0.80  % (3595)------------------------------
% 3.02/0.80  % (3654)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 3.66/0.85  % (3594)Time limit reached!
% 3.66/0.85  % (3594)------------------------------
% 3.66/0.85  % (3594)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.66/0.85  % (3594)Termination reason: Time limit
% 3.66/0.85  
% 3.66/0.85  % (3594)Memory used [KB]: 6524
% 3.66/0.85  % (3594)Time elapsed: 0.416 s
% 3.66/0.85  % (3594)------------------------------
% 3.66/0.85  % (3594)------------------------------
% 3.66/0.85  % (3616)Time limit reached!
% 3.66/0.85  % (3616)------------------------------
% 3.66/0.85  % (3616)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.66/0.85  % (3616)Termination reason: Time limit
% 3.66/0.85  % (3616)Termination phase: Saturation
% 3.66/0.85  
% 3.66/0.85  % (3616)Memory used [KB]: 12665
% 3.66/0.85  % (3616)Time elapsed: 0.400 s
% 3.66/0.85  % (3616)------------------------------
% 3.66/0.85  % (3616)------------------------------
% 4.00/0.89  % (3686)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 4.00/0.92  % (3692)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 4.00/0.92  % (3692)Refutation not found, incomplete strategy% (3692)------------------------------
% 4.00/0.92  % (3692)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.00/0.92  % (3692)Termination reason: Refutation not found, incomplete strategy
% 4.00/0.92  
% 4.00/0.92  % (3692)Memory used [KB]: 6140
% 4.00/0.92  % (3692)Time elapsed: 0.073 s
% 4.00/0.92  % (3692)------------------------------
% 4.00/0.92  % (3692)------------------------------
% 4.43/0.95  % (3606)Time limit reached!
% 4.43/0.95  % (3606)------------------------------
% 4.43/0.95  % (3606)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.43/0.96  % (3598)Time limit reached!
% 4.43/0.96  % (3598)------------------------------
% 4.43/0.96  % (3598)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.43/0.96  % (3606)Termination reason: Time limit
% 4.43/0.96  
% 4.43/0.96  % (3606)Memory used [KB]: 4221
% 4.43/0.96  % (3606)Time elapsed: 0.525 s
% 4.43/0.96  % (3606)------------------------------
% 4.43/0.96  % (3606)------------------------------
% 4.54/0.96  % (3598)Termination reason: Time limit
% 4.54/0.96  
% 4.54/0.96  % (3598)Memory used [KB]: 14200
% 4.54/0.96  % (3598)Time elapsed: 0.527 s
% 4.54/0.96  % (3598)------------------------------
% 4.54/0.96  % (3598)------------------------------
% 4.54/0.96  % (3621)Time limit reached!
% 4.54/0.96  % (3621)------------------------------
% 4.54/0.96  % (3621)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.54/0.96  % (3621)Termination reason: Time limit
% 4.54/0.96  
% 4.54/0.96  % (3621)Memory used [KB]: 1918
% 4.54/0.96  % (3621)Time elapsed: 0.532 s
% 4.54/0.96  % (3621)------------------------------
% 4.54/0.96  % (3621)------------------------------
% 4.54/0.98  % (3714)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 4.54/0.98  % (3711)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 5.15/1.06  % (3758)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 5.15/1.07  % (3780)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 5.15/1.09  % (3785)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 5.15/1.09  % (3782)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 5.15/1.13  % (3599)Time limit reached!
% 5.15/1.13  % (3599)------------------------------
% 5.15/1.13  % (3599)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.15/1.13  % (3599)Termination reason: Time limit
% 5.15/1.13  % (3599)Termination phase: Saturation
% 5.15/1.13  
% 5.15/1.13  % (3599)Memory used [KB]: 9083
% 5.15/1.13  % (3599)Time elapsed: 0.600 s
% 5.15/1.13  % (3599)------------------------------
% 5.15/1.13  % (3599)------------------------------
% 6.52/1.24  % (3836)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_4 on theBenchmark
% 7.01/1.27  % (3612)Refutation found. Thanks to Tanya!
% 7.01/1.27  % SZS status Theorem for theBenchmark
% 7.01/1.28  % SZS output start Proof for theBenchmark
% 7.01/1.28  fof(f11256,plain,(
% 7.01/1.28    $false),
% 7.01/1.28    inference(avatar_sat_refutation,[],[f65,f70,f75,f80,f85,f276,f4663,f7021,f10522,f11244])).
% 7.01/1.28  fof(f11244,plain,(
% 7.01/1.28    spl4_3 | ~spl4_29),
% 7.01/1.28    inference(avatar_contradiction_clause,[],[f11243])).
% 7.01/1.28  fof(f11243,plain,(
% 7.01/1.28    $false | (spl4_3 | ~spl4_29)),
% 7.01/1.28    inference(subsumption_resolution,[],[f11242,f59])).
% 7.01/1.28  fof(f59,plain,(
% 7.01/1.28    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.01/1.28    inference(equality_resolution,[],[f46])).
% 7.01/1.28  fof(f46,plain,(
% 7.01/1.28    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 7.01/1.28    inference(cnf_transformation,[],[f31])).
% 7.01/1.28  fof(f31,plain,(
% 7.01/1.28    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.01/1.28    inference(flattening,[],[f30])).
% 7.01/1.28  fof(f30,plain,(
% 7.01/1.28    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.01/1.28    inference(nnf_transformation,[],[f1])).
% 7.01/1.28  fof(f1,axiom,(
% 7.01/1.28    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.01/1.28    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 7.01/1.28  fof(f11242,plain,(
% 7.01/1.28    ~r1_tarski(sK1,sK1) | (spl4_3 | ~spl4_29)),
% 7.01/1.28    inference(forward_demodulation,[],[f11203,f362])).
% 7.01/1.28  fof(f362,plain,(
% 7.01/1.28    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 7.01/1.28    inference(backward_demodulation,[],[f140,f361])).
% 7.01/1.28  fof(f361,plain,(
% 7.01/1.28    ( ! [X0] : (k1_xboole_0 = k6_subset_1(X0,X0)) )),
% 7.01/1.28    inference(forward_demodulation,[],[f344,f207])).
% 7.01/1.28  fof(f207,plain,(
% 7.01/1.28    k1_xboole_0 = k2_xboole_0(k1_xboole_0,k1_xboole_0)),
% 7.01/1.28    inference(forward_demodulation,[],[f206,f91])).
% 7.01/1.28  fof(f91,plain,(
% 7.01/1.28    ( ! [X0] : (k1_xboole_0 = k6_subset_1(k1_xboole_0,X0)) )),
% 7.01/1.28    inference(unit_resulting_resolution,[],[f39,f55,f47])).
% 7.01/1.28  fof(f47,plain,(
% 7.01/1.28    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 7.01/1.28    inference(cnf_transformation,[],[f31])).
% 7.01/1.28  fof(f55,plain,(
% 7.01/1.28    ( ! [X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X0)) )),
% 7.01/1.28    inference(definition_unfolding,[],[f41,f42])).
% 7.01/1.28  fof(f42,plain,(
% 7.01/1.28    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 7.01/1.28    inference(cnf_transformation,[],[f10])).
% 7.01/1.28  fof(f10,axiom,(
% 7.01/1.28    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 7.01/1.28    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 7.01/1.28  fof(f41,plain,(
% 7.01/1.28    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 7.01/1.28    inference(cnf_transformation,[],[f5])).
% 7.01/1.28  fof(f5,axiom,(
% 7.01/1.28    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 7.01/1.28    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 7.01/1.28  fof(f39,plain,(
% 7.01/1.28    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 7.01/1.28    inference(cnf_transformation,[],[f4])).
% 7.01/1.28  fof(f4,axiom,(
% 7.01/1.28    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 7.01/1.28    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 7.01/1.28  fof(f206,plain,(
% 7.01/1.28    ( ! [X0] : (k1_xboole_0 = k2_xboole_0(k6_subset_1(k1_xboole_0,X0),k1_xboole_0)) )),
% 7.01/1.28    inference(forward_demodulation,[],[f199,f91])).
% 7.01/1.28  fof(f199,plain,(
% 7.01/1.28    ( ! [X0,X1] : (k1_xboole_0 = k2_xboole_0(k6_subset_1(k1_xboole_0,X0),k6_subset_1(k1_xboole_0,X1))) )),
% 7.01/1.28    inference(unit_resulting_resolution,[],[f55,f55,f39,f54])).
% 7.01/1.28  fof(f54,plain,(
% 7.01/1.28    ( ! [X2,X0,X1] : (~r1_tarski(X1,sK3(X0,X1,X2)) | k2_xboole_0(X0,X2) = X1 | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 7.01/1.28    inference(cnf_transformation,[],[f33])).
% 7.01/1.28  fof(f33,plain,(
% 7.01/1.28    ! [X0,X1,X2] : (k2_xboole_0(X0,X2) = X1 | (~r1_tarski(X1,sK3(X0,X1,X2)) & r1_tarski(X2,sK3(X0,X1,X2)) & r1_tarski(X0,sK3(X0,X1,X2))) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 7.01/1.28    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f27,f32])).
% 7.01/1.28  fof(f32,plain,(
% 7.01/1.28    ! [X2,X1,X0] : (? [X3] : (~r1_tarski(X1,X3) & r1_tarski(X2,X3) & r1_tarski(X0,X3)) => (~r1_tarski(X1,sK3(X0,X1,X2)) & r1_tarski(X2,sK3(X0,X1,X2)) & r1_tarski(X0,sK3(X0,X1,X2))))),
% 7.01/1.28    introduced(choice_axiom,[])).
% 7.01/1.28  fof(f27,plain,(
% 7.01/1.28    ! [X0,X1,X2] : (k2_xboole_0(X0,X2) = X1 | ? [X3] : (~r1_tarski(X1,X3) & r1_tarski(X2,X3) & r1_tarski(X0,X3)) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 7.01/1.28    inference(flattening,[],[f26])).
% 7.01/1.28  fof(f26,plain,(
% 7.01/1.28    ! [X0,X1,X2] : (k2_xboole_0(X0,X2) = X1 | (? [X3] : (~r1_tarski(X1,X3) & (r1_tarski(X2,X3) & r1_tarski(X0,X3))) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 7.01/1.28    inference(ennf_transformation,[],[f2])).
% 7.01/1.28  fof(f2,axiom,(
% 7.01/1.28    ! [X0,X1,X2] : ((! [X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X3)) => r1_tarski(X1,X3)) & r1_tarski(X2,X1) & r1_tarski(X0,X1)) => k2_xboole_0(X0,X2) = X1)),
% 7.01/1.28    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_xboole_1)).
% 7.01/1.28  fof(f344,plain,(
% 7.01/1.28    ( ! [X0] : (k6_subset_1(X0,X0) = k2_xboole_0(k1_xboole_0,k1_xboole_0)) )),
% 7.01/1.28    inference(unit_resulting_resolution,[],[f39,f39,f152,f54])).
% 7.01/1.28  fof(f152,plain,(
% 7.01/1.28    ( ! [X0,X1] : (r1_tarski(k6_subset_1(X0,X0),X1)) )),
% 7.01/1.28    inference(unit_resulting_resolution,[],[f40,f57])).
% 7.01/1.28  fof(f57,plain,(
% 7.01/1.28    ( ! [X2,X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 7.01/1.28    inference(definition_unfolding,[],[f48,f42])).
% 7.01/1.28  fof(f48,plain,(
% 7.01/1.28    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 7.01/1.28    inference(cnf_transformation,[],[f20])).
% 7.01/1.28  fof(f20,plain,(
% 7.01/1.28    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 7.01/1.28    inference(ennf_transformation,[],[f6])).
% 7.01/1.28  fof(f6,axiom,(
% 7.01/1.28    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 7.01/1.28    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).
% 7.01/1.28  fof(f40,plain,(
% 7.01/1.28    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 7.01/1.28    inference(cnf_transformation,[],[f9])).
% 7.01/1.28  fof(f9,axiom,(
% 7.01/1.28    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 7.01/1.28    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 7.01/1.28  fof(f140,plain,(
% 7.01/1.28    ( ! [X0] : (k2_xboole_0(X0,k6_subset_1(X0,X0)) = X0) )),
% 7.01/1.28    inference(unit_resulting_resolution,[],[f59,f56])).
% 7.01/1.28  fof(f56,plain,(
% 7.01/1.28    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,k6_subset_1(X1,X0)) = X1) )),
% 7.01/1.28    inference(definition_unfolding,[],[f43,f42])).
% 7.01/1.28  fof(f43,plain,(
% 7.01/1.28    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1)) )),
% 7.01/1.28    inference(cnf_transformation,[],[f17])).
% 7.01/1.28  fof(f17,plain,(
% 7.01/1.28    ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1))),
% 7.01/1.28    inference(ennf_transformation,[],[f8])).
% 7.01/1.28  fof(f8,axiom,(
% 7.01/1.28    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1)),
% 7.01/1.28    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_xboole_1)).
% 7.01/1.28  fof(f11203,plain,(
% 7.01/1.28    ~r1_tarski(k2_xboole_0(sK1,k1_xboole_0),sK1) | (spl4_3 | ~spl4_29)),
% 7.01/1.28    inference(superposition,[],[f868,f10521])).
% 7.01/1.28  fof(f10521,plain,(
% 7.01/1.28    k1_xboole_0 = k6_subset_1(sK0,sK1) | ~spl4_29),
% 7.01/1.28    inference(avatar_component_clause,[],[f10519])).
% 7.01/1.28  fof(f10519,plain,(
% 7.01/1.28    spl4_29 <=> k1_xboole_0 = k6_subset_1(sK0,sK1)),
% 7.01/1.28    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).
% 7.01/1.28  fof(f868,plain,(
% 7.01/1.28    ( ! [X0] : (~r1_tarski(k2_xboole_0(X0,k6_subset_1(sK0,X0)),sK1)) ) | spl4_3),
% 7.01/1.28    inference(unit_resulting_resolution,[],[f74,f161,f51])).
% 7.01/1.28  fof(f51,plain,(
% 7.01/1.28    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 7.01/1.28    inference(cnf_transformation,[],[f25])).
% 7.01/1.28  fof(f25,plain,(
% 7.01/1.28    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 7.01/1.28    inference(flattening,[],[f24])).
% 7.01/1.28  fof(f24,plain,(
% 7.01/1.28    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 7.01/1.28    inference(ennf_transformation,[],[f3])).
% 7.01/1.28  fof(f3,axiom,(
% 7.01/1.28    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 7.01/1.28    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 7.01/1.28  fof(f161,plain,(
% 7.01/1.28    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,k6_subset_1(X0,X1)))) )),
% 7.01/1.28    inference(unit_resulting_resolution,[],[f59,f58])).
% 7.01/1.28  fof(f58,plain,(
% 7.01/1.28    ( ! [X2,X0,X1] : (~r1_tarski(k6_subset_1(X0,X1),X2) | r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 7.01/1.28    inference(definition_unfolding,[],[f49,f42])).
% 7.01/1.28  fof(f49,plain,(
% 7.01/1.28    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 7.01/1.28    inference(cnf_transformation,[],[f21])).
% 7.01/1.28  fof(f21,plain,(
% 7.01/1.28    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 7.01/1.28    inference(ennf_transformation,[],[f7])).
% 7.01/1.28  fof(f7,axiom,(
% 7.01/1.28    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 7.01/1.28    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).
% 7.01/1.28  fof(f74,plain,(
% 7.01/1.28    ~r1_tarski(sK0,sK1) | spl4_3),
% 7.01/1.28    inference(avatar_component_clause,[],[f72])).
% 7.01/1.28  fof(f72,plain,(
% 7.01/1.28    spl4_3 <=> r1_tarski(sK0,sK1)),
% 7.01/1.28    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 7.01/1.28  fof(f10522,plain,(
% 7.01/1.28    spl4_29 | ~spl4_1 | ~spl4_2 | ~spl4_4 | ~spl4_22 | ~spl4_25),
% 7.01/1.28    inference(avatar_split_clause,[],[f10430,f7018,f4660,f77,f67,f62,f10519])).
% 7.01/1.28  fof(f62,plain,(
% 7.01/1.28    spl4_1 <=> v1_relat_1(sK2)),
% 7.01/1.28    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 7.01/1.28  fof(f67,plain,(
% 7.01/1.28    spl4_2 <=> v1_funct_1(sK2)),
% 7.01/1.28    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 7.01/1.28  fof(f77,plain,(
% 7.01/1.28    spl4_4 <=> r1_tarski(sK0,k2_relat_1(sK2))),
% 7.01/1.28    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 7.01/1.28  fof(f4660,plain,(
% 7.01/1.28    spl4_22 <=> k1_xboole_0 = k9_relat_1(sK2,k1_xboole_0)),
% 7.01/1.28    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 7.01/1.28  fof(f7018,plain,(
% 7.01/1.28    spl4_25 <=> k1_xboole_0 = k10_relat_1(sK2,k6_subset_1(sK0,sK1))),
% 7.01/1.28    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 7.01/1.28  fof(f10430,plain,(
% 7.01/1.28    k1_xboole_0 = k6_subset_1(sK0,sK1) | (~spl4_1 | ~spl4_2 | ~spl4_4 | ~spl4_22 | ~spl4_25)),
% 7.01/1.28    inference(forward_demodulation,[],[f10426,f4662])).
% 7.01/1.28  fof(f4662,plain,(
% 7.01/1.28    k1_xboole_0 = k9_relat_1(sK2,k1_xboole_0) | ~spl4_22),
% 7.01/1.28    inference(avatar_component_clause,[],[f4660])).
% 7.01/1.28  fof(f10426,plain,(
% 7.01/1.28    k6_subset_1(sK0,sK1) = k9_relat_1(sK2,k1_xboole_0) | (~spl4_1 | ~spl4_2 | ~spl4_4 | ~spl4_25)),
% 7.01/1.28    inference(superposition,[],[f254,f7020])).
% 7.01/1.28  fof(f7020,plain,(
% 7.01/1.28    k1_xboole_0 = k10_relat_1(sK2,k6_subset_1(sK0,sK1)) | ~spl4_25),
% 7.01/1.28    inference(avatar_component_clause,[],[f7018])).
% 7.01/1.28  fof(f254,plain,(
% 7.01/1.28    ( ! [X0] : (k6_subset_1(sK0,X0) = k9_relat_1(sK2,k10_relat_1(sK2,k6_subset_1(sK0,X0)))) ) | (~spl4_1 | ~spl4_2 | ~spl4_4)),
% 7.01/1.28    inference(unit_resulting_resolution,[],[f64,f69,f127,f44])).
% 7.01/1.28  fof(f44,plain,(
% 7.01/1.28    ( ! [X0,X1] : (~v1_funct_1(X1) | ~r1_tarski(X0,k2_relat_1(X1)) | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~v1_relat_1(X1)) )),
% 7.01/1.28    inference(cnf_transformation,[],[f19])).
% 7.01/1.28  fof(f19,plain,(
% 7.01/1.28    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 7.01/1.28    inference(flattening,[],[f18])).
% 7.01/1.28  fof(f18,plain,(
% 7.01/1.28    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 7.01/1.28    inference(ennf_transformation,[],[f12])).
% 7.01/1.28  fof(f12,axiom,(
% 7.01/1.28    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 7.01/1.28    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).
% 7.01/1.28  fof(f127,plain,(
% 7.01/1.28    ( ! [X0] : (r1_tarski(k6_subset_1(sK0,X0),k2_relat_1(sK2))) ) | ~spl4_4),
% 7.01/1.28    inference(unit_resulting_resolution,[],[f55,f79,f51])).
% 7.01/1.28  fof(f79,plain,(
% 7.01/1.28    r1_tarski(sK0,k2_relat_1(sK2)) | ~spl4_4),
% 7.01/1.28    inference(avatar_component_clause,[],[f77])).
% 7.01/1.28  fof(f69,plain,(
% 7.01/1.28    v1_funct_1(sK2) | ~spl4_2),
% 7.01/1.28    inference(avatar_component_clause,[],[f67])).
% 7.01/1.28  fof(f64,plain,(
% 7.01/1.28    v1_relat_1(sK2) | ~spl4_1),
% 7.01/1.28    inference(avatar_component_clause,[],[f62])).
% 7.01/1.28  fof(f7021,plain,(
% 7.01/1.28    spl4_25 | ~spl4_1 | ~spl4_2 | ~spl4_5),
% 7.01/1.28    inference(avatar_split_clause,[],[f3817,f82,f67,f62,f7018])).
% 7.01/1.28  fof(f82,plain,(
% 7.01/1.28    spl4_5 <=> r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),
% 7.01/1.28    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 7.01/1.28  fof(f3817,plain,(
% 7.01/1.28    k1_xboole_0 = k10_relat_1(sK2,k6_subset_1(sK0,sK1)) | (~spl4_1 | ~spl4_2 | ~spl4_5)),
% 7.01/1.28    inference(forward_demodulation,[],[f3728,f1031])).
% 7.01/1.28  fof(f1031,plain,(
% 7.01/1.28    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 7.01/1.28    inference(unit_resulting_resolution,[],[f39,f213])).
% 7.01/1.28  fof(f213,plain,(
% 7.01/1.28    ( ! [X2,X3] : (~r1_tarski(X2,X3) | k2_xboole_0(X2,X3) = X3) )),
% 7.01/1.28    inference(subsumption_resolution,[],[f204,f59])).
% 7.01/1.28  fof(f204,plain,(
% 7.01/1.28    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = X3 | ~r1_tarski(X3,X3) | ~r1_tarski(X2,X3)) )),
% 7.01/1.28    inference(duplicate_literal_removal,[],[f201])).
% 7.01/1.28  fof(f201,plain,(
% 7.01/1.28    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = X3 | ~r1_tarski(X3,X3) | ~r1_tarski(X2,X3) | k2_xboole_0(X2,X3) = X3 | ~r1_tarski(X3,X3) | ~r1_tarski(X2,X3)) )),
% 7.01/1.28    inference(resolution,[],[f54,f53])).
% 7.01/1.28  fof(f53,plain,(
% 7.01/1.28    ( ! [X2,X0,X1] : (r1_tarski(X2,sK3(X0,X1,X2)) | k2_xboole_0(X0,X2) = X1 | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 7.01/1.28    inference(cnf_transformation,[],[f33])).
% 7.01/1.28  fof(f3728,plain,(
% 7.01/1.28    k2_xboole_0(k1_xboole_0,k1_xboole_0) = k10_relat_1(sK2,k6_subset_1(sK0,sK1)) | (~spl4_1 | ~spl4_2 | ~spl4_5)),
% 7.01/1.28    inference(unit_resulting_resolution,[],[f39,f39,f522,f54])).
% 7.01/1.28  fof(f522,plain,(
% 7.01/1.28    ( ! [X0] : (r1_tarski(k10_relat_1(sK2,k6_subset_1(sK0,sK1)),X0)) ) | (~spl4_1 | ~spl4_2 | ~spl4_5)),
% 7.01/1.28    inference(forward_demodulation,[],[f510,f180])).
% 7.01/1.28  fof(f180,plain,(
% 7.01/1.28    ( ! [X0,X1] : (k10_relat_1(sK2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1))) ) | (~spl4_1 | ~spl4_2)),
% 7.01/1.28    inference(unit_resulting_resolution,[],[f64,f69,f50])).
% 7.01/1.28  fof(f50,plain,(
% 7.01/1.28    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 7.01/1.28    inference(cnf_transformation,[],[f23])).
% 7.01/1.28  fof(f23,plain,(
% 7.01/1.28    ! [X0,X1,X2] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 7.01/1.28    inference(flattening,[],[f22])).
% 7.01/1.28  fof(f22,plain,(
% 7.01/1.28    ! [X0,X1,X2] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 7.01/1.28    inference(ennf_transformation,[],[f11])).
% 7.01/1.28  fof(f11,axiom,(
% 7.01/1.28    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))),
% 7.01/1.28    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_funct_1)).
% 7.01/1.28  fof(f510,plain,(
% 7.01/1.28    ( ! [X0] : (r1_tarski(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),X0)) ) | ~spl4_5),
% 7.01/1.28    inference(unit_resulting_resolution,[],[f112,f57])).
% 7.01/1.28  fof(f112,plain,(
% 7.01/1.28    ( ! [X0] : (r1_tarski(k10_relat_1(sK2,sK0),k2_xboole_0(k10_relat_1(sK2,sK1),X0))) ) | ~spl4_5),
% 7.01/1.28    inference(unit_resulting_resolution,[],[f84,f40,f51])).
% 7.01/1.28  fof(f84,plain,(
% 7.01/1.28    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) | ~spl4_5),
% 7.01/1.28    inference(avatar_component_clause,[],[f82])).
% 7.01/1.28  fof(f4663,plain,(
% 7.01/1.28    spl4_22 | ~spl4_1 | ~spl4_2 | ~spl4_9),
% 7.01/1.28    inference(avatar_split_clause,[],[f4653,f273,f67,f62,f4660])).
% 7.01/1.28  fof(f273,plain,(
% 7.01/1.28    spl4_9 <=> k1_xboole_0 = k9_relat_1(sK2,k10_relat_1(sK2,k1_xboole_0))),
% 7.01/1.28    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 7.01/1.28  fof(f4653,plain,(
% 7.01/1.28    k1_xboole_0 = k9_relat_1(sK2,k1_xboole_0) | (~spl4_1 | ~spl4_2 | ~spl4_9)),
% 7.01/1.28    inference(backward_demodulation,[],[f275,f4652])).
% 7.01/1.28  fof(f4652,plain,(
% 7.01/1.28    k1_xboole_0 = k10_relat_1(sK2,k1_xboole_0) | (~spl4_1 | ~spl4_2)),
% 7.01/1.28    inference(forward_demodulation,[],[f4620,f361])).
% 7.01/1.28  fof(f4620,plain,(
% 7.01/1.28    ( ! [X1] : (k1_xboole_0 = k10_relat_1(sK2,k6_subset_1(X1,X1))) ) | (~spl4_1 | ~spl4_2)),
% 7.01/1.28    inference(superposition,[],[f361,f180])).
% 7.01/1.28  fof(f275,plain,(
% 7.01/1.28    k1_xboole_0 = k9_relat_1(sK2,k10_relat_1(sK2,k1_xboole_0)) | ~spl4_9),
% 7.01/1.28    inference(avatar_component_clause,[],[f273])).
% 7.01/1.28  fof(f276,plain,(
% 7.01/1.28    spl4_9 | ~spl4_1 | ~spl4_2),
% 7.01/1.28    inference(avatar_split_clause,[],[f168,f67,f62,f273])).
% 7.01/1.28  fof(f168,plain,(
% 7.01/1.28    k1_xboole_0 = k9_relat_1(sK2,k10_relat_1(sK2,k1_xboole_0)) | (~spl4_1 | ~spl4_2)),
% 7.01/1.28    inference(unit_resulting_resolution,[],[f64,f69,f39,f44])).
% 7.01/1.28  fof(f85,plain,(
% 7.01/1.28    spl4_5),
% 7.01/1.28    inference(avatar_split_clause,[],[f36,f82])).
% 7.01/1.28  fof(f36,plain,(
% 7.01/1.28    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),
% 7.01/1.28    inference(cnf_transformation,[],[f29])).
% 7.01/1.28  fof(f29,plain,(
% 7.01/1.28    ~r1_tarski(sK0,sK1) & r1_tarski(sK0,k2_relat_1(sK2)) & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 7.01/1.28    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f28])).
% 7.01/1.28  fof(f28,plain,(
% 7.01/1.28    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_tarski(sK0,sK1) & r1_tarski(sK0,k2_relat_1(sK2)) & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 7.01/1.28    introduced(choice_axiom,[])).
% 7.01/1.28  fof(f16,plain,(
% 7.01/1.28    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 7.01/1.28    inference(flattening,[],[f15])).
% 7.01/1.28  fof(f15,plain,(
% 7.01/1.28    ? [X0,X1,X2] : ((~r1_tarski(X0,X1) & (r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 7.01/1.28    inference(ennf_transformation,[],[f14])).
% 7.01/1.28  fof(f14,negated_conjecture,(
% 7.01/1.28    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 7.01/1.28    inference(negated_conjecture,[],[f13])).
% 7.01/1.28  fof(f13,conjecture,(
% 7.01/1.28    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 7.01/1.28    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_funct_1)).
% 7.01/1.28  fof(f80,plain,(
% 7.01/1.28    spl4_4),
% 7.01/1.28    inference(avatar_split_clause,[],[f37,f77])).
% 7.01/1.28  fof(f37,plain,(
% 7.01/1.28    r1_tarski(sK0,k2_relat_1(sK2))),
% 7.01/1.28    inference(cnf_transformation,[],[f29])).
% 7.01/1.28  fof(f75,plain,(
% 7.01/1.28    ~spl4_3),
% 7.01/1.28    inference(avatar_split_clause,[],[f38,f72])).
% 7.01/1.28  fof(f38,plain,(
% 7.01/1.28    ~r1_tarski(sK0,sK1)),
% 7.01/1.28    inference(cnf_transformation,[],[f29])).
% 7.01/1.28  fof(f70,plain,(
% 7.01/1.28    spl4_2),
% 7.01/1.28    inference(avatar_split_clause,[],[f35,f67])).
% 7.01/1.28  fof(f35,plain,(
% 7.01/1.28    v1_funct_1(sK2)),
% 7.01/1.28    inference(cnf_transformation,[],[f29])).
% 7.01/1.28  fof(f65,plain,(
% 7.01/1.28    spl4_1),
% 7.01/1.28    inference(avatar_split_clause,[],[f34,f62])).
% 7.01/1.28  fof(f34,plain,(
% 7.01/1.28    v1_relat_1(sK2)),
% 7.01/1.28    inference(cnf_transformation,[],[f29])).
% 7.01/1.28  % SZS output end Proof for theBenchmark
% 7.01/1.28  % (3612)------------------------------
% 7.01/1.28  % (3612)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.01/1.28  % (3612)Termination reason: Refutation
% 7.01/1.28  
% 7.01/1.28  % (3612)Memory used [KB]: 17654
% 7.01/1.28  % (3612)Time elapsed: 0.818 s
% 7.01/1.28  % (3612)------------------------------
% 7.01/1.28  % (3612)------------------------------
% 7.01/1.28  % (3591)Success in time 0.913 s
%------------------------------------------------------------------------------
