%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:41 EST 2020

% Result     : Theorem 7.44s
% Output     : Refutation 7.44s
% Verified   : 
% Statistics : Number of formulae       :  299 (1832 expanded)
%              Number of leaves         :   61 ( 610 expanded)
%              Depth                    :   17
%              Number of atoms          :  612 (3831 expanded)
%              Number of equality atoms :   35 ( 527 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9665,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f86,f91,f287,f288,f289,f1883,f1888,f1893,f1898,f1956,f1958,f2085,f2094,f2105,f2117,f2155,f2525,f2531,f2542,f2547,f3769,f4104,f4109,f4115,f4126,f5006,f5140,f5165,f5170,f5171,f5301,f5662,f5988,f5993,f5999,f6041,f6046,f6047,f6053,f6054,f6093,f6098,f6103,f6104,f6106,f6107,f8827,f8833,f9018,f9023,f9028,f9029,f9035,f9036,f9082,f9087,f9092,f9097,f9098,f9100,f9101,f9411,f9469,f9662,f9664])).

fof(f9664,plain,
    ( ~ spl5_2
    | spl5_18 ),
    inference(avatar_contradiction_clause,[],[f9663])).

fof(f9663,plain,
    ( $false
    | ~ spl5_2
    | spl5_18 ),
    inference(subsumption_resolution,[],[f9618,f90])).

fof(f90,plain,
    ( v1_relat_1(sK2)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl5_2
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f9618,plain,
    ( ~ v1_relat_1(sK2)
    | spl5_18 ),
    inference(unit_resulting_resolution,[],[f3768,f77,f2125])).

fof(f2125,plain,(
    ! [X6,X8,X7,X9] :
      ( ~ r1_tarski(k10_relat_1(X6,k2_xboole_0(X7,X8)),X9)
      | r1_tarski(k10_relat_1(X6,X7),X9)
      | ~ v1_relat_1(X6) ) ),
    inference(superposition,[],[f49,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_relat_1)).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f77,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f3768,plain,
    ( ~ r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,k2_xboole_0(sK0,sK1)))
    | spl5_18 ),
    inference(avatar_component_clause,[],[f3766])).

fof(f3766,plain,
    ( spl5_18
  <=> r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,k2_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f9662,plain,
    ( ~ spl5_2
    | spl5_18 ),
    inference(avatar_contradiction_clause,[],[f9619])).

fof(f9619,plain,
    ( $false
    | ~ spl5_2
    | spl5_18 ),
    inference(unit_resulting_resolution,[],[f90,f3768,f77,f2125])).

fof(f9469,plain,
    ( spl5_49
    | spl5_24
    | spl5_26 ),
    inference(avatar_split_clause,[],[f9424,f5167,f5137,f9466])).

fof(f9466,plain,
    ( spl5_49
  <=> r2_hidden(sK3(k6_subset_1(k2_xboole_0(sK0,sK1),sK0),k1_xboole_0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_49])])).

fof(f5137,plain,
    ( spl5_24
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f5167,plain,
    ( spl5_26
  <=> r2_hidden(sK3(sK1,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f9424,plain,
    ( r2_hidden(sK3(k6_subset_1(k2_xboole_0(sK0,sK1),sK0),k1_xboole_0),sK1)
    | spl5_24
    | spl5_26 ),
    inference(unit_resulting_resolution,[],[f163,f7761,f137])).

fof(f137,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1),X2)
      | ~ r1_tarski(X0,X2)
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f41,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f7761,plain,
    ( ! [X0] : ~ r1_tarski(k6_subset_1(k2_xboole_0(X0,sK1),sK0),k1_xboole_0)
    | spl5_24
    | spl5_26 ),
    inference(unit_resulting_resolution,[],[f5169,f246,f5145,f1318])).

fof(f1318,plain,(
    ! [X14,X12,X15,X13] :
      ( ~ r1_tarski(k6_subset_1(X14,X13),X15)
      | ~ r2_hidden(X12,X14)
      | r2_hidden(X12,X15)
      | r2_hidden(X12,X13) ) ),
    inference(resolution,[],[f79,f41])).

fof(f79,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k6_subset_1(X0,X1))
      | r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k6_subset_1(X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f56,f34])).

fof(f34,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f5145,plain,
    ( ! [X0] : r2_hidden(sK3(sK1,sK0),k2_xboole_0(X0,sK1))
    | spl5_24 ),
    inference(unit_resulting_resolution,[],[f94,f5139,f137])).

fof(f5139,plain,
    ( ~ r1_tarski(sK1,sK0)
    | spl5_24 ),
    inference(avatar_component_clause,[],[f5137])).

fof(f94,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X1,X0)) ),
    inference(unit_resulting_resolution,[],[f77,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f246,plain,(
    ! [X4] : ~ r2_hidden(X4,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f244,f108])).

fof(f108,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_xboole_0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(superposition,[],[f80,f67])).

fof(f67,plain,(
    ! [X0] : k6_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f33,f34])).

fof(f33,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f80,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k6_subset_1(X0,X1))
      | ~ r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k6_subset_1(X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f55,f34])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f244,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(X4,k1_xboole_0)
      | r2_hidden(X4,X3) ) ),
    inference(superposition,[],[f81,f196])).

fof(f196,plain,(
    ! [X0] : k1_xboole_0 = k6_subset_1(X0,X0) ),
    inference(unit_resulting_resolution,[],[f160,f132])).

fof(f132,plain,(
    ! [X17] :
      ( ~ r1_tarski(X17,k1_xboole_0)
      | k1_xboole_0 = X17 ) ),
    inference(resolution,[],[f40,f119])).

fof(f119,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(duplicate_literal_removal,[],[f118])).

fof(f118,plain,(
    ! [X0] :
      ( r1_tarski(k1_xboole_0,X0)
      | r1_tarski(k1_xboole_0,X0) ) ),
    inference(resolution,[],[f109,f42])).

fof(f109,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(k1_xboole_0,X0),X1)
      | r1_tarski(k1_xboole_0,X0) ) ),
    inference(resolution,[],[f108,f42])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f160,plain,(
    ! [X0,X1] : r1_tarski(k6_subset_1(X0,X0),X1) ),
    inference(unit_resulting_resolution,[],[f97,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
      | r1_tarski(k6_subset_1(X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f47,f34])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
      | r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f97,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(unit_resulting_resolution,[],[f77,f49])).

fof(f81,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k6_subset_1(X0,X1))
      | r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k6_subset_1(X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f54,f34])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f5169,plain,
    ( ~ r2_hidden(sK3(sK1,sK0),sK0)
    | spl5_26 ),
    inference(avatar_component_clause,[],[f5167])).

fof(f163,plain,(
    ! [X0,X1] : r1_tarski(k6_subset_1(k2_xboole_0(X0,X1),X0),X1) ),
    inference(unit_resulting_resolution,[],[f77,f69])).

fof(f9411,plain,
    ( spl5_48
    | spl5_24
    | spl5_26 ),
    inference(avatar_split_clause,[],[f9369,f5167,f5137,f9408])).

fof(f9408,plain,
    ( spl5_48
  <=> r2_hidden(sK3(k6_subset_1(k2_xboole_0(sK0,sK1),sK0),sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_48])])).

fof(f9369,plain,
    ( r2_hidden(sK3(k6_subset_1(k2_xboole_0(sK0,sK1),sK0),sK0),sK1)
    | spl5_24
    | spl5_26 ),
    inference(unit_resulting_resolution,[],[f163,f7757,f137])).

fof(f7757,plain,
    ( ! [X0] : ~ r1_tarski(k6_subset_1(k2_xboole_0(X0,sK1),sK0),sK0)
    | spl5_24
    | spl5_26 ),
    inference(unit_resulting_resolution,[],[f5169,f5169,f5145,f1318])).

fof(f9101,plain,
    ( spl5_46
    | spl5_39 ),
    inference(avatar_split_clause,[],[f9037,f8830,f9089])).

fof(f9089,plain,
    ( spl5_46
  <=> r2_hidden(sK3(k6_subset_1(k6_subset_1(sK1,sK0),sK0),sK0),k6_subset_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_46])])).

fof(f8830,plain,
    ( spl5_39
  <=> r1_tarski(k6_subset_1(k6_subset_1(sK1,sK0),sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_39])])).

fof(f9037,plain,
    ( r2_hidden(sK3(k6_subset_1(k6_subset_1(sK1,sK0),sK0),sK0),k6_subset_1(sK1,sK0))
    | spl5_39 ),
    inference(unit_resulting_resolution,[],[f8832,f116])).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(k6_subset_1(X0,X1),X2),X0)
      | r1_tarski(k6_subset_1(X0,X1),X2) ) ),
    inference(resolution,[],[f81,f42])).

fof(f8832,plain,
    ( ~ r1_tarski(k6_subset_1(k6_subset_1(sK1,sK0),sK0),sK0)
    | spl5_39 ),
    inference(avatar_component_clause,[],[f8830])).

fof(f9100,plain,
    ( ~ spl5_47
    | spl5_39 ),
    inference(avatar_split_clause,[],[f9038,f8830,f9094])).

fof(f9094,plain,
    ( spl5_47
  <=> r2_hidden(sK3(k6_subset_1(k6_subset_1(sK1,sK0),sK0),sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_47])])).

fof(f9038,plain,
    ( ~ r2_hidden(sK3(k6_subset_1(k6_subset_1(sK1,sK0),sK0),sK0),sK0)
    | spl5_39 ),
    inference(unit_resulting_resolution,[],[f8832,f107])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK3(k6_subset_1(X0,X1),X2),X1)
      | r1_tarski(k6_subset_1(X0,X1),X2) ) ),
    inference(resolution,[],[f80,f42])).

fof(f9098,plain,
    ( spl5_44
    | spl5_39 ),
    inference(avatar_split_clause,[],[f9043,f8830,f9079])).

fof(f9079,plain,
    ( spl5_44
  <=> r2_hidden(sK3(k6_subset_1(k6_subset_1(sK1,sK0),sK0),sK0),k6_subset_1(k6_subset_1(sK1,sK0),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_44])])).

fof(f9043,plain,
    ( r2_hidden(sK3(k6_subset_1(k6_subset_1(sK1,sK0),sK0),sK0),k6_subset_1(k6_subset_1(sK1,sK0),sK0))
    | spl5_39 ),
    inference(unit_resulting_resolution,[],[f8832,f42])).

fof(f9097,plain,
    ( ~ spl5_47
    | spl5_39 ),
    inference(avatar_split_clause,[],[f9044,f8830,f9094])).

fof(f9044,plain,
    ( ~ r2_hidden(sK3(k6_subset_1(k6_subset_1(sK1,sK0),sK0),sK0),sK0)
    | spl5_39 ),
    inference(unit_resulting_resolution,[],[f8832,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f9092,plain,
    ( spl5_46
    | spl5_39 ),
    inference(avatar_split_clause,[],[f9046,f8830,f9089])).

fof(f9046,plain,
    ( r2_hidden(sK3(k6_subset_1(k6_subset_1(sK1,sK0),sK0),sK0),k6_subset_1(sK1,sK0))
    | spl5_39 ),
    inference(unit_resulting_resolution,[],[f154,f8832,f137])).

fof(f154,plain,(
    ! [X0,X1] : r1_tarski(k6_subset_1(X0,X1),X0) ),
    inference(unit_resulting_resolution,[],[f94,f69])).

fof(f9087,plain,
    ( spl5_45
    | spl5_39 ),
    inference(avatar_split_clause,[],[f9047,f8830,f9084])).

fof(f9084,plain,
    ( spl5_45
  <=> r2_hidden(sK3(k6_subset_1(k6_subset_1(sK1,sK0),sK0),sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_45])])).

fof(f9047,plain,
    ( r2_hidden(sK3(k6_subset_1(k6_subset_1(sK1,sK0),sK0),sK0),sK1)
    | spl5_39 ),
    inference(unit_resulting_resolution,[],[f329,f8832,f137])).

fof(f329,plain,(
    ! [X2,X0,X1] : r1_tarski(k6_subset_1(k6_subset_1(X0,X1),X2),X0) ),
    inference(unit_resulting_resolution,[],[f155,f69])).

fof(f155,plain,(
    ! [X2,X0,X1] : r1_tarski(k6_subset_1(X0,X1),k2_xboole_0(X2,X0)) ),
    inference(unit_resulting_resolution,[],[f95,f69])).

fof(f95,plain,(
    ! [X2,X0,X1] : r1_tarski(X0,k2_xboole_0(X1,k2_xboole_0(X2,X0))) ),
    inference(unit_resulting_resolution,[],[f94,f46])).

fof(f9082,plain,
    ( spl5_44
    | spl5_39 ),
    inference(avatar_split_clause,[],[f9050,f8830,f9079])).

fof(f9050,plain,
    ( r2_hidden(sK3(k6_subset_1(k6_subset_1(sK1,sK0),sK0),sK0),k6_subset_1(k6_subset_1(sK1,sK0),sK0))
    | spl5_39 ),
    inference(unit_resulting_resolution,[],[f77,f8832,f137])).

fof(f9036,plain,
    ( spl5_42
    | spl5_38 ),
    inference(avatar_split_clause,[],[f8970,f8824,f9025])).

fof(f9025,plain,
    ( spl5_42
  <=> r2_hidden(sK3(k6_subset_1(k6_subset_1(sK1,sK0),sK0),k1_xboole_0),k6_subset_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_42])])).

fof(f8824,plain,
    ( spl5_38
  <=> r1_tarski(k6_subset_1(k6_subset_1(sK1,sK0),sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).

fof(f8970,plain,
    ( r2_hidden(sK3(k6_subset_1(k6_subset_1(sK1,sK0),sK0),k1_xboole_0),k6_subset_1(sK1,sK0))
    | spl5_38 ),
    inference(unit_resulting_resolution,[],[f8826,f116])).

fof(f8826,plain,
    ( ~ r1_tarski(k6_subset_1(k6_subset_1(sK1,sK0),sK0),k1_xboole_0)
    | spl5_38 ),
    inference(avatar_component_clause,[],[f8824])).

fof(f9035,plain,
    ( ~ spl5_43
    | spl5_38 ),
    inference(avatar_split_clause,[],[f8971,f8824,f9032])).

fof(f9032,plain,
    ( spl5_43
  <=> r2_hidden(sK3(k6_subset_1(k6_subset_1(sK1,sK0),sK0),k1_xboole_0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_43])])).

fof(f8971,plain,
    ( ~ r2_hidden(sK3(k6_subset_1(k6_subset_1(sK1,sK0),sK0),k1_xboole_0),sK0)
    | spl5_38 ),
    inference(unit_resulting_resolution,[],[f8826,f107])).

fof(f9029,plain,
    ( spl5_40
    | spl5_38 ),
    inference(avatar_split_clause,[],[f8976,f8824,f9015])).

fof(f9015,plain,
    ( spl5_40
  <=> r2_hidden(sK3(k6_subset_1(k6_subset_1(sK1,sK0),sK0),k1_xboole_0),k6_subset_1(k6_subset_1(sK1,sK0),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_40])])).

fof(f8976,plain,
    ( r2_hidden(sK3(k6_subset_1(k6_subset_1(sK1,sK0),sK0),k1_xboole_0),k6_subset_1(k6_subset_1(sK1,sK0),sK0))
    | spl5_38 ),
    inference(unit_resulting_resolution,[],[f8826,f42])).

fof(f9028,plain,
    ( spl5_42
    | spl5_38 ),
    inference(avatar_split_clause,[],[f8979,f8824,f9025])).

fof(f8979,plain,
    ( r2_hidden(sK3(k6_subset_1(k6_subset_1(sK1,sK0),sK0),k1_xboole_0),k6_subset_1(sK1,sK0))
    | spl5_38 ),
    inference(unit_resulting_resolution,[],[f154,f8826,f137])).

fof(f9023,plain,
    ( spl5_41
    | spl5_38 ),
    inference(avatar_split_clause,[],[f8980,f8824,f9020])).

fof(f9020,plain,
    ( spl5_41
  <=> r2_hidden(sK3(k6_subset_1(k6_subset_1(sK1,sK0),sK0),k1_xboole_0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_41])])).

fof(f8980,plain,
    ( r2_hidden(sK3(k6_subset_1(k6_subset_1(sK1,sK0),sK0),k1_xboole_0),sK1)
    | spl5_38 ),
    inference(unit_resulting_resolution,[],[f329,f8826,f137])).

fof(f9018,plain,
    ( spl5_40
    | spl5_38 ),
    inference(avatar_split_clause,[],[f8983,f8824,f9015])).

fof(f8983,plain,
    ( r2_hidden(sK3(k6_subset_1(k6_subset_1(sK1,sK0),sK0),k1_xboole_0),k6_subset_1(k6_subset_1(sK1,sK0),sK0))
    | spl5_38 ),
    inference(unit_resulting_resolution,[],[f77,f8826,f137])).

fof(f8833,plain,
    ( ~ spl5_39
    | spl5_26
    | ~ spl5_27 ),
    inference(avatar_split_clause,[],[f7789,f5298,f5167,f8830])).

fof(f5298,plain,
    ( spl5_27
  <=> r2_hidden(sK3(sK1,sK0),k6_subset_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f7789,plain,
    ( ~ r1_tarski(k6_subset_1(k6_subset_1(sK1,sK0),sK0),sK0)
    | spl5_26
    | ~ spl5_27 ),
    inference(unit_resulting_resolution,[],[f5169,f5169,f5300,f1318])).

fof(f5300,plain,
    ( r2_hidden(sK3(sK1,sK0),k6_subset_1(sK1,sK0))
    | ~ spl5_27 ),
    inference(avatar_component_clause,[],[f5298])).

fof(f8827,plain,
    ( ~ spl5_38
    | spl5_26
    | ~ spl5_27 ),
    inference(avatar_split_clause,[],[f7793,f5298,f5167,f8824])).

fof(f7793,plain,
    ( ~ r1_tarski(k6_subset_1(k6_subset_1(sK1,sK0),sK0),k1_xboole_0)
    | spl5_26
    | ~ spl5_27 ),
    inference(unit_resulting_resolution,[],[f5169,f246,f5300,f1318])).

fof(f6107,plain,
    ( spl5_36
    | spl5_30 ),
    inference(avatar_split_clause,[],[f6055,f5990,f6095])).

fof(f6095,plain,
    ( spl5_36
  <=> r2_hidden(sK3(k6_subset_1(sK1,sK0),sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).

fof(f5990,plain,
    ( spl5_30
  <=> r1_tarski(k6_subset_1(sK1,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f6055,plain,
    ( r2_hidden(sK3(k6_subset_1(sK1,sK0),sK0),sK1)
    | spl5_30 ),
    inference(unit_resulting_resolution,[],[f5992,f116])).

fof(f5992,plain,
    ( ~ r1_tarski(k6_subset_1(sK1,sK0),sK0)
    | spl5_30 ),
    inference(avatar_component_clause,[],[f5990])).

fof(f6106,plain,
    ( ~ spl5_37
    | spl5_30 ),
    inference(avatar_split_clause,[],[f6056,f5990,f6100])).

fof(f6100,plain,
    ( spl5_37
  <=> r2_hidden(sK3(k6_subset_1(sK1,sK0),sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).

fof(f6056,plain,
    ( ~ r2_hidden(sK3(k6_subset_1(sK1,sK0),sK0),sK0)
    | spl5_30 ),
    inference(unit_resulting_resolution,[],[f5992,f107])).

fof(f6104,plain,
    ( spl5_35
    | spl5_30 ),
    inference(avatar_split_clause,[],[f6061,f5990,f6090])).

fof(f6090,plain,
    ( spl5_35
  <=> r2_hidden(sK3(k6_subset_1(sK1,sK0),sK0),k6_subset_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).

fof(f6061,plain,
    ( r2_hidden(sK3(k6_subset_1(sK1,sK0),sK0),k6_subset_1(sK1,sK0))
    | spl5_30 ),
    inference(unit_resulting_resolution,[],[f5992,f42])).

fof(f6103,plain,
    ( ~ spl5_37
    | spl5_30 ),
    inference(avatar_split_clause,[],[f6062,f5990,f6100])).

fof(f6062,plain,
    ( ~ r2_hidden(sK3(k6_subset_1(sK1,sK0),sK0),sK0)
    | spl5_30 ),
    inference(unit_resulting_resolution,[],[f5992,f43])).

fof(f6098,plain,
    ( spl5_36
    | spl5_30 ),
    inference(avatar_split_clause,[],[f6064,f5990,f6095])).

fof(f6064,plain,
    ( r2_hidden(sK3(k6_subset_1(sK1,sK0),sK0),sK1)
    | spl5_30 ),
    inference(unit_resulting_resolution,[],[f154,f5992,f137])).

fof(f6093,plain,
    ( spl5_35
    | spl5_30 ),
    inference(avatar_split_clause,[],[f6067,f5990,f6090])).

fof(f6067,plain,
    ( r2_hidden(sK3(k6_subset_1(sK1,sK0),sK0),k6_subset_1(sK1,sK0))
    | spl5_30 ),
    inference(unit_resulting_resolution,[],[f77,f5992,f137])).

fof(f6054,plain,
    ( spl5_33
    | spl5_29 ),
    inference(avatar_split_clause,[],[f6001,f5985,f6043])).

fof(f6043,plain,
    ( spl5_33
  <=> r2_hidden(sK3(k6_subset_1(sK1,sK0),k1_xboole_0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).

fof(f5985,plain,
    ( spl5_29
  <=> r1_tarski(k6_subset_1(sK1,sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).

fof(f6001,plain,
    ( r2_hidden(sK3(k6_subset_1(sK1,sK0),k1_xboole_0),sK1)
    | spl5_29 ),
    inference(unit_resulting_resolution,[],[f5987,f116])).

fof(f5987,plain,
    ( ~ r1_tarski(k6_subset_1(sK1,sK0),k1_xboole_0)
    | spl5_29 ),
    inference(avatar_component_clause,[],[f5985])).

fof(f6053,plain,
    ( ~ spl5_34
    | spl5_29 ),
    inference(avatar_split_clause,[],[f6002,f5985,f6050])).

fof(f6050,plain,
    ( spl5_34
  <=> r2_hidden(sK3(k6_subset_1(sK1,sK0),k1_xboole_0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).

fof(f6002,plain,
    ( ~ r2_hidden(sK3(k6_subset_1(sK1,sK0),k1_xboole_0),sK0)
    | spl5_29 ),
    inference(unit_resulting_resolution,[],[f5987,f107])).

fof(f6047,plain,
    ( spl5_32
    | spl5_29 ),
    inference(avatar_split_clause,[],[f6007,f5985,f6038])).

fof(f6038,plain,
    ( spl5_32
  <=> r2_hidden(sK3(k6_subset_1(sK1,sK0),k1_xboole_0),k6_subset_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).

fof(f6007,plain,
    ( r2_hidden(sK3(k6_subset_1(sK1,sK0),k1_xboole_0),k6_subset_1(sK1,sK0))
    | spl5_29 ),
    inference(unit_resulting_resolution,[],[f5987,f42])).

fof(f6046,plain,
    ( spl5_33
    | spl5_29 ),
    inference(avatar_split_clause,[],[f6010,f5985,f6043])).

fof(f6010,plain,
    ( r2_hidden(sK3(k6_subset_1(sK1,sK0),k1_xboole_0),sK1)
    | spl5_29 ),
    inference(unit_resulting_resolution,[],[f154,f5987,f137])).

fof(f6041,plain,
    ( spl5_32
    | spl5_29 ),
    inference(avatar_split_clause,[],[f6013,f5985,f6038])).

fof(f6013,plain,
    ( r2_hidden(sK3(k6_subset_1(sK1,sK0),k1_xboole_0),k6_subset_1(sK1,sK0))
    | spl5_29 ),
    inference(unit_resulting_resolution,[],[f77,f5987,f137])).

fof(f5999,plain,
    ( spl5_31
    | spl5_26
    | ~ spl5_27 ),
    inference(avatar_split_clause,[],[f5954,f5298,f5167,f5996])).

fof(f5996,plain,
    ( spl5_31
  <=> r2_hidden(sK3(sK1,sK0),k6_subset_1(k6_subset_1(sK1,sK0),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).

fof(f5954,plain,
    ( r2_hidden(sK3(sK1,sK0),k6_subset_1(k6_subset_1(sK1,sK0),sK0))
    | spl5_26
    | ~ spl5_27 ),
    inference(unit_resulting_resolution,[],[f5169,f5300,f79])).

fof(f5993,plain,
    ( ~ spl5_30
    | spl5_26
    | ~ spl5_27 ),
    inference(avatar_split_clause,[],[f5975,f5298,f5167,f5990])).

fof(f5975,plain,
    ( ~ r1_tarski(k6_subset_1(sK1,sK0),sK0)
    | spl5_26
    | ~ spl5_27 ),
    inference(unit_resulting_resolution,[],[f5169,f5300,f41])).

fof(f5988,plain,
    ( ~ spl5_29
    | ~ spl5_27 ),
    inference(avatar_split_clause,[],[f5976,f5298,f5985])).

fof(f5976,plain,
    ( ~ r1_tarski(k6_subset_1(sK1,sK0),k1_xboole_0)
    | ~ spl5_27 ),
    inference(unit_resulting_resolution,[],[f246,f5300,f41])).

fof(f5662,plain,
    ( ~ spl5_28
    | spl5_1 ),
    inference(avatar_split_clause,[],[f5644,f83,f5659])).

fof(f5659,plain,
    ( spl5_28
  <=> r2_hidden(sK3(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1))),k10_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).

fof(f83,plain,
    ( spl5_1
  <=> r1_tarski(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f5644,plain,
    ( ~ r2_hidden(sK3(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1))),k10_relat_1(sK2,sK1))
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f85,f107])).

fof(f85,plain,
    ( ~ r1_tarski(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1)))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f83])).

fof(f5301,plain,
    ( spl5_27
    | ~ spl5_25
    | spl5_26 ),
    inference(avatar_split_clause,[],[f5287,f5167,f5162,f5298])).

fof(f5162,plain,
    ( spl5_25
  <=> r2_hidden(sK3(sK1,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f5287,plain,
    ( r2_hidden(sK3(sK1,sK0),k6_subset_1(sK1,sK0))
    | ~ spl5_25
    | spl5_26 ),
    inference(unit_resulting_resolution,[],[f5164,f5169,f79])).

fof(f5164,plain,
    ( r2_hidden(sK3(sK1,sK0),sK1)
    | ~ spl5_25 ),
    inference(avatar_component_clause,[],[f5162])).

fof(f5171,plain,
    ( spl5_25
    | spl5_24 ),
    inference(avatar_split_clause,[],[f5141,f5137,f5162])).

fof(f5141,plain,
    ( r2_hidden(sK3(sK1,sK0),sK1)
    | spl5_24 ),
    inference(unit_resulting_resolution,[],[f5139,f42])).

fof(f5170,plain,
    ( ~ spl5_26
    | spl5_24 ),
    inference(avatar_split_clause,[],[f5142,f5137,f5167])).

fof(f5142,plain,
    ( ~ r2_hidden(sK3(sK1,sK0),sK0)
    | spl5_24 ),
    inference(unit_resulting_resolution,[],[f5139,f43])).

fof(f5165,plain,
    ( spl5_25
    | spl5_24 ),
    inference(avatar_split_clause,[],[f5144,f5137,f5162])).

fof(f5144,plain,
    ( r2_hidden(sK3(sK1,sK0),sK1)
    | spl5_24 ),
    inference(unit_resulting_resolution,[],[f77,f5139,f137])).

fof(f5140,plain,
    ( ~ spl5_24
    | spl5_18 ),
    inference(avatar_split_clause,[],[f5135,f3766,f5137])).

fof(f5135,plain,
    ( ~ r1_tarski(sK1,sK0)
    | spl5_18 ),
    inference(subsumption_resolution,[],[f5113,f77])).

fof(f5113,plain,
    ( ~ r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK0))
    | ~ r1_tarski(sK1,sK0)
    | spl5_18 ),
    inference(superposition,[],[f3768,f3898])).

fof(f3898,plain,(
    ! [X8,X7] :
      ( k2_xboole_0(X8,X7) = X8
      | ~ r1_tarski(X7,X8) ) ),
    inference(subsumption_resolution,[],[f3869,f97])).

fof(f3869,plain,(
    ! [X8,X7] :
      ( ~ r1_tarski(X7,X8)
      | ~ r1_tarski(X8,k2_xboole_0(X8,X7))
      | k2_xboole_0(X8,X7) = X8 ) ),
    inference(resolution,[],[f3777,f40])).

fof(f3777,plain,(
    ! [X2,X1] :
      ( r1_tarski(k2_xboole_0(X2,X1),X2)
      | ~ r1_tarski(X1,X2) ) ),
    inference(forward_demodulation,[],[f3606,f788])).

fof(f788,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(unit_resulting_resolution,[],[f97,f515,f40])).

fof(f515,plain,(
    ! [X0] : r1_tarski(k2_xboole_0(X0,k1_xboole_0),X0) ),
    inference(unit_resulting_resolution,[],[f77,f119,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f3606,plain,(
    ! [X2,X1] :
      ( r1_tarski(k2_xboole_0(X2,X1),k2_xboole_0(X2,k1_xboole_0))
      | ~ r1_tarski(X1,X2) ) ),
    inference(superposition,[],[f458,f2512])).

fof(f2512,plain,(
    ! [X14,X13] :
      ( k1_xboole_0 = k6_subset_1(X13,X14)
      | ~ r1_tarski(X13,X14) ) ),
    inference(resolution,[],[f1980,f132])).

fof(f1980,plain,(
    ! [X6,X4,X5] :
      ( r1_tarski(k6_subset_1(X4,X5),X6)
      | ~ r1_tarski(X4,X5) ) ),
    inference(resolution,[],[f1405,f69])).

fof(f1405,plain,(
    ! [X2,X3,X1] :
      ( r1_tarski(X3,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X3,X2) ) ),
    inference(superposition,[],[f46,f935])).

fof(f935,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(unit_resulting_resolution,[],[f467,f467,f40])).

fof(f467,plain,(
    ! [X0,X1] : r1_tarski(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) ),
    inference(unit_resulting_resolution,[],[f94,f97,f50])).

fof(f458,plain,(
    ! [X0,X1] : r1_tarski(k2_xboole_0(X0,X1),k2_xboole_0(X0,k6_subset_1(X1,X0))) ),
    inference(unit_resulting_resolution,[],[f97,f218,f50])).

fof(f218,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X1,k6_subset_1(X0,X1))) ),
    inference(unit_resulting_resolution,[],[f77,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k6_subset_1(X0,X1),X2)
      | r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(definition_unfolding,[],[f48,f34])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k4_xboole_0(X0,X1),X2)
      | r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f5006,plain,
    ( spl5_23
    | spl5_1 ),
    inference(avatar_split_clause,[],[f4943,f83,f5003])).

fof(f5003,plain,
    ( spl5_23
  <=> r2_hidden(sK3(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1))),k10_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f4943,plain,
    ( r2_hidden(sK3(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1))),k10_relat_1(sK2,sK0))
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f85,f154,f137])).

fof(f4126,plain,
    ( spl5_22
    | spl5_21 ),
    inference(avatar_split_clause,[],[f4121,f4112,f4123])).

fof(f4123,plain,
    ( spl5_22
  <=> r2_hidden(sK3(sK1,k1_xboole_0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f4112,plain,
    ( spl5_21
  <=> r1_tarski(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f4121,plain,
    ( r2_hidden(sK3(sK1,k1_xboole_0),sK1)
    | spl5_21 ),
    inference(unit_resulting_resolution,[],[f4114,f42])).

fof(f4114,plain,
    ( ~ r1_tarski(sK1,k1_xboole_0)
    | spl5_21 ),
    inference(avatar_component_clause,[],[f4112])).

fof(f4115,plain,
    ( ~ spl5_21
    | spl5_18 ),
    inference(avatar_split_clause,[],[f4110,f3766,f4112])).

fof(f4110,plain,
    ( ~ r1_tarski(sK1,k1_xboole_0)
    | spl5_18 ),
    inference(subsumption_resolution,[],[f4099,f77])).

fof(f4099,plain,
    ( ~ r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK0))
    | ~ r1_tarski(sK1,k1_xboole_0)
    | spl5_18 ),
    inference(superposition,[],[f3768,f3833])).

fof(f3833,plain,(
    ! [X6,X7] :
      ( k2_xboole_0(X7,X6) = X7
      | ~ r1_tarski(X6,k1_xboole_0) ) ),
    inference(subsumption_resolution,[],[f3808,f97])).

fof(f3808,plain,(
    ! [X6,X7] :
      ( ~ r1_tarski(X6,k1_xboole_0)
      | ~ r1_tarski(X7,k2_xboole_0(X7,X6))
      | k2_xboole_0(X7,X6) = X7 ) ),
    inference(resolution,[],[f3778,f40])).

fof(f3778,plain,(
    ! [X4,X3] :
      ( r1_tarski(k2_xboole_0(X4,X3),X4)
      | ~ r1_tarski(X3,k1_xboole_0) ) ),
    inference(forward_demodulation,[],[f3607,f788])).

fof(f3607,plain,(
    ! [X4,X3] :
      ( r1_tarski(k2_xboole_0(X4,X3),k2_xboole_0(X4,k1_xboole_0))
      | ~ r1_tarski(X3,k1_xboole_0) ) ),
    inference(superposition,[],[f458,f1944])).

fof(f1944,plain,(
    ! [X10,X9] :
      ( k1_xboole_0 = k6_subset_1(X9,X10)
      | ~ r1_tarski(X9,k1_xboole_0) ) ),
    inference(resolution,[],[f165,f132])).

fof(f165,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k6_subset_1(X0,X1),X2)
      | ~ r1_tarski(X0,X2) ) ),
    inference(resolution,[],[f69,f46])).

fof(f4109,plain,
    ( ~ spl5_20
    | spl5_18 ),
    inference(avatar_split_clause,[],[f4097,f3766,f4106])).

fof(f4106,plain,
    ( spl5_20
  <=> r2_hidden(sK3(k10_relat_1(sK2,sK0),k10_relat_1(sK2,k2_xboole_0(sK0,sK1))),k10_relat_1(sK2,k2_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f4097,plain,
    ( ~ r2_hidden(sK3(k10_relat_1(sK2,sK0),k10_relat_1(sK2,k2_xboole_0(sK0,sK1))),k10_relat_1(sK2,k2_xboole_0(sK0,sK1)))
    | spl5_18 ),
    inference(unit_resulting_resolution,[],[f3768,f43])).

fof(f4104,plain,
    ( spl5_19
    | spl5_18 ),
    inference(avatar_split_clause,[],[f4098,f3766,f4101])).

fof(f4101,plain,
    ( spl5_19
  <=> r2_hidden(sK3(k10_relat_1(sK2,sK0),k10_relat_1(sK2,k2_xboole_0(sK0,sK1))),k10_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f4098,plain,
    ( r2_hidden(sK3(k10_relat_1(sK2,sK0),k10_relat_1(sK2,k2_xboole_0(sK0,sK1))),k10_relat_1(sK2,sK0))
    | spl5_18 ),
    inference(unit_resulting_resolution,[],[f3768,f42])).

fof(f3769,plain,
    ( ~ spl5_18
    | spl5_14 ),
    inference(avatar_split_clause,[],[f3764,f2152,f3766])).

fof(f2152,plain,
    ( spl5_14
  <=> r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,k2_xboole_0(sK1,k6_subset_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f3764,plain,
    ( ~ r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,k2_xboole_0(sK0,sK1)))
    | spl5_14 ),
    inference(forward_demodulation,[],[f3756,f935])).

fof(f3756,plain,
    ( ~ r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,k2_xboole_0(sK1,sK0)))
    | spl5_14 ),
    inference(backward_demodulation,[],[f2154,f3642])).

fof(f3642,plain,(
    ! [X6,X7] : k2_xboole_0(X6,X7) = k2_xboole_0(X6,k6_subset_1(X7,X6)) ),
    inference(subsumption_resolution,[],[f3597,f570])).

fof(f570,plain,(
    ! [X2,X0,X1] : r1_tarski(k2_xboole_0(X0,k6_subset_1(X1,X2)),k2_xboole_0(X0,X1)) ),
    inference(unit_resulting_resolution,[],[f97,f155,f50])).

fof(f3597,plain,(
    ! [X6,X7] :
      ( ~ r1_tarski(k2_xboole_0(X6,k6_subset_1(X7,X6)),k2_xboole_0(X6,X7))
      | k2_xboole_0(X6,X7) = k2_xboole_0(X6,k6_subset_1(X7,X6)) ) ),
    inference(resolution,[],[f458,f40])).

fof(f2154,plain,
    ( ~ r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,k2_xboole_0(sK1,k6_subset_1(sK0,sK1))))
    | spl5_14 ),
    inference(avatar_component_clause,[],[f2152])).

fof(f2547,plain,
    ( ~ spl5_17
    | spl5_15 ),
    inference(avatar_split_clause,[],[f2536,f2522,f2544])).

fof(f2544,plain,
    ( spl5_17
  <=> r2_hidden(sK3(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f2522,plain,
    ( spl5_15
  <=> r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f2536,plain,
    ( ~ r2_hidden(sK3(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,sK1))
    | spl5_15 ),
    inference(unit_resulting_resolution,[],[f2524,f43])).

fof(f2524,plain,
    ( ~ r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
    | spl5_15 ),
    inference(avatar_component_clause,[],[f2522])).

fof(f2542,plain,
    ( spl5_16
    | spl5_15 ),
    inference(avatar_split_clause,[],[f2537,f2522,f2539])).

fof(f2539,plain,
    ( spl5_16
  <=> r2_hidden(sK3(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f2537,plain,
    ( r2_hidden(sK3(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,sK0))
    | spl5_15 ),
    inference(unit_resulting_resolution,[],[f2524,f42])).

fof(f2531,plain,
    ( ~ spl5_15
    | spl5_1 ),
    inference(avatar_split_clause,[],[f2508,f83,f2522])).

fof(f2508,plain,
    ( ~ r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
    | spl5_1 ),
    inference(resolution,[],[f1980,f85])).

fof(f2525,plain,
    ( ~ spl5_15
    | spl5_1 ),
    inference(avatar_split_clause,[],[f2506,f83,f2522])).

fof(f2506,plain,
    ( ~ r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f85,f1980])).

fof(f2155,plain,
    ( ~ spl5_14
    | ~ spl5_2
    | spl5_7 ),
    inference(avatar_split_clause,[],[f2150,f1895,f88,f2152])).

fof(f1895,plain,
    ( spl5_7
  <=> r1_tarski(k10_relat_1(sK2,sK0),k2_xboole_0(k10_relat_1(sK2,sK1),k10_relat_1(sK2,k6_subset_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f2150,plain,
    ( ~ r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,k2_xboole_0(sK1,k6_subset_1(sK0,sK1))))
    | ~ spl5_2
    | spl5_7 ),
    inference(backward_demodulation,[],[f1897,f2119])).

fof(f2119,plain,
    ( ! [X0,X1] : k10_relat_1(sK2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1))
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f90,f45])).

fof(f1897,plain,
    ( ~ r1_tarski(k10_relat_1(sK2,sK0),k2_xboole_0(k10_relat_1(sK2,sK1),k10_relat_1(sK2,k6_subset_1(sK0,sK1))))
    | spl5_7 ),
    inference(avatar_component_clause,[],[f1895])).

fof(f2117,plain,
    ( spl5_13
    | spl5_9 ),
    inference(avatar_split_clause,[],[f2112,f2082,f2114])).

fof(f2114,plain,
    ( spl5_13
  <=> r2_hidden(sK3(k10_relat_1(sK2,sK0),k1_xboole_0),k10_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f2082,plain,
    ( spl5_9
  <=> r1_tarski(k10_relat_1(sK2,sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f2112,plain,
    ( r2_hidden(sK3(k10_relat_1(sK2,sK0),k1_xboole_0),k10_relat_1(sK2,sK0))
    | spl5_9 ),
    inference(unit_resulting_resolution,[],[f2084,f42])).

fof(f2084,plain,
    ( ~ r1_tarski(k10_relat_1(sK2,sK0),k1_xboole_0)
    | spl5_9 ),
    inference(avatar_component_clause,[],[f2082])).

fof(f2105,plain,
    ( spl5_12
    | spl5_10 ),
    inference(avatar_split_clause,[],[f2100,f2087,f2102])).

fof(f2102,plain,
    ( spl5_12
  <=> r2_hidden(sK3(sK0,k1_xboole_0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f2087,plain,
    ( spl5_10
  <=> r1_tarski(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f2100,plain,
    ( r2_hidden(sK3(sK0,k1_xboole_0),sK0)
    | spl5_10 ),
    inference(unit_resulting_resolution,[],[f2089,f42])).

fof(f2089,plain,
    ( ~ r1_tarski(sK0,k1_xboole_0)
    | spl5_10 ),
    inference(avatar_component_clause,[],[f2087])).

fof(f2094,plain,
    ( ~ spl5_10
    | ~ spl5_11
    | spl5_1 ),
    inference(avatar_split_clause,[],[f2071,f83,f2091,f2087])).

fof(f2091,plain,
    ( spl5_11
  <=> r1_tarski(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f2071,plain,
    ( ~ r1_tarski(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k1_xboole_0))
    | ~ r1_tarski(sK0,k1_xboole_0)
    | spl5_1 ),
    inference(superposition,[],[f85,f1944])).

fof(f2085,plain,
    ( ~ spl5_9
    | spl5_1 ),
    inference(avatar_split_clause,[],[f2080,f83,f2082])).

fof(f2080,plain,
    ( ~ r1_tarski(k10_relat_1(sK2,sK0),k1_xboole_0)
    | spl5_1 ),
    inference(subsumption_resolution,[],[f2070,f119])).

fof(f2070,plain,
    ( ~ r1_tarski(k1_xboole_0,k10_relat_1(sK2,k6_subset_1(sK0,sK1)))
    | ~ r1_tarski(k10_relat_1(sK2,sK0),k1_xboole_0)
    | spl5_1 ),
    inference(superposition,[],[f85,f1944])).

fof(f1958,plain,
    ( ~ spl5_8
    | spl5_1 ),
    inference(avatar_split_clause,[],[f1941,f83,f1953])).

fof(f1953,plain,
    ( spl5_8
  <=> r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,k6_subset_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f1941,plain,
    ( ~ r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,k6_subset_1(sK0,sK1)))
    | spl5_1 ),
    inference(resolution,[],[f165,f85])).

fof(f1956,plain,
    ( ~ spl5_8
    | spl5_1 ),
    inference(avatar_split_clause,[],[f1939,f83,f1953])).

fof(f1939,plain,
    ( ~ r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,k6_subset_1(sK0,sK1)))
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f85,f165])).

fof(f1898,plain,
    ( ~ spl5_7
    | spl5_1 ),
    inference(avatar_split_clause,[],[f1874,f83,f1895])).

fof(f1874,plain,
    ( ~ r1_tarski(k10_relat_1(sK2,sK0),k2_xboole_0(k10_relat_1(sK2,sK1),k10_relat_1(sK2,k6_subset_1(sK0,sK1))))
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f85,f69])).

fof(f1893,plain,
    ( ~ spl5_6
    | spl5_1 ),
    inference(avatar_split_clause,[],[f1875,f83,f1890])).

fof(f1890,plain,
    ( spl5_6
  <=> r1_tarski(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f1875,plain,
    ( ~ r1_tarski(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k1_xboole_0)
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f85,f860])).

fof(f860,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,k1_xboole_0)
      | r1_tarski(X1,X0) ) ),
    inference(superposition,[],[f46,f788])).

fof(f1888,plain,
    ( ~ spl5_5
    | spl5_1 ),
    inference(avatar_split_clause,[],[f1877,f83,f1885])).

fof(f1885,plain,
    ( spl5_5
  <=> r2_hidden(sK3(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1))),k10_relat_1(sK2,k6_subset_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f1877,plain,
    ( ~ r2_hidden(sK3(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1))),k10_relat_1(sK2,k6_subset_1(sK0,sK1)))
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f85,f43])).

fof(f1883,plain,
    ( spl5_4
    | spl5_1 ),
    inference(avatar_split_clause,[],[f1878,f83,f1880])).

fof(f1880,plain,
    ( spl5_4
  <=> r2_hidden(sK3(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1))),k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f1878,plain,
    ( r2_hidden(sK3(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1))),k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f85,f42])).

fof(f289,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f274,f284])).

fof(f284,plain,
    ( spl5_3
  <=> k1_xboole_0 = k2_xboole_0(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f274,plain,(
    k1_xboole_0 = k2_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f97,f266,f40])).

fof(f266,plain,(
    ! [X0] : r1_tarski(k2_xboole_0(k1_xboole_0,X0),X0) ),
    inference(superposition,[],[f163,f67])).

fof(f288,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f275,f284])).

fof(f275,plain,(
    k1_xboole_0 = k2_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f119,f266,f40])).

fof(f287,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f277,f284])).

fof(f277,plain,(
    k1_xboole_0 = k2_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f266,f132])).

fof(f91,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f31,f88])).

fof(f31,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)),k10_relat_1(X2,k6_subset_1(X0,X1)))
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => r1_tarski(k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)),k10_relat_1(X2,k6_subset_1(X0,X1))) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)),k10_relat_1(X2,k6_subset_1(X0,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t177_relat_1)).

fof(f86,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f32,f83])).

fof(f32,plain,(
    ~ r1_tarski(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:07:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.43  % (4513)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.55  % (4498)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.55  % (4490)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.57  % (4494)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.58  % (4484)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.58  % (4488)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.58  % (4486)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.58  % (4500)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.58  % (4485)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.58  % (4506)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.58  % (4506)Refutation not found, incomplete strategy% (4506)------------------------------
% 0.22/0.58  % (4506)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.58  % (4506)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.58  
% 0.22/0.58  % (4506)Memory used [KB]: 10746
% 0.22/0.58  % (4506)Time elapsed: 0.153 s
% 0.22/0.58  % (4506)------------------------------
% 0.22/0.58  % (4506)------------------------------
% 0.22/0.58  % (4487)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.58  % (4503)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.59  % (4509)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.59  % (4494)Refutation not found, incomplete strategy% (4494)------------------------------
% 0.22/0.59  % (4494)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.59  % (4494)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.59  
% 0.22/0.59  % (4494)Memory used [KB]: 10618
% 0.22/0.59  % (4494)Time elapsed: 0.161 s
% 0.22/0.59  % (4494)------------------------------
% 0.22/0.59  % (4494)------------------------------
% 0.22/0.59  % (4508)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.59  % (4501)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.59  % (4496)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.59  % (4492)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.60  % (4504)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.60  % (4510)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.60  % (4511)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.60  % (4493)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.60  % (4507)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.60  % (4502)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.85/0.61  % (4505)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.85/0.61  % (4491)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.85/0.61  % (4489)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.85/0.62  % (4512)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.85/0.62  % (4495)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.85/0.62  % (4495)Refutation not found, incomplete strategy% (4495)------------------------------
% 1.85/0.62  % (4495)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.85/0.62  % (4495)Termination reason: Refutation not found, incomplete strategy
% 1.85/0.62  
% 1.85/0.62  % (4495)Memory used [KB]: 10618
% 1.85/0.62  % (4495)Time elapsed: 0.191 s
% 1.85/0.62  % (4495)------------------------------
% 1.85/0.62  % (4495)------------------------------
% 1.85/0.63  % (4499)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 2.01/0.64  % (4497)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 2.23/0.72  % (4540)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.69/0.74  % (4541)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.97/0.79  % (4544)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.97/0.84  % (4489)Time limit reached!
% 2.97/0.84  % (4489)------------------------------
% 2.97/0.84  % (4489)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.97/0.84  % (4489)Termination reason: Time limit
% 2.97/0.84  % (4489)Termination phase: Saturation
% 2.97/0.84  
% 2.97/0.84  % (4489)Memory used [KB]: 8571
% 2.97/0.84  % (4489)Time elapsed: 0.400 s
% 2.97/0.84  % (4489)------------------------------
% 2.97/0.84  % (4489)------------------------------
% 3.64/0.92  % (4501)Time limit reached!
% 3.64/0.92  % (4501)------------------------------
% 3.64/0.92  % (4501)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.64/0.92  % (4501)Termination reason: Time limit
% 3.64/0.92  
% 3.64/0.92  % (4501)Memory used [KB]: 14072
% 3.64/0.92  % (4501)Time elapsed: 0.507 s
% 3.64/0.92  % (4501)------------------------------
% 3.64/0.92  % (4501)------------------------------
% 4.03/0.93  % (4484)Time limit reached!
% 4.03/0.93  % (4484)------------------------------
% 4.03/0.93  % (4484)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.03/0.93  % (4484)Termination reason: Time limit
% 4.03/0.93  % (4484)Termination phase: Saturation
% 4.03/0.93  
% 4.03/0.93  % (4484)Memory used [KB]: 3709
% 4.03/0.93  % (4484)Time elapsed: 0.500 s
% 4.03/0.93  % (4484)------------------------------
% 4.03/0.93  % (4484)------------------------------
% 4.03/0.95  % (4496)Time limit reached!
% 4.03/0.95  % (4496)------------------------------
% 4.03/0.95  % (4496)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.03/0.95  % (4496)Termination reason: Time limit
% 4.03/0.95  
% 4.03/0.95  % (4496)Memory used [KB]: 8443
% 4.03/0.95  % (4496)Time elapsed: 0.517 s
% 4.03/0.95  % (4496)------------------------------
% 4.03/0.95  % (4496)------------------------------
% 4.26/0.97  % (4546)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 4.26/0.97  % (4485)Time limit reached!
% 4.26/0.97  % (4485)------------------------------
% 4.26/0.97  % (4485)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.26/0.97  % (4485)Termination reason: Time limit
% 4.26/0.97  
% 4.26/0.97  % (4485)Memory used [KB]: 8187
% 4.26/0.97  % (4485)Time elapsed: 0.506 s
% 4.26/0.97  % (4485)------------------------------
% 4.26/0.97  % (4485)------------------------------
% 4.68/1.04  % (4491)Time limit reached!
% 4.68/1.04  % (4491)------------------------------
% 4.68/1.04  % (4491)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.68/1.04  % (4491)Termination reason: Time limit
% 4.68/1.04  
% 4.68/1.04  % (4491)Memory used [KB]: 10106
% 4.68/1.04  % (4491)Time elapsed: 0.607 s
% 4.68/1.04  % (4491)------------------------------
% 4.68/1.04  % (4491)------------------------------
% 4.68/1.05  % (4512)Time limit reached!
% 4.68/1.05  % (4512)------------------------------
% 4.68/1.05  % (4512)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.68/1.05  % (4512)Termination reason: Time limit
% 4.68/1.05  % (4512)Termination phase: Saturation
% 4.68/1.05  
% 4.68/1.05  % (4512)Memory used [KB]: 8827
% 4.68/1.05  % (4512)Time elapsed: 0.600 s
% 4.68/1.05  % (4512)------------------------------
% 4.68/1.05  % (4512)------------------------------
% 4.68/1.05  % (4500)Time limit reached!
% 4.68/1.05  % (4500)------------------------------
% 4.68/1.05  % (4500)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.68/1.05  % (4500)Termination reason: Time limit
% 4.68/1.05  
% 4.68/1.05  % (4500)Memory used [KB]: 16630
% 4.68/1.05  % (4500)Time elapsed: 0.615 s
% 4.68/1.05  % (4500)------------------------------
% 4.68/1.05  % (4500)------------------------------
% 4.68/1.07  % (4552)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 4.92/1.07  % (4551)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 4.92/1.07  % (4549)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 4.92/1.09  % (4548)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 6.13/1.16  % (4556)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 6.36/1.18  % (4553)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 6.36/1.21  % (4561)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 6.36/1.22  % (4505)Time limit reached!
% 6.36/1.22  % (4505)------------------------------
% 6.36/1.22  % (4505)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.36/1.22  % (4505)Termination reason: Time limit
% 6.36/1.22  % (4505)Termination phase: Saturation
% 6.36/1.22  
% 6.36/1.22  % (4505)Memory used [KB]: 6268
% 6.36/1.22  % (4505)Time elapsed: 0.800 s
% 6.36/1.22  % (4505)------------------------------
% 6.36/1.22  % (4505)------------------------------
% 7.44/1.34  % (4498)Refutation found. Thanks to Tanya!
% 7.44/1.34  % SZS status Theorem for theBenchmark
% 7.44/1.34  % SZS output start Proof for theBenchmark
% 7.44/1.34  fof(f9665,plain,(
% 7.44/1.34    $false),
% 7.44/1.34    inference(avatar_sat_refutation,[],[f86,f91,f287,f288,f289,f1883,f1888,f1893,f1898,f1956,f1958,f2085,f2094,f2105,f2117,f2155,f2525,f2531,f2542,f2547,f3769,f4104,f4109,f4115,f4126,f5006,f5140,f5165,f5170,f5171,f5301,f5662,f5988,f5993,f5999,f6041,f6046,f6047,f6053,f6054,f6093,f6098,f6103,f6104,f6106,f6107,f8827,f8833,f9018,f9023,f9028,f9029,f9035,f9036,f9082,f9087,f9092,f9097,f9098,f9100,f9101,f9411,f9469,f9662,f9664])).
% 7.44/1.34  fof(f9664,plain,(
% 7.44/1.34    ~spl5_2 | spl5_18),
% 7.44/1.34    inference(avatar_contradiction_clause,[],[f9663])).
% 7.44/1.34  fof(f9663,plain,(
% 7.44/1.34    $false | (~spl5_2 | spl5_18)),
% 7.44/1.34    inference(subsumption_resolution,[],[f9618,f90])).
% 7.44/1.34  fof(f90,plain,(
% 7.44/1.34    v1_relat_1(sK2) | ~spl5_2),
% 7.44/1.34    inference(avatar_component_clause,[],[f88])).
% 7.44/1.34  fof(f88,plain,(
% 7.44/1.34    spl5_2 <=> v1_relat_1(sK2)),
% 7.44/1.34    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 7.44/1.34  fof(f9618,plain,(
% 7.44/1.34    ~v1_relat_1(sK2) | spl5_18),
% 7.44/1.34    inference(unit_resulting_resolution,[],[f3768,f77,f2125])).
% 7.44/1.34  fof(f2125,plain,(
% 7.44/1.34    ( ! [X6,X8,X7,X9] : (~r1_tarski(k10_relat_1(X6,k2_xboole_0(X7,X8)),X9) | r1_tarski(k10_relat_1(X6,X7),X9) | ~v1_relat_1(X6)) )),
% 7.44/1.34    inference(superposition,[],[f49,f45])).
% 7.44/1.34  fof(f45,plain,(
% 7.44/1.34    ( ! [X2,X0,X1] : (k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 7.44/1.34    inference(cnf_transformation,[],[f24])).
% 7.44/1.34  fof(f24,plain,(
% 7.44/1.34    ! [X0,X1,X2] : (k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 7.44/1.34    inference(ennf_transformation,[],[f19])).
% 7.44/1.34  fof(f19,axiom,(
% 7.44/1.34    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))),
% 7.44/1.34    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_relat_1)).
% 7.44/1.34  fof(f49,plain,(
% 7.44/1.34    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 7.44/1.34    inference(cnf_transformation,[],[f28])).
% 7.44/1.34  fof(f28,plain,(
% 7.44/1.34    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 7.44/1.34    inference(ennf_transformation,[],[f6])).
% 7.44/1.34  fof(f6,axiom,(
% 7.44/1.34    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 7.44/1.34    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).
% 7.44/1.34  fof(f77,plain,(
% 7.44/1.34    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.44/1.34    inference(equality_resolution,[],[f39])).
% 7.44/1.34  fof(f39,plain,(
% 7.44/1.34    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 7.44/1.34    inference(cnf_transformation,[],[f3])).
% 7.44/1.34  fof(f3,axiom,(
% 7.44/1.34    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.44/1.34    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 7.44/1.34  fof(f3768,plain,(
% 7.44/1.34    ~r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,k2_xboole_0(sK0,sK1))) | spl5_18),
% 7.44/1.34    inference(avatar_component_clause,[],[f3766])).
% 7.44/1.34  fof(f3766,plain,(
% 7.44/1.34    spl5_18 <=> r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,k2_xboole_0(sK0,sK1)))),
% 7.44/1.34    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 7.44/1.34  fof(f9662,plain,(
% 7.44/1.34    ~spl5_2 | spl5_18),
% 7.44/1.34    inference(avatar_contradiction_clause,[],[f9619])).
% 7.44/1.34  fof(f9619,plain,(
% 7.44/1.34    $false | (~spl5_2 | spl5_18)),
% 7.44/1.34    inference(unit_resulting_resolution,[],[f90,f3768,f77,f2125])).
% 7.44/1.34  fof(f9469,plain,(
% 7.44/1.34    spl5_49 | spl5_24 | spl5_26),
% 7.44/1.34    inference(avatar_split_clause,[],[f9424,f5167,f5137,f9466])).
% 7.44/1.34  fof(f9466,plain,(
% 7.44/1.34    spl5_49 <=> r2_hidden(sK3(k6_subset_1(k2_xboole_0(sK0,sK1),sK0),k1_xboole_0),sK1)),
% 7.44/1.34    introduced(avatar_definition,[new_symbols(naming,[spl5_49])])).
% 7.44/1.34  fof(f5137,plain,(
% 7.44/1.34    spl5_24 <=> r1_tarski(sK1,sK0)),
% 7.44/1.34    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 7.44/1.34  fof(f5167,plain,(
% 7.44/1.34    spl5_26 <=> r2_hidden(sK3(sK1,sK0),sK0)),
% 7.44/1.34    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).
% 7.44/1.34  fof(f9424,plain,(
% 7.44/1.34    r2_hidden(sK3(k6_subset_1(k2_xboole_0(sK0,sK1),sK0),k1_xboole_0),sK1) | (spl5_24 | spl5_26)),
% 7.44/1.34    inference(unit_resulting_resolution,[],[f163,f7761,f137])).
% 7.44/1.34  fof(f137,plain,(
% 7.44/1.34    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1),X2) | ~r1_tarski(X0,X2) | r1_tarski(X0,X1)) )),
% 7.44/1.34    inference(resolution,[],[f41,f42])).
% 7.44/1.34  fof(f42,plain,(
% 7.44/1.34    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 7.44/1.34    inference(cnf_transformation,[],[f23])).
% 7.44/1.34  fof(f23,plain,(
% 7.44/1.34    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 7.44/1.34    inference(ennf_transformation,[],[f1])).
% 7.44/1.34  fof(f1,axiom,(
% 7.44/1.34    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 7.44/1.34    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 7.44/1.34  fof(f41,plain,(
% 7.44/1.34    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 7.44/1.34    inference(cnf_transformation,[],[f23])).
% 7.44/1.34  fof(f7761,plain,(
% 7.44/1.34    ( ! [X0] : (~r1_tarski(k6_subset_1(k2_xboole_0(X0,sK1),sK0),k1_xboole_0)) ) | (spl5_24 | spl5_26)),
% 7.44/1.34    inference(unit_resulting_resolution,[],[f5169,f246,f5145,f1318])).
% 7.44/1.34  fof(f1318,plain,(
% 7.44/1.34    ( ! [X14,X12,X15,X13] : (~r1_tarski(k6_subset_1(X14,X13),X15) | ~r2_hidden(X12,X14) | r2_hidden(X12,X15) | r2_hidden(X12,X13)) )),
% 7.44/1.34    inference(resolution,[],[f79,f41])).
% 7.44/1.34  fof(f79,plain,(
% 7.44/1.34    ( ! [X0,X3,X1] : (r2_hidden(X3,k6_subset_1(X0,X1)) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) )),
% 7.44/1.34    inference(equality_resolution,[],[f71])).
% 7.44/1.34  fof(f71,plain,(
% 7.44/1.34    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | r2_hidden(X3,X2) | k6_subset_1(X0,X1) != X2) )),
% 7.44/1.34    inference(definition_unfolding,[],[f56,f34])).
% 7.44/1.34  fof(f34,plain,(
% 7.44/1.34    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 7.44/1.34    inference(cnf_transformation,[],[f17])).
% 7.44/1.34  fof(f17,axiom,(
% 7.44/1.34    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 7.44/1.34    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 7.44/1.34  fof(f56,plain,(
% 7.44/1.34    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 7.44/1.34    inference(cnf_transformation,[],[f2])).
% 7.44/1.34  fof(f2,axiom,(
% 7.44/1.34    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 7.44/1.34    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 7.44/1.34  fof(f5145,plain,(
% 7.44/1.34    ( ! [X0] : (r2_hidden(sK3(sK1,sK0),k2_xboole_0(X0,sK1))) ) | spl5_24),
% 7.44/1.34    inference(unit_resulting_resolution,[],[f94,f5139,f137])).
% 7.44/1.34  fof(f5139,plain,(
% 7.44/1.34    ~r1_tarski(sK1,sK0) | spl5_24),
% 7.44/1.34    inference(avatar_component_clause,[],[f5137])).
% 7.44/1.34  fof(f94,plain,(
% 7.44/1.34    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X0))) )),
% 7.44/1.34    inference(unit_resulting_resolution,[],[f77,f46])).
% 7.44/1.34  fof(f46,plain,(
% 7.44/1.34    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 7.44/1.34    inference(cnf_transformation,[],[f25])).
% 7.44/1.34  fof(f25,plain,(
% 7.44/1.34    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 7.44/1.34    inference(ennf_transformation,[],[f5])).
% 7.44/1.34  fof(f5,axiom,(
% 7.44/1.34    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 7.44/1.34    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).
% 7.44/1.34  fof(f246,plain,(
% 7.44/1.34    ( ! [X4] : (~r2_hidden(X4,k1_xboole_0)) )),
% 7.44/1.34    inference(subsumption_resolution,[],[f244,f108])).
% 7.44/1.34  fof(f108,plain,(
% 7.44/1.34    ( ! [X0,X1] : (~r2_hidden(X1,k1_xboole_0) | ~r2_hidden(X1,X0)) )),
% 7.44/1.34    inference(superposition,[],[f80,f67])).
% 7.44/1.34  fof(f67,plain,(
% 7.44/1.34    ( ! [X0] : (k6_subset_1(X0,k1_xboole_0) = X0) )),
% 7.44/1.34    inference(definition_unfolding,[],[f33,f34])).
% 7.44/1.34  fof(f33,plain,(
% 7.44/1.34    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 7.44/1.34    inference(cnf_transformation,[],[f7])).
% 7.44/1.34  fof(f7,axiom,(
% 7.44/1.34    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 7.44/1.34    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 7.44/1.34  fof(f80,plain,(
% 7.44/1.34    ( ! [X0,X3,X1] : (~r2_hidden(X3,k6_subset_1(X0,X1)) | ~r2_hidden(X3,X1)) )),
% 7.44/1.34    inference(equality_resolution,[],[f72])).
% 7.44/1.34  fof(f72,plain,(
% 7.44/1.34    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k6_subset_1(X0,X1) != X2) )),
% 7.44/1.34    inference(definition_unfolding,[],[f55,f34])).
% 7.44/1.34  fof(f55,plain,(
% 7.44/1.34    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 7.44/1.34    inference(cnf_transformation,[],[f2])).
% 7.44/1.34  fof(f244,plain,(
% 7.44/1.34    ( ! [X4,X3] : (~r2_hidden(X4,k1_xboole_0) | r2_hidden(X4,X3)) )),
% 7.44/1.34    inference(superposition,[],[f81,f196])).
% 7.44/1.34  fof(f196,plain,(
% 7.44/1.34    ( ! [X0] : (k1_xboole_0 = k6_subset_1(X0,X0)) )),
% 7.44/1.34    inference(unit_resulting_resolution,[],[f160,f132])).
% 7.44/1.34  fof(f132,plain,(
% 7.44/1.34    ( ! [X17] : (~r1_tarski(X17,k1_xboole_0) | k1_xboole_0 = X17) )),
% 7.44/1.34    inference(resolution,[],[f40,f119])).
% 7.44/1.34  fof(f119,plain,(
% 7.44/1.34    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 7.44/1.34    inference(duplicate_literal_removal,[],[f118])).
% 7.44/1.34  fof(f118,plain,(
% 7.44/1.34    ( ! [X0] : (r1_tarski(k1_xboole_0,X0) | r1_tarski(k1_xboole_0,X0)) )),
% 7.44/1.34    inference(resolution,[],[f109,f42])).
% 7.44/1.34  fof(f109,plain,(
% 7.44/1.34    ( ! [X0,X1] : (~r2_hidden(sK3(k1_xboole_0,X0),X1) | r1_tarski(k1_xboole_0,X0)) )),
% 7.44/1.34    inference(resolution,[],[f108,f42])).
% 7.44/1.34  fof(f40,plain,(
% 7.44/1.34    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 7.44/1.34    inference(cnf_transformation,[],[f3])).
% 7.44/1.34  fof(f160,plain,(
% 7.44/1.34    ( ! [X0,X1] : (r1_tarski(k6_subset_1(X0,X0),X1)) )),
% 7.44/1.34    inference(unit_resulting_resolution,[],[f97,f69])).
% 7.44/1.34  fof(f69,plain,(
% 7.44/1.34    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_xboole_0(X1,X2)) | r1_tarski(k6_subset_1(X0,X1),X2)) )),
% 7.44/1.34    inference(definition_unfolding,[],[f47,f34])).
% 7.44/1.34  fof(f47,plain,(
% 7.44/1.34    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_xboole_0(X1,X2)) | r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 7.44/1.34    inference(cnf_transformation,[],[f26])).
% 7.44/1.34  fof(f26,plain,(
% 7.44/1.34    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 7.44/1.34    inference(ennf_transformation,[],[f8])).
% 7.44/1.34  fof(f8,axiom,(
% 7.44/1.34    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 7.44/1.34    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).
% 7.44/1.34  fof(f97,plain,(
% 7.44/1.34    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 7.44/1.34    inference(unit_resulting_resolution,[],[f77,f49])).
% 7.44/1.34  fof(f81,plain,(
% 7.44/1.34    ( ! [X0,X3,X1] : (~r2_hidden(X3,k6_subset_1(X0,X1)) | r2_hidden(X3,X0)) )),
% 7.44/1.34    inference(equality_resolution,[],[f73])).
% 7.44/1.34  fof(f73,plain,(
% 7.44/1.34    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,X2) | k6_subset_1(X0,X1) != X2) )),
% 7.44/1.34    inference(definition_unfolding,[],[f54,f34])).
% 7.44/1.34  fof(f54,plain,(
% 7.44/1.34    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 7.44/1.34    inference(cnf_transformation,[],[f2])).
% 7.44/1.34  fof(f5169,plain,(
% 7.44/1.34    ~r2_hidden(sK3(sK1,sK0),sK0) | spl5_26),
% 7.44/1.34    inference(avatar_component_clause,[],[f5167])).
% 7.44/1.34  fof(f163,plain,(
% 7.44/1.34    ( ! [X0,X1] : (r1_tarski(k6_subset_1(k2_xboole_0(X0,X1),X0),X1)) )),
% 7.44/1.34    inference(unit_resulting_resolution,[],[f77,f69])).
% 7.44/1.34  fof(f9411,plain,(
% 7.44/1.34    spl5_48 | spl5_24 | spl5_26),
% 7.44/1.34    inference(avatar_split_clause,[],[f9369,f5167,f5137,f9408])).
% 7.44/1.34  fof(f9408,plain,(
% 7.44/1.34    spl5_48 <=> r2_hidden(sK3(k6_subset_1(k2_xboole_0(sK0,sK1),sK0),sK0),sK1)),
% 7.44/1.34    introduced(avatar_definition,[new_symbols(naming,[spl5_48])])).
% 7.44/1.34  fof(f9369,plain,(
% 7.44/1.34    r2_hidden(sK3(k6_subset_1(k2_xboole_0(sK0,sK1),sK0),sK0),sK1) | (spl5_24 | spl5_26)),
% 7.44/1.34    inference(unit_resulting_resolution,[],[f163,f7757,f137])).
% 7.44/1.34  fof(f7757,plain,(
% 7.44/1.34    ( ! [X0] : (~r1_tarski(k6_subset_1(k2_xboole_0(X0,sK1),sK0),sK0)) ) | (spl5_24 | spl5_26)),
% 7.44/1.34    inference(unit_resulting_resolution,[],[f5169,f5169,f5145,f1318])).
% 7.44/1.34  fof(f9101,plain,(
% 7.44/1.34    spl5_46 | spl5_39),
% 7.44/1.34    inference(avatar_split_clause,[],[f9037,f8830,f9089])).
% 7.44/1.34  fof(f9089,plain,(
% 7.44/1.34    spl5_46 <=> r2_hidden(sK3(k6_subset_1(k6_subset_1(sK1,sK0),sK0),sK0),k6_subset_1(sK1,sK0))),
% 7.44/1.34    introduced(avatar_definition,[new_symbols(naming,[spl5_46])])).
% 7.44/1.34  fof(f8830,plain,(
% 7.44/1.34    spl5_39 <=> r1_tarski(k6_subset_1(k6_subset_1(sK1,sK0),sK0),sK0)),
% 7.44/1.34    introduced(avatar_definition,[new_symbols(naming,[spl5_39])])).
% 7.44/1.34  fof(f9037,plain,(
% 7.44/1.34    r2_hidden(sK3(k6_subset_1(k6_subset_1(sK1,sK0),sK0),sK0),k6_subset_1(sK1,sK0)) | spl5_39),
% 7.44/1.34    inference(unit_resulting_resolution,[],[f8832,f116])).
% 7.44/1.34  fof(f116,plain,(
% 7.44/1.34    ( ! [X2,X0,X1] : (r2_hidden(sK3(k6_subset_1(X0,X1),X2),X0) | r1_tarski(k6_subset_1(X0,X1),X2)) )),
% 7.44/1.34    inference(resolution,[],[f81,f42])).
% 7.44/1.34  fof(f8832,plain,(
% 7.44/1.34    ~r1_tarski(k6_subset_1(k6_subset_1(sK1,sK0),sK0),sK0) | spl5_39),
% 7.44/1.34    inference(avatar_component_clause,[],[f8830])).
% 7.44/1.34  fof(f9100,plain,(
% 7.44/1.34    ~spl5_47 | spl5_39),
% 7.44/1.34    inference(avatar_split_clause,[],[f9038,f8830,f9094])).
% 7.44/1.34  fof(f9094,plain,(
% 7.44/1.34    spl5_47 <=> r2_hidden(sK3(k6_subset_1(k6_subset_1(sK1,sK0),sK0),sK0),sK0)),
% 7.44/1.34    introduced(avatar_definition,[new_symbols(naming,[spl5_47])])).
% 7.44/1.34  fof(f9038,plain,(
% 7.44/1.34    ~r2_hidden(sK3(k6_subset_1(k6_subset_1(sK1,sK0),sK0),sK0),sK0) | spl5_39),
% 7.44/1.34    inference(unit_resulting_resolution,[],[f8832,f107])).
% 7.44/1.34  fof(f107,plain,(
% 7.44/1.34    ( ! [X2,X0,X1] : (~r2_hidden(sK3(k6_subset_1(X0,X1),X2),X1) | r1_tarski(k6_subset_1(X0,X1),X2)) )),
% 7.44/1.34    inference(resolution,[],[f80,f42])).
% 7.44/1.34  fof(f9098,plain,(
% 7.44/1.34    spl5_44 | spl5_39),
% 7.44/1.34    inference(avatar_split_clause,[],[f9043,f8830,f9079])).
% 7.44/1.34  fof(f9079,plain,(
% 7.44/1.34    spl5_44 <=> r2_hidden(sK3(k6_subset_1(k6_subset_1(sK1,sK0),sK0),sK0),k6_subset_1(k6_subset_1(sK1,sK0),sK0))),
% 7.44/1.34    introduced(avatar_definition,[new_symbols(naming,[spl5_44])])).
% 7.44/1.34  fof(f9043,plain,(
% 7.44/1.34    r2_hidden(sK3(k6_subset_1(k6_subset_1(sK1,sK0),sK0),sK0),k6_subset_1(k6_subset_1(sK1,sK0),sK0)) | spl5_39),
% 7.44/1.34    inference(unit_resulting_resolution,[],[f8832,f42])).
% 7.44/1.34  fof(f9097,plain,(
% 7.44/1.34    ~spl5_47 | spl5_39),
% 7.44/1.34    inference(avatar_split_clause,[],[f9044,f8830,f9094])).
% 7.44/1.34  fof(f9044,plain,(
% 7.44/1.34    ~r2_hidden(sK3(k6_subset_1(k6_subset_1(sK1,sK0),sK0),sK0),sK0) | spl5_39),
% 7.44/1.34    inference(unit_resulting_resolution,[],[f8832,f43])).
% 7.44/1.34  fof(f43,plain,(
% 7.44/1.34    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 7.44/1.34    inference(cnf_transformation,[],[f23])).
% 7.44/1.34  fof(f9092,plain,(
% 7.44/1.34    spl5_46 | spl5_39),
% 7.44/1.34    inference(avatar_split_clause,[],[f9046,f8830,f9089])).
% 7.44/1.34  fof(f9046,plain,(
% 7.44/1.34    r2_hidden(sK3(k6_subset_1(k6_subset_1(sK1,sK0),sK0),sK0),k6_subset_1(sK1,sK0)) | spl5_39),
% 7.44/1.34    inference(unit_resulting_resolution,[],[f154,f8832,f137])).
% 7.44/1.34  fof(f154,plain,(
% 7.44/1.34    ( ! [X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X0)) )),
% 7.44/1.34    inference(unit_resulting_resolution,[],[f94,f69])).
% 7.44/1.34  fof(f9087,plain,(
% 7.44/1.34    spl5_45 | spl5_39),
% 7.44/1.34    inference(avatar_split_clause,[],[f9047,f8830,f9084])).
% 7.44/1.34  fof(f9084,plain,(
% 7.44/1.34    spl5_45 <=> r2_hidden(sK3(k6_subset_1(k6_subset_1(sK1,sK0),sK0),sK0),sK1)),
% 7.44/1.34    introduced(avatar_definition,[new_symbols(naming,[spl5_45])])).
% 7.44/1.34  fof(f9047,plain,(
% 7.44/1.34    r2_hidden(sK3(k6_subset_1(k6_subset_1(sK1,sK0),sK0),sK0),sK1) | spl5_39),
% 7.44/1.34    inference(unit_resulting_resolution,[],[f329,f8832,f137])).
% 7.44/1.34  fof(f329,plain,(
% 7.44/1.34    ( ! [X2,X0,X1] : (r1_tarski(k6_subset_1(k6_subset_1(X0,X1),X2),X0)) )),
% 7.44/1.34    inference(unit_resulting_resolution,[],[f155,f69])).
% 7.44/1.34  fof(f155,plain,(
% 7.44/1.34    ( ! [X2,X0,X1] : (r1_tarski(k6_subset_1(X0,X1),k2_xboole_0(X2,X0))) )),
% 7.44/1.34    inference(unit_resulting_resolution,[],[f95,f69])).
% 7.44/1.34  fof(f95,plain,(
% 7.44/1.34    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,k2_xboole_0(X2,X0)))) )),
% 7.44/1.34    inference(unit_resulting_resolution,[],[f94,f46])).
% 7.44/1.34  fof(f9082,plain,(
% 7.44/1.34    spl5_44 | spl5_39),
% 7.44/1.34    inference(avatar_split_clause,[],[f9050,f8830,f9079])).
% 7.44/1.34  fof(f9050,plain,(
% 7.44/1.34    r2_hidden(sK3(k6_subset_1(k6_subset_1(sK1,sK0),sK0),sK0),k6_subset_1(k6_subset_1(sK1,sK0),sK0)) | spl5_39),
% 7.44/1.34    inference(unit_resulting_resolution,[],[f77,f8832,f137])).
% 7.44/1.34  fof(f9036,plain,(
% 7.44/1.34    spl5_42 | spl5_38),
% 7.44/1.34    inference(avatar_split_clause,[],[f8970,f8824,f9025])).
% 7.44/1.34  fof(f9025,plain,(
% 7.44/1.34    spl5_42 <=> r2_hidden(sK3(k6_subset_1(k6_subset_1(sK1,sK0),sK0),k1_xboole_0),k6_subset_1(sK1,sK0))),
% 7.44/1.34    introduced(avatar_definition,[new_symbols(naming,[spl5_42])])).
% 7.44/1.34  fof(f8824,plain,(
% 7.44/1.34    spl5_38 <=> r1_tarski(k6_subset_1(k6_subset_1(sK1,sK0),sK0),k1_xboole_0)),
% 7.44/1.34    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).
% 7.44/1.34  fof(f8970,plain,(
% 7.44/1.34    r2_hidden(sK3(k6_subset_1(k6_subset_1(sK1,sK0),sK0),k1_xboole_0),k6_subset_1(sK1,sK0)) | spl5_38),
% 7.44/1.34    inference(unit_resulting_resolution,[],[f8826,f116])).
% 7.44/1.34  fof(f8826,plain,(
% 7.44/1.34    ~r1_tarski(k6_subset_1(k6_subset_1(sK1,sK0),sK0),k1_xboole_0) | spl5_38),
% 7.44/1.34    inference(avatar_component_clause,[],[f8824])).
% 7.44/1.34  fof(f9035,plain,(
% 7.44/1.34    ~spl5_43 | spl5_38),
% 7.44/1.34    inference(avatar_split_clause,[],[f8971,f8824,f9032])).
% 7.44/1.34  fof(f9032,plain,(
% 7.44/1.34    spl5_43 <=> r2_hidden(sK3(k6_subset_1(k6_subset_1(sK1,sK0),sK0),k1_xboole_0),sK0)),
% 7.44/1.34    introduced(avatar_definition,[new_symbols(naming,[spl5_43])])).
% 7.44/1.34  fof(f8971,plain,(
% 7.44/1.34    ~r2_hidden(sK3(k6_subset_1(k6_subset_1(sK1,sK0),sK0),k1_xboole_0),sK0) | spl5_38),
% 7.44/1.34    inference(unit_resulting_resolution,[],[f8826,f107])).
% 7.44/1.34  fof(f9029,plain,(
% 7.44/1.34    spl5_40 | spl5_38),
% 7.44/1.34    inference(avatar_split_clause,[],[f8976,f8824,f9015])).
% 7.44/1.34  fof(f9015,plain,(
% 7.44/1.34    spl5_40 <=> r2_hidden(sK3(k6_subset_1(k6_subset_1(sK1,sK0),sK0),k1_xboole_0),k6_subset_1(k6_subset_1(sK1,sK0),sK0))),
% 7.44/1.34    introduced(avatar_definition,[new_symbols(naming,[spl5_40])])).
% 7.44/1.34  fof(f8976,plain,(
% 7.44/1.34    r2_hidden(sK3(k6_subset_1(k6_subset_1(sK1,sK0),sK0),k1_xboole_0),k6_subset_1(k6_subset_1(sK1,sK0),sK0)) | spl5_38),
% 7.44/1.34    inference(unit_resulting_resolution,[],[f8826,f42])).
% 7.44/1.34  fof(f9028,plain,(
% 7.44/1.34    spl5_42 | spl5_38),
% 7.44/1.34    inference(avatar_split_clause,[],[f8979,f8824,f9025])).
% 7.44/1.34  fof(f8979,plain,(
% 7.44/1.34    r2_hidden(sK3(k6_subset_1(k6_subset_1(sK1,sK0),sK0),k1_xboole_0),k6_subset_1(sK1,sK0)) | spl5_38),
% 7.44/1.34    inference(unit_resulting_resolution,[],[f154,f8826,f137])).
% 7.44/1.34  fof(f9023,plain,(
% 7.44/1.34    spl5_41 | spl5_38),
% 7.44/1.34    inference(avatar_split_clause,[],[f8980,f8824,f9020])).
% 7.44/1.34  fof(f9020,plain,(
% 7.44/1.34    spl5_41 <=> r2_hidden(sK3(k6_subset_1(k6_subset_1(sK1,sK0),sK0),k1_xboole_0),sK1)),
% 7.44/1.34    introduced(avatar_definition,[new_symbols(naming,[spl5_41])])).
% 7.44/1.34  fof(f8980,plain,(
% 7.44/1.34    r2_hidden(sK3(k6_subset_1(k6_subset_1(sK1,sK0),sK0),k1_xboole_0),sK1) | spl5_38),
% 7.44/1.34    inference(unit_resulting_resolution,[],[f329,f8826,f137])).
% 7.44/1.34  fof(f9018,plain,(
% 7.44/1.34    spl5_40 | spl5_38),
% 7.44/1.34    inference(avatar_split_clause,[],[f8983,f8824,f9015])).
% 7.44/1.34  fof(f8983,plain,(
% 7.44/1.34    r2_hidden(sK3(k6_subset_1(k6_subset_1(sK1,sK0),sK0),k1_xboole_0),k6_subset_1(k6_subset_1(sK1,sK0),sK0)) | spl5_38),
% 7.44/1.34    inference(unit_resulting_resolution,[],[f77,f8826,f137])).
% 7.44/1.34  fof(f8833,plain,(
% 7.44/1.34    ~spl5_39 | spl5_26 | ~spl5_27),
% 7.44/1.34    inference(avatar_split_clause,[],[f7789,f5298,f5167,f8830])).
% 7.44/1.34  fof(f5298,plain,(
% 7.44/1.34    spl5_27 <=> r2_hidden(sK3(sK1,sK0),k6_subset_1(sK1,sK0))),
% 7.44/1.34    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).
% 7.44/1.34  fof(f7789,plain,(
% 7.44/1.34    ~r1_tarski(k6_subset_1(k6_subset_1(sK1,sK0),sK0),sK0) | (spl5_26 | ~spl5_27)),
% 7.44/1.34    inference(unit_resulting_resolution,[],[f5169,f5169,f5300,f1318])).
% 7.44/1.34  fof(f5300,plain,(
% 7.44/1.34    r2_hidden(sK3(sK1,sK0),k6_subset_1(sK1,sK0)) | ~spl5_27),
% 7.44/1.34    inference(avatar_component_clause,[],[f5298])).
% 7.44/1.34  fof(f8827,plain,(
% 7.44/1.34    ~spl5_38 | spl5_26 | ~spl5_27),
% 7.44/1.34    inference(avatar_split_clause,[],[f7793,f5298,f5167,f8824])).
% 7.44/1.34  fof(f7793,plain,(
% 7.44/1.34    ~r1_tarski(k6_subset_1(k6_subset_1(sK1,sK0),sK0),k1_xboole_0) | (spl5_26 | ~spl5_27)),
% 7.44/1.34    inference(unit_resulting_resolution,[],[f5169,f246,f5300,f1318])).
% 7.44/1.34  fof(f6107,plain,(
% 7.44/1.34    spl5_36 | spl5_30),
% 7.44/1.34    inference(avatar_split_clause,[],[f6055,f5990,f6095])).
% 7.44/1.34  fof(f6095,plain,(
% 7.44/1.34    spl5_36 <=> r2_hidden(sK3(k6_subset_1(sK1,sK0),sK0),sK1)),
% 7.44/1.34    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).
% 7.44/1.34  fof(f5990,plain,(
% 7.44/1.34    spl5_30 <=> r1_tarski(k6_subset_1(sK1,sK0),sK0)),
% 7.44/1.34    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).
% 7.44/1.34  fof(f6055,plain,(
% 7.44/1.34    r2_hidden(sK3(k6_subset_1(sK1,sK0),sK0),sK1) | spl5_30),
% 7.44/1.34    inference(unit_resulting_resolution,[],[f5992,f116])).
% 7.44/1.34  fof(f5992,plain,(
% 7.44/1.34    ~r1_tarski(k6_subset_1(sK1,sK0),sK0) | spl5_30),
% 7.44/1.34    inference(avatar_component_clause,[],[f5990])).
% 7.44/1.34  fof(f6106,plain,(
% 7.44/1.34    ~spl5_37 | spl5_30),
% 7.44/1.34    inference(avatar_split_clause,[],[f6056,f5990,f6100])).
% 7.44/1.34  fof(f6100,plain,(
% 7.44/1.34    spl5_37 <=> r2_hidden(sK3(k6_subset_1(sK1,sK0),sK0),sK0)),
% 7.44/1.34    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).
% 7.44/1.34  fof(f6056,plain,(
% 7.44/1.34    ~r2_hidden(sK3(k6_subset_1(sK1,sK0),sK0),sK0) | spl5_30),
% 7.44/1.34    inference(unit_resulting_resolution,[],[f5992,f107])).
% 7.44/1.34  fof(f6104,plain,(
% 7.44/1.34    spl5_35 | spl5_30),
% 7.44/1.34    inference(avatar_split_clause,[],[f6061,f5990,f6090])).
% 7.44/1.34  fof(f6090,plain,(
% 7.44/1.34    spl5_35 <=> r2_hidden(sK3(k6_subset_1(sK1,sK0),sK0),k6_subset_1(sK1,sK0))),
% 7.44/1.34    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).
% 7.44/1.34  fof(f6061,plain,(
% 7.44/1.34    r2_hidden(sK3(k6_subset_1(sK1,sK0),sK0),k6_subset_1(sK1,sK0)) | spl5_30),
% 7.44/1.34    inference(unit_resulting_resolution,[],[f5992,f42])).
% 7.44/1.34  fof(f6103,plain,(
% 7.44/1.34    ~spl5_37 | spl5_30),
% 7.44/1.34    inference(avatar_split_clause,[],[f6062,f5990,f6100])).
% 7.44/1.34  fof(f6062,plain,(
% 7.44/1.34    ~r2_hidden(sK3(k6_subset_1(sK1,sK0),sK0),sK0) | spl5_30),
% 7.44/1.34    inference(unit_resulting_resolution,[],[f5992,f43])).
% 7.44/1.34  fof(f6098,plain,(
% 7.44/1.34    spl5_36 | spl5_30),
% 7.44/1.34    inference(avatar_split_clause,[],[f6064,f5990,f6095])).
% 7.44/1.34  fof(f6064,plain,(
% 7.44/1.34    r2_hidden(sK3(k6_subset_1(sK1,sK0),sK0),sK1) | spl5_30),
% 7.44/1.34    inference(unit_resulting_resolution,[],[f154,f5992,f137])).
% 7.44/1.34  fof(f6093,plain,(
% 7.44/1.34    spl5_35 | spl5_30),
% 7.44/1.34    inference(avatar_split_clause,[],[f6067,f5990,f6090])).
% 7.44/1.34  fof(f6067,plain,(
% 7.44/1.34    r2_hidden(sK3(k6_subset_1(sK1,sK0),sK0),k6_subset_1(sK1,sK0)) | spl5_30),
% 7.44/1.34    inference(unit_resulting_resolution,[],[f77,f5992,f137])).
% 7.44/1.34  fof(f6054,plain,(
% 7.44/1.34    spl5_33 | spl5_29),
% 7.44/1.34    inference(avatar_split_clause,[],[f6001,f5985,f6043])).
% 7.44/1.34  fof(f6043,plain,(
% 7.44/1.34    spl5_33 <=> r2_hidden(sK3(k6_subset_1(sK1,sK0),k1_xboole_0),sK1)),
% 7.44/1.34    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).
% 7.44/1.34  fof(f5985,plain,(
% 7.44/1.34    spl5_29 <=> r1_tarski(k6_subset_1(sK1,sK0),k1_xboole_0)),
% 7.44/1.34    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).
% 7.44/1.34  fof(f6001,plain,(
% 7.44/1.34    r2_hidden(sK3(k6_subset_1(sK1,sK0),k1_xboole_0),sK1) | spl5_29),
% 7.44/1.34    inference(unit_resulting_resolution,[],[f5987,f116])).
% 7.44/1.34  fof(f5987,plain,(
% 7.44/1.34    ~r1_tarski(k6_subset_1(sK1,sK0),k1_xboole_0) | spl5_29),
% 7.44/1.34    inference(avatar_component_clause,[],[f5985])).
% 7.44/1.34  fof(f6053,plain,(
% 7.44/1.34    ~spl5_34 | spl5_29),
% 7.44/1.34    inference(avatar_split_clause,[],[f6002,f5985,f6050])).
% 7.44/1.34  fof(f6050,plain,(
% 7.44/1.34    spl5_34 <=> r2_hidden(sK3(k6_subset_1(sK1,sK0),k1_xboole_0),sK0)),
% 7.44/1.34    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).
% 7.44/1.34  fof(f6002,plain,(
% 7.44/1.34    ~r2_hidden(sK3(k6_subset_1(sK1,sK0),k1_xboole_0),sK0) | spl5_29),
% 7.44/1.34    inference(unit_resulting_resolution,[],[f5987,f107])).
% 7.44/1.34  fof(f6047,plain,(
% 7.44/1.34    spl5_32 | spl5_29),
% 7.44/1.34    inference(avatar_split_clause,[],[f6007,f5985,f6038])).
% 7.44/1.34  fof(f6038,plain,(
% 7.44/1.34    spl5_32 <=> r2_hidden(sK3(k6_subset_1(sK1,sK0),k1_xboole_0),k6_subset_1(sK1,sK0))),
% 7.44/1.34    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).
% 7.44/1.34  fof(f6007,plain,(
% 7.44/1.34    r2_hidden(sK3(k6_subset_1(sK1,sK0),k1_xboole_0),k6_subset_1(sK1,sK0)) | spl5_29),
% 7.44/1.34    inference(unit_resulting_resolution,[],[f5987,f42])).
% 7.44/1.34  fof(f6046,plain,(
% 7.44/1.34    spl5_33 | spl5_29),
% 7.44/1.34    inference(avatar_split_clause,[],[f6010,f5985,f6043])).
% 7.44/1.34  fof(f6010,plain,(
% 7.44/1.34    r2_hidden(sK3(k6_subset_1(sK1,sK0),k1_xboole_0),sK1) | spl5_29),
% 7.44/1.34    inference(unit_resulting_resolution,[],[f154,f5987,f137])).
% 7.44/1.34  fof(f6041,plain,(
% 7.44/1.34    spl5_32 | spl5_29),
% 7.44/1.34    inference(avatar_split_clause,[],[f6013,f5985,f6038])).
% 7.44/1.34  fof(f6013,plain,(
% 7.44/1.34    r2_hidden(sK3(k6_subset_1(sK1,sK0),k1_xboole_0),k6_subset_1(sK1,sK0)) | spl5_29),
% 7.44/1.34    inference(unit_resulting_resolution,[],[f77,f5987,f137])).
% 7.44/1.34  fof(f5999,plain,(
% 7.44/1.34    spl5_31 | spl5_26 | ~spl5_27),
% 7.44/1.34    inference(avatar_split_clause,[],[f5954,f5298,f5167,f5996])).
% 7.44/1.34  fof(f5996,plain,(
% 7.44/1.34    spl5_31 <=> r2_hidden(sK3(sK1,sK0),k6_subset_1(k6_subset_1(sK1,sK0),sK0))),
% 7.44/1.34    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).
% 7.44/1.34  fof(f5954,plain,(
% 7.44/1.34    r2_hidden(sK3(sK1,sK0),k6_subset_1(k6_subset_1(sK1,sK0),sK0)) | (spl5_26 | ~spl5_27)),
% 7.44/1.34    inference(unit_resulting_resolution,[],[f5169,f5300,f79])).
% 7.44/1.34  fof(f5993,plain,(
% 7.44/1.34    ~spl5_30 | spl5_26 | ~spl5_27),
% 7.44/1.34    inference(avatar_split_clause,[],[f5975,f5298,f5167,f5990])).
% 7.44/1.34  fof(f5975,plain,(
% 7.44/1.34    ~r1_tarski(k6_subset_1(sK1,sK0),sK0) | (spl5_26 | ~spl5_27)),
% 7.44/1.34    inference(unit_resulting_resolution,[],[f5169,f5300,f41])).
% 7.44/1.34  fof(f5988,plain,(
% 7.44/1.34    ~spl5_29 | ~spl5_27),
% 7.44/1.34    inference(avatar_split_clause,[],[f5976,f5298,f5985])).
% 7.44/1.34  fof(f5976,plain,(
% 7.44/1.34    ~r1_tarski(k6_subset_1(sK1,sK0),k1_xboole_0) | ~spl5_27),
% 7.44/1.34    inference(unit_resulting_resolution,[],[f246,f5300,f41])).
% 7.44/1.34  fof(f5662,plain,(
% 7.44/1.34    ~spl5_28 | spl5_1),
% 7.44/1.34    inference(avatar_split_clause,[],[f5644,f83,f5659])).
% 7.44/1.34  fof(f5659,plain,(
% 7.44/1.34    spl5_28 <=> r2_hidden(sK3(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1))),k10_relat_1(sK2,sK1))),
% 7.44/1.34    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).
% 7.44/1.34  fof(f83,plain,(
% 7.44/1.34    spl5_1 <=> r1_tarski(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1)))),
% 7.44/1.34    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 7.44/1.34  fof(f5644,plain,(
% 7.44/1.34    ~r2_hidden(sK3(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1))),k10_relat_1(sK2,sK1)) | spl5_1),
% 7.44/1.34    inference(unit_resulting_resolution,[],[f85,f107])).
% 7.44/1.34  fof(f85,plain,(
% 7.44/1.34    ~r1_tarski(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1))) | spl5_1),
% 7.44/1.34    inference(avatar_component_clause,[],[f83])).
% 7.44/1.34  fof(f5301,plain,(
% 7.44/1.34    spl5_27 | ~spl5_25 | spl5_26),
% 7.44/1.34    inference(avatar_split_clause,[],[f5287,f5167,f5162,f5298])).
% 7.44/1.34  fof(f5162,plain,(
% 7.44/1.34    spl5_25 <=> r2_hidden(sK3(sK1,sK0),sK1)),
% 7.44/1.34    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).
% 7.44/1.34  fof(f5287,plain,(
% 7.44/1.34    r2_hidden(sK3(sK1,sK0),k6_subset_1(sK1,sK0)) | (~spl5_25 | spl5_26)),
% 7.44/1.34    inference(unit_resulting_resolution,[],[f5164,f5169,f79])).
% 7.44/1.34  fof(f5164,plain,(
% 7.44/1.34    r2_hidden(sK3(sK1,sK0),sK1) | ~spl5_25),
% 7.44/1.34    inference(avatar_component_clause,[],[f5162])).
% 7.44/1.34  fof(f5171,plain,(
% 7.44/1.34    spl5_25 | spl5_24),
% 7.44/1.34    inference(avatar_split_clause,[],[f5141,f5137,f5162])).
% 7.44/1.34  fof(f5141,plain,(
% 7.44/1.34    r2_hidden(sK3(sK1,sK0),sK1) | spl5_24),
% 7.44/1.34    inference(unit_resulting_resolution,[],[f5139,f42])).
% 7.44/1.34  fof(f5170,plain,(
% 7.44/1.34    ~spl5_26 | spl5_24),
% 7.44/1.34    inference(avatar_split_clause,[],[f5142,f5137,f5167])).
% 7.44/1.34  fof(f5142,plain,(
% 7.44/1.34    ~r2_hidden(sK3(sK1,sK0),sK0) | spl5_24),
% 7.44/1.34    inference(unit_resulting_resolution,[],[f5139,f43])).
% 7.44/1.34  fof(f5165,plain,(
% 7.44/1.34    spl5_25 | spl5_24),
% 7.44/1.34    inference(avatar_split_clause,[],[f5144,f5137,f5162])).
% 7.44/1.34  fof(f5144,plain,(
% 7.44/1.34    r2_hidden(sK3(sK1,sK0),sK1) | spl5_24),
% 7.44/1.34    inference(unit_resulting_resolution,[],[f77,f5139,f137])).
% 7.44/1.34  fof(f5140,plain,(
% 7.44/1.34    ~spl5_24 | spl5_18),
% 7.44/1.34    inference(avatar_split_clause,[],[f5135,f3766,f5137])).
% 7.44/1.34  fof(f5135,plain,(
% 7.44/1.34    ~r1_tarski(sK1,sK0) | spl5_18),
% 7.44/1.34    inference(subsumption_resolution,[],[f5113,f77])).
% 7.44/1.34  fof(f5113,plain,(
% 7.44/1.34    ~r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK0)) | ~r1_tarski(sK1,sK0) | spl5_18),
% 7.44/1.34    inference(superposition,[],[f3768,f3898])).
% 7.44/1.34  fof(f3898,plain,(
% 7.44/1.34    ( ! [X8,X7] : (k2_xboole_0(X8,X7) = X8 | ~r1_tarski(X7,X8)) )),
% 7.44/1.34    inference(subsumption_resolution,[],[f3869,f97])).
% 7.44/1.34  fof(f3869,plain,(
% 7.44/1.34    ( ! [X8,X7] : (~r1_tarski(X7,X8) | ~r1_tarski(X8,k2_xboole_0(X8,X7)) | k2_xboole_0(X8,X7) = X8) )),
% 7.44/1.34    inference(resolution,[],[f3777,f40])).
% 7.44/1.34  fof(f3777,plain,(
% 7.44/1.34    ( ! [X2,X1] : (r1_tarski(k2_xboole_0(X2,X1),X2) | ~r1_tarski(X1,X2)) )),
% 7.44/1.34    inference(forward_demodulation,[],[f3606,f788])).
% 7.44/1.34  fof(f788,plain,(
% 7.44/1.34    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 7.44/1.34    inference(unit_resulting_resolution,[],[f97,f515,f40])).
% 7.44/1.34  fof(f515,plain,(
% 7.44/1.34    ( ! [X0] : (r1_tarski(k2_xboole_0(X0,k1_xboole_0),X0)) )),
% 7.44/1.34    inference(unit_resulting_resolution,[],[f77,f119,f50])).
% 7.44/1.34  fof(f50,plain,(
% 7.44/1.34    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 7.44/1.34    inference(cnf_transformation,[],[f30])).
% 7.44/1.34  fof(f30,plain,(
% 7.44/1.34    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 7.44/1.34    inference(flattening,[],[f29])).
% 7.44/1.34  fof(f29,plain,(
% 7.44/1.34    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 7.44/1.34    inference(ennf_transformation,[],[f10])).
% 7.44/1.34  fof(f10,axiom,(
% 7.44/1.34    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 7.44/1.34    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).
% 7.44/1.34  fof(f3606,plain,(
% 7.44/1.34    ( ! [X2,X1] : (r1_tarski(k2_xboole_0(X2,X1),k2_xboole_0(X2,k1_xboole_0)) | ~r1_tarski(X1,X2)) )),
% 7.44/1.34    inference(superposition,[],[f458,f2512])).
% 7.44/1.34  fof(f2512,plain,(
% 7.44/1.34    ( ! [X14,X13] : (k1_xboole_0 = k6_subset_1(X13,X14) | ~r1_tarski(X13,X14)) )),
% 7.44/1.34    inference(resolution,[],[f1980,f132])).
% 7.44/1.34  fof(f1980,plain,(
% 7.44/1.34    ( ! [X6,X4,X5] : (r1_tarski(k6_subset_1(X4,X5),X6) | ~r1_tarski(X4,X5)) )),
% 7.44/1.34    inference(resolution,[],[f1405,f69])).
% 7.44/1.34  fof(f1405,plain,(
% 7.44/1.34    ( ! [X2,X3,X1] : (r1_tarski(X3,k2_xboole_0(X2,X1)) | ~r1_tarski(X3,X2)) )),
% 7.44/1.34    inference(superposition,[],[f46,f935])).
% 7.44/1.34  fof(f935,plain,(
% 7.44/1.34    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 7.44/1.34    inference(unit_resulting_resolution,[],[f467,f467,f40])).
% 7.44/1.34  fof(f467,plain,(
% 7.44/1.34    ( ! [X0,X1] : (r1_tarski(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0))) )),
% 7.44/1.34    inference(unit_resulting_resolution,[],[f94,f97,f50])).
% 7.44/1.34  fof(f458,plain,(
% 7.44/1.34    ( ! [X0,X1] : (r1_tarski(k2_xboole_0(X0,X1),k2_xboole_0(X0,k6_subset_1(X1,X0)))) )),
% 7.44/1.34    inference(unit_resulting_resolution,[],[f97,f218,f50])).
% 7.44/1.34  fof(f218,plain,(
% 7.44/1.34    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,k6_subset_1(X0,X1)))) )),
% 7.44/1.34    inference(unit_resulting_resolution,[],[f77,f70])).
% 7.44/1.34  fof(f70,plain,(
% 7.44/1.34    ( ! [X2,X0,X1] : (~r1_tarski(k6_subset_1(X0,X1),X2) | r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 7.44/1.34    inference(definition_unfolding,[],[f48,f34])).
% 7.44/1.34  fof(f48,plain,(
% 7.44/1.34    ( ! [X2,X0,X1] : (~r1_tarski(k4_xboole_0(X0,X1),X2) | r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 7.44/1.34    inference(cnf_transformation,[],[f27])).
% 7.44/1.34  fof(f27,plain,(
% 7.44/1.34    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 7.44/1.34    inference(ennf_transformation,[],[f9])).
% 7.44/1.34  fof(f9,axiom,(
% 7.44/1.34    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 7.44/1.34    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).
% 7.44/1.34  fof(f5006,plain,(
% 7.44/1.34    spl5_23 | spl5_1),
% 7.44/1.34    inference(avatar_split_clause,[],[f4943,f83,f5003])).
% 7.44/1.34  fof(f5003,plain,(
% 7.44/1.34    spl5_23 <=> r2_hidden(sK3(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1))),k10_relat_1(sK2,sK0))),
% 7.44/1.34    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).
% 7.44/1.34  fof(f4943,plain,(
% 7.44/1.34    r2_hidden(sK3(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1))),k10_relat_1(sK2,sK0)) | spl5_1),
% 7.44/1.34    inference(unit_resulting_resolution,[],[f85,f154,f137])).
% 7.44/1.34  fof(f4126,plain,(
% 7.44/1.34    spl5_22 | spl5_21),
% 7.44/1.34    inference(avatar_split_clause,[],[f4121,f4112,f4123])).
% 7.44/1.34  fof(f4123,plain,(
% 7.44/1.34    spl5_22 <=> r2_hidden(sK3(sK1,k1_xboole_0),sK1)),
% 7.44/1.34    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 7.44/1.34  fof(f4112,plain,(
% 7.44/1.34    spl5_21 <=> r1_tarski(sK1,k1_xboole_0)),
% 7.44/1.34    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 7.44/1.34  fof(f4121,plain,(
% 7.44/1.34    r2_hidden(sK3(sK1,k1_xboole_0),sK1) | spl5_21),
% 7.44/1.34    inference(unit_resulting_resolution,[],[f4114,f42])).
% 7.44/1.34  fof(f4114,plain,(
% 7.44/1.34    ~r1_tarski(sK1,k1_xboole_0) | spl5_21),
% 7.44/1.34    inference(avatar_component_clause,[],[f4112])).
% 7.44/1.34  fof(f4115,plain,(
% 7.44/1.34    ~spl5_21 | spl5_18),
% 7.44/1.34    inference(avatar_split_clause,[],[f4110,f3766,f4112])).
% 7.44/1.34  fof(f4110,plain,(
% 7.44/1.34    ~r1_tarski(sK1,k1_xboole_0) | spl5_18),
% 7.44/1.34    inference(subsumption_resolution,[],[f4099,f77])).
% 7.44/1.34  fof(f4099,plain,(
% 7.44/1.34    ~r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK0)) | ~r1_tarski(sK1,k1_xboole_0) | spl5_18),
% 7.44/1.34    inference(superposition,[],[f3768,f3833])).
% 7.44/1.34  fof(f3833,plain,(
% 7.44/1.34    ( ! [X6,X7] : (k2_xboole_0(X7,X6) = X7 | ~r1_tarski(X6,k1_xboole_0)) )),
% 7.44/1.34    inference(subsumption_resolution,[],[f3808,f97])).
% 7.44/1.34  fof(f3808,plain,(
% 7.44/1.34    ( ! [X6,X7] : (~r1_tarski(X6,k1_xboole_0) | ~r1_tarski(X7,k2_xboole_0(X7,X6)) | k2_xboole_0(X7,X6) = X7) )),
% 7.44/1.34    inference(resolution,[],[f3778,f40])).
% 7.44/1.34  fof(f3778,plain,(
% 7.44/1.34    ( ! [X4,X3] : (r1_tarski(k2_xboole_0(X4,X3),X4) | ~r1_tarski(X3,k1_xboole_0)) )),
% 7.44/1.34    inference(forward_demodulation,[],[f3607,f788])).
% 7.44/1.34  fof(f3607,plain,(
% 7.44/1.34    ( ! [X4,X3] : (r1_tarski(k2_xboole_0(X4,X3),k2_xboole_0(X4,k1_xboole_0)) | ~r1_tarski(X3,k1_xboole_0)) )),
% 7.44/1.34    inference(superposition,[],[f458,f1944])).
% 7.44/1.34  fof(f1944,plain,(
% 7.44/1.34    ( ! [X10,X9] : (k1_xboole_0 = k6_subset_1(X9,X10) | ~r1_tarski(X9,k1_xboole_0)) )),
% 7.44/1.34    inference(resolution,[],[f165,f132])).
% 7.44/1.34  fof(f165,plain,(
% 7.44/1.34    ( ! [X2,X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X2) | ~r1_tarski(X0,X2)) )),
% 7.44/1.34    inference(resolution,[],[f69,f46])).
% 7.44/1.34  fof(f4109,plain,(
% 7.44/1.34    ~spl5_20 | spl5_18),
% 7.44/1.34    inference(avatar_split_clause,[],[f4097,f3766,f4106])).
% 7.44/1.34  fof(f4106,plain,(
% 7.44/1.34    spl5_20 <=> r2_hidden(sK3(k10_relat_1(sK2,sK0),k10_relat_1(sK2,k2_xboole_0(sK0,sK1))),k10_relat_1(sK2,k2_xboole_0(sK0,sK1)))),
% 7.44/1.34    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 7.44/1.34  fof(f4097,plain,(
% 7.44/1.34    ~r2_hidden(sK3(k10_relat_1(sK2,sK0),k10_relat_1(sK2,k2_xboole_0(sK0,sK1))),k10_relat_1(sK2,k2_xboole_0(sK0,sK1))) | spl5_18),
% 7.44/1.34    inference(unit_resulting_resolution,[],[f3768,f43])).
% 7.44/1.34  fof(f4104,plain,(
% 7.44/1.34    spl5_19 | spl5_18),
% 7.44/1.34    inference(avatar_split_clause,[],[f4098,f3766,f4101])).
% 7.44/1.34  fof(f4101,plain,(
% 7.44/1.34    spl5_19 <=> r2_hidden(sK3(k10_relat_1(sK2,sK0),k10_relat_1(sK2,k2_xboole_0(sK0,sK1))),k10_relat_1(sK2,sK0))),
% 7.44/1.34    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 7.44/1.34  fof(f4098,plain,(
% 7.44/1.34    r2_hidden(sK3(k10_relat_1(sK2,sK0),k10_relat_1(sK2,k2_xboole_0(sK0,sK1))),k10_relat_1(sK2,sK0)) | spl5_18),
% 7.44/1.34    inference(unit_resulting_resolution,[],[f3768,f42])).
% 7.44/1.34  fof(f3769,plain,(
% 7.44/1.34    ~spl5_18 | spl5_14),
% 7.44/1.34    inference(avatar_split_clause,[],[f3764,f2152,f3766])).
% 7.44/1.34  fof(f2152,plain,(
% 7.44/1.34    spl5_14 <=> r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,k2_xboole_0(sK1,k6_subset_1(sK0,sK1))))),
% 7.44/1.34    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 7.44/1.34  fof(f3764,plain,(
% 7.44/1.34    ~r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,k2_xboole_0(sK0,sK1))) | spl5_14),
% 7.44/1.34    inference(forward_demodulation,[],[f3756,f935])).
% 7.44/1.34  fof(f3756,plain,(
% 7.44/1.34    ~r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,k2_xboole_0(sK1,sK0))) | spl5_14),
% 7.44/1.34    inference(backward_demodulation,[],[f2154,f3642])).
% 7.44/1.34  fof(f3642,plain,(
% 7.44/1.34    ( ! [X6,X7] : (k2_xboole_0(X6,X7) = k2_xboole_0(X6,k6_subset_1(X7,X6))) )),
% 7.44/1.34    inference(subsumption_resolution,[],[f3597,f570])).
% 7.44/1.34  fof(f570,plain,(
% 7.44/1.34    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,k6_subset_1(X1,X2)),k2_xboole_0(X0,X1))) )),
% 7.44/1.34    inference(unit_resulting_resolution,[],[f97,f155,f50])).
% 7.44/1.34  fof(f3597,plain,(
% 7.44/1.34    ( ! [X6,X7] : (~r1_tarski(k2_xboole_0(X6,k6_subset_1(X7,X6)),k2_xboole_0(X6,X7)) | k2_xboole_0(X6,X7) = k2_xboole_0(X6,k6_subset_1(X7,X6))) )),
% 7.44/1.34    inference(resolution,[],[f458,f40])).
% 7.44/1.34  fof(f2154,plain,(
% 7.44/1.34    ~r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,k2_xboole_0(sK1,k6_subset_1(sK0,sK1)))) | spl5_14),
% 7.44/1.34    inference(avatar_component_clause,[],[f2152])).
% 7.44/1.34  fof(f2547,plain,(
% 7.44/1.34    ~spl5_17 | spl5_15),
% 7.44/1.34    inference(avatar_split_clause,[],[f2536,f2522,f2544])).
% 7.44/1.34  fof(f2544,plain,(
% 7.44/1.34    spl5_17 <=> r2_hidden(sK3(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,sK1))),
% 7.44/1.34    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 7.44/1.34  fof(f2522,plain,(
% 7.44/1.34    spl5_15 <=> r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),
% 7.44/1.34    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 7.44/1.34  fof(f2536,plain,(
% 7.44/1.34    ~r2_hidden(sK3(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,sK1)) | spl5_15),
% 7.44/1.34    inference(unit_resulting_resolution,[],[f2524,f43])).
% 7.44/1.34  fof(f2524,plain,(
% 7.44/1.34    ~r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) | spl5_15),
% 7.44/1.34    inference(avatar_component_clause,[],[f2522])).
% 7.44/1.34  fof(f2542,plain,(
% 7.44/1.34    spl5_16 | spl5_15),
% 7.44/1.34    inference(avatar_split_clause,[],[f2537,f2522,f2539])).
% 7.44/1.34  fof(f2539,plain,(
% 7.44/1.34    spl5_16 <=> r2_hidden(sK3(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,sK0))),
% 7.44/1.34    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 7.44/1.34  fof(f2537,plain,(
% 7.44/1.34    r2_hidden(sK3(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,sK0)) | spl5_15),
% 7.44/1.34    inference(unit_resulting_resolution,[],[f2524,f42])).
% 7.44/1.34  fof(f2531,plain,(
% 7.44/1.34    ~spl5_15 | spl5_1),
% 7.44/1.34    inference(avatar_split_clause,[],[f2508,f83,f2522])).
% 7.44/1.34  fof(f2508,plain,(
% 7.44/1.34    ~r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) | spl5_1),
% 7.44/1.34    inference(resolution,[],[f1980,f85])).
% 7.44/1.34  fof(f2525,plain,(
% 7.44/1.34    ~spl5_15 | spl5_1),
% 7.44/1.34    inference(avatar_split_clause,[],[f2506,f83,f2522])).
% 7.44/1.34  fof(f2506,plain,(
% 7.44/1.34    ~r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) | spl5_1),
% 7.44/1.34    inference(unit_resulting_resolution,[],[f85,f1980])).
% 7.44/1.34  fof(f2155,plain,(
% 7.44/1.34    ~spl5_14 | ~spl5_2 | spl5_7),
% 7.44/1.34    inference(avatar_split_clause,[],[f2150,f1895,f88,f2152])).
% 7.44/1.34  fof(f1895,plain,(
% 7.44/1.34    spl5_7 <=> r1_tarski(k10_relat_1(sK2,sK0),k2_xboole_0(k10_relat_1(sK2,sK1),k10_relat_1(sK2,k6_subset_1(sK0,sK1))))),
% 7.44/1.34    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 7.44/1.34  fof(f2150,plain,(
% 7.44/1.34    ~r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,k2_xboole_0(sK1,k6_subset_1(sK0,sK1)))) | (~spl5_2 | spl5_7)),
% 7.44/1.34    inference(backward_demodulation,[],[f1897,f2119])).
% 7.44/1.34  fof(f2119,plain,(
% 7.44/1.34    ( ! [X0,X1] : (k10_relat_1(sK2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1))) ) | ~spl5_2),
% 7.44/1.34    inference(unit_resulting_resolution,[],[f90,f45])).
% 7.44/1.34  fof(f1897,plain,(
% 7.44/1.34    ~r1_tarski(k10_relat_1(sK2,sK0),k2_xboole_0(k10_relat_1(sK2,sK1),k10_relat_1(sK2,k6_subset_1(sK0,sK1)))) | spl5_7),
% 7.44/1.34    inference(avatar_component_clause,[],[f1895])).
% 7.44/1.34  fof(f2117,plain,(
% 7.44/1.34    spl5_13 | spl5_9),
% 7.44/1.34    inference(avatar_split_clause,[],[f2112,f2082,f2114])).
% 7.44/1.34  fof(f2114,plain,(
% 7.44/1.34    spl5_13 <=> r2_hidden(sK3(k10_relat_1(sK2,sK0),k1_xboole_0),k10_relat_1(sK2,sK0))),
% 7.44/1.34    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 7.44/1.34  fof(f2082,plain,(
% 7.44/1.34    spl5_9 <=> r1_tarski(k10_relat_1(sK2,sK0),k1_xboole_0)),
% 7.44/1.34    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 7.44/1.34  fof(f2112,plain,(
% 7.44/1.34    r2_hidden(sK3(k10_relat_1(sK2,sK0),k1_xboole_0),k10_relat_1(sK2,sK0)) | spl5_9),
% 7.44/1.34    inference(unit_resulting_resolution,[],[f2084,f42])).
% 7.44/1.34  fof(f2084,plain,(
% 7.44/1.34    ~r1_tarski(k10_relat_1(sK2,sK0),k1_xboole_0) | spl5_9),
% 7.44/1.34    inference(avatar_component_clause,[],[f2082])).
% 7.44/1.34  fof(f2105,plain,(
% 7.44/1.34    spl5_12 | spl5_10),
% 7.44/1.34    inference(avatar_split_clause,[],[f2100,f2087,f2102])).
% 7.44/1.34  fof(f2102,plain,(
% 7.44/1.34    spl5_12 <=> r2_hidden(sK3(sK0,k1_xboole_0),sK0)),
% 7.44/1.34    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 7.44/1.34  fof(f2087,plain,(
% 7.44/1.34    spl5_10 <=> r1_tarski(sK0,k1_xboole_0)),
% 7.44/1.34    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 7.44/1.34  fof(f2100,plain,(
% 7.44/1.34    r2_hidden(sK3(sK0,k1_xboole_0),sK0) | spl5_10),
% 7.44/1.34    inference(unit_resulting_resolution,[],[f2089,f42])).
% 7.44/1.34  fof(f2089,plain,(
% 7.44/1.34    ~r1_tarski(sK0,k1_xboole_0) | spl5_10),
% 7.44/1.34    inference(avatar_component_clause,[],[f2087])).
% 7.44/1.34  fof(f2094,plain,(
% 7.44/1.34    ~spl5_10 | ~spl5_11 | spl5_1),
% 7.44/1.34    inference(avatar_split_clause,[],[f2071,f83,f2091,f2087])).
% 7.44/1.34  fof(f2091,plain,(
% 7.44/1.34    spl5_11 <=> r1_tarski(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k1_xboole_0))),
% 7.44/1.34    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 7.44/1.34  fof(f2071,plain,(
% 7.44/1.34    ~r1_tarski(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k1_xboole_0)) | ~r1_tarski(sK0,k1_xboole_0) | spl5_1),
% 7.44/1.34    inference(superposition,[],[f85,f1944])).
% 7.44/1.34  fof(f2085,plain,(
% 7.44/1.34    ~spl5_9 | spl5_1),
% 7.44/1.34    inference(avatar_split_clause,[],[f2080,f83,f2082])).
% 7.44/1.34  fof(f2080,plain,(
% 7.44/1.34    ~r1_tarski(k10_relat_1(sK2,sK0),k1_xboole_0) | spl5_1),
% 7.44/1.34    inference(subsumption_resolution,[],[f2070,f119])).
% 7.44/1.34  fof(f2070,plain,(
% 7.44/1.34    ~r1_tarski(k1_xboole_0,k10_relat_1(sK2,k6_subset_1(sK0,sK1))) | ~r1_tarski(k10_relat_1(sK2,sK0),k1_xboole_0) | spl5_1),
% 7.44/1.34    inference(superposition,[],[f85,f1944])).
% 7.44/1.34  fof(f1958,plain,(
% 7.44/1.34    ~spl5_8 | spl5_1),
% 7.44/1.34    inference(avatar_split_clause,[],[f1941,f83,f1953])).
% 7.44/1.34  fof(f1953,plain,(
% 7.44/1.34    spl5_8 <=> r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,k6_subset_1(sK0,sK1)))),
% 7.44/1.34    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 7.44/1.34  fof(f1941,plain,(
% 7.44/1.34    ~r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,k6_subset_1(sK0,sK1))) | spl5_1),
% 7.44/1.34    inference(resolution,[],[f165,f85])).
% 7.44/1.34  fof(f1956,plain,(
% 7.44/1.34    ~spl5_8 | spl5_1),
% 7.44/1.34    inference(avatar_split_clause,[],[f1939,f83,f1953])).
% 7.44/1.34  fof(f1939,plain,(
% 7.44/1.34    ~r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,k6_subset_1(sK0,sK1))) | spl5_1),
% 7.44/1.34    inference(unit_resulting_resolution,[],[f85,f165])).
% 7.44/1.34  fof(f1898,plain,(
% 7.44/1.34    ~spl5_7 | spl5_1),
% 7.44/1.34    inference(avatar_split_clause,[],[f1874,f83,f1895])).
% 7.44/1.34  fof(f1874,plain,(
% 7.44/1.34    ~r1_tarski(k10_relat_1(sK2,sK0),k2_xboole_0(k10_relat_1(sK2,sK1),k10_relat_1(sK2,k6_subset_1(sK0,sK1)))) | spl5_1),
% 7.44/1.34    inference(unit_resulting_resolution,[],[f85,f69])).
% 7.44/1.34  fof(f1893,plain,(
% 7.44/1.34    ~spl5_6 | spl5_1),
% 7.44/1.34    inference(avatar_split_clause,[],[f1875,f83,f1890])).
% 7.44/1.34  fof(f1890,plain,(
% 7.44/1.34    spl5_6 <=> r1_tarski(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k1_xboole_0)),
% 7.44/1.34    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 7.44/1.34  fof(f1875,plain,(
% 7.44/1.34    ~r1_tarski(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k1_xboole_0) | spl5_1),
% 7.44/1.34    inference(unit_resulting_resolution,[],[f85,f860])).
% 7.44/1.34  fof(f860,plain,(
% 7.44/1.34    ( ! [X0,X1] : (~r1_tarski(X1,k1_xboole_0) | r1_tarski(X1,X0)) )),
% 7.44/1.34    inference(superposition,[],[f46,f788])).
% 7.44/1.34  fof(f1888,plain,(
% 7.44/1.34    ~spl5_5 | spl5_1),
% 7.44/1.34    inference(avatar_split_clause,[],[f1877,f83,f1885])).
% 7.44/1.34  fof(f1885,plain,(
% 7.44/1.34    spl5_5 <=> r2_hidden(sK3(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1))),k10_relat_1(sK2,k6_subset_1(sK0,sK1)))),
% 7.44/1.34    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 7.44/1.34  fof(f1877,plain,(
% 7.44/1.34    ~r2_hidden(sK3(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1))),k10_relat_1(sK2,k6_subset_1(sK0,sK1))) | spl5_1),
% 7.44/1.34    inference(unit_resulting_resolution,[],[f85,f43])).
% 7.44/1.34  fof(f1883,plain,(
% 7.44/1.34    spl5_4 | spl5_1),
% 7.44/1.34    inference(avatar_split_clause,[],[f1878,f83,f1880])).
% 7.44/1.34  fof(f1880,plain,(
% 7.44/1.34    spl5_4 <=> r2_hidden(sK3(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1))),k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))),
% 7.44/1.34    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 7.44/1.34  fof(f1878,plain,(
% 7.44/1.34    r2_hidden(sK3(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1))),k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))) | spl5_1),
% 7.44/1.34    inference(unit_resulting_resolution,[],[f85,f42])).
% 7.44/1.34  fof(f289,plain,(
% 7.44/1.34    spl5_3),
% 7.44/1.34    inference(avatar_split_clause,[],[f274,f284])).
% 7.44/1.34  fof(f284,plain,(
% 7.44/1.34    spl5_3 <=> k1_xboole_0 = k2_xboole_0(k1_xboole_0,k1_xboole_0)),
% 7.44/1.34    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 7.44/1.34  fof(f274,plain,(
% 7.44/1.34    k1_xboole_0 = k2_xboole_0(k1_xboole_0,k1_xboole_0)),
% 7.44/1.34    inference(unit_resulting_resolution,[],[f97,f266,f40])).
% 7.44/1.34  fof(f266,plain,(
% 7.44/1.34    ( ! [X0] : (r1_tarski(k2_xboole_0(k1_xboole_0,X0),X0)) )),
% 7.44/1.34    inference(superposition,[],[f163,f67])).
% 7.44/1.34  fof(f288,plain,(
% 7.44/1.34    spl5_3),
% 7.44/1.34    inference(avatar_split_clause,[],[f275,f284])).
% 7.44/1.34  fof(f275,plain,(
% 7.44/1.34    k1_xboole_0 = k2_xboole_0(k1_xboole_0,k1_xboole_0)),
% 7.44/1.34    inference(unit_resulting_resolution,[],[f119,f266,f40])).
% 7.44/1.34  fof(f287,plain,(
% 7.44/1.34    spl5_3),
% 7.44/1.34    inference(avatar_split_clause,[],[f277,f284])).
% 7.44/1.34  fof(f277,plain,(
% 7.44/1.34    k1_xboole_0 = k2_xboole_0(k1_xboole_0,k1_xboole_0)),
% 7.44/1.34    inference(unit_resulting_resolution,[],[f266,f132])).
% 7.44/1.34  fof(f91,plain,(
% 7.44/1.34    spl5_2),
% 7.44/1.34    inference(avatar_split_clause,[],[f31,f88])).
% 7.44/1.34  fof(f31,plain,(
% 7.44/1.34    v1_relat_1(sK2)),
% 7.44/1.34    inference(cnf_transformation,[],[f22])).
% 7.44/1.34  fof(f22,plain,(
% 7.44/1.34    ? [X0,X1,X2] : (~r1_tarski(k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)),k10_relat_1(X2,k6_subset_1(X0,X1))) & v1_relat_1(X2))),
% 7.44/1.34    inference(ennf_transformation,[],[f21])).
% 7.44/1.34  fof(f21,negated_conjecture,(
% 7.44/1.34    ~! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)),k10_relat_1(X2,k6_subset_1(X0,X1))))),
% 7.44/1.34    inference(negated_conjecture,[],[f20])).
% 7.44/1.34  fof(f20,conjecture,(
% 7.44/1.34    ! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)),k10_relat_1(X2,k6_subset_1(X0,X1))))),
% 7.44/1.34    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t177_relat_1)).
% 7.44/1.34  fof(f86,plain,(
% 7.44/1.34    ~spl5_1),
% 7.44/1.34    inference(avatar_split_clause,[],[f32,f83])).
% 7.44/1.34  fof(f32,plain,(
% 7.44/1.34    ~r1_tarski(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1)))),
% 7.44/1.34    inference(cnf_transformation,[],[f22])).
% 7.44/1.34  % SZS output end Proof for theBenchmark
% 7.44/1.34  % (4498)------------------------------
% 7.44/1.34  % (4498)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.44/1.34  % (4498)Termination reason: Refutation
% 7.44/1.34  
% 7.44/1.34  % (4498)Memory used [KB]: 7164
% 7.44/1.34  % (4498)Time elapsed: 0.793 s
% 7.44/1.34  % (4498)------------------------------
% 7.44/1.34  % (4498)------------------------------
% 7.44/1.35  % (4483)Success in time 0.967 s
%------------------------------------------------------------------------------
