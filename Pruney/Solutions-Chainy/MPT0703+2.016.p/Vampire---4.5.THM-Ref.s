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
% DateTime   : Thu Dec  3 12:54:20 EST 2020

% Result     : Theorem 1.47s
% Output     : Refutation 1.47s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 277 expanded)
%              Number of leaves         :   25 (  98 expanded)
%              Depth                    :   12
%              Number of atoms          :  344 ( 786 expanded)
%              Number of equality atoms :   56 ( 138 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f600,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f57,f62,f67,f72,f77,f249,f280,f305,f338,f367,f438,f482,f544,f571,f599])).

fof(f599,plain,
    ( spl3_1
    | ~ spl3_34 ),
    inference(avatar_contradiction_clause,[],[f598])).

fof(f598,plain,
    ( $false
    | spl3_1
    | ~ spl3_34 ),
    inference(subsumption_resolution,[],[f595,f56])).

fof(f56,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl3_1
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f595,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_34 ),
    inference(trivial_inequality_removal,[],[f582])).

fof(f582,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK0,sK1)
    | ~ spl3_34 ),
    inference(superposition,[],[f39,f570])).

fof(f570,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK1)
    | ~ spl3_34 ),
    inference(avatar_component_clause,[],[f568])).

fof(f568,plain,
    ( spl3_34
  <=> k1_xboole_0 = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k1_xboole_0
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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

fof(f571,plain,
    ( spl3_34
    | ~ spl3_20
    | ~ spl3_33 ),
    inference(avatar_split_clause,[],[f566,f541,f335,f568])).

fof(f335,plain,
    ( spl3_20
  <=> k4_xboole_0(sK0,sK1) = k9_relat_1(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f541,plain,
    ( spl3_33
  <=> k1_xboole_0 = k9_relat_1(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

fof(f566,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK1)
    | ~ spl3_20
    | ~ spl3_33 ),
    inference(backward_demodulation,[],[f337,f543])).

fof(f543,plain,
    ( k1_xboole_0 = k9_relat_1(sK2,k1_xboole_0)
    | ~ spl3_33 ),
    inference(avatar_component_clause,[],[f541])).

fof(f337,plain,
    ( k4_xboole_0(sK0,sK1) = k9_relat_1(sK2,k1_xboole_0)
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f335])).

fof(f544,plain,
    ( spl3_33
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_29 ),
    inference(avatar_split_clause,[],[f539,f479,f74,f69,f541])).

fof(f69,plain,
    ( spl3_4
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f74,plain,
    ( spl3_5
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f479,plain,
    ( spl3_29
  <=> k1_xboole_0 = k10_relat_1(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f539,plain,
    ( k1_xboole_0 = k9_relat_1(sK2,k1_xboole_0)
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_29 ),
    inference(subsumption_resolution,[],[f538,f76])).

fof(f76,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f74])).

fof(f538,plain,
    ( k1_xboole_0 = k9_relat_1(sK2,k1_xboole_0)
    | ~ v1_relat_1(sK2)
    | ~ spl3_4
    | ~ spl3_29 ),
    inference(subsumption_resolution,[],[f537,f71])).

fof(f71,plain,
    ( v1_funct_1(sK2)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f69])).

fof(f537,plain,
    ( k1_xboole_0 = k9_relat_1(sK2,k1_xboole_0)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_29 ),
    inference(subsumption_resolution,[],[f529,f82])).

fof(f82,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[],[f81,f51])).

fof(f51,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f81,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X2,X3)
      | r1_tarski(k1_xboole_0,X2) ) ),
    inference(superposition,[],[f46,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f46,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f529,plain,
    ( k1_xboole_0 = k9_relat_1(sK2,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_29 ),
    inference(superposition,[],[f36,f481])).

fof(f481,plain,
    ( k1_xboole_0 = k10_relat_1(sK2,k1_xboole_0)
    | ~ spl3_29 ),
    inference(avatar_component_clause,[],[f479])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

fof(f482,plain,
    ( spl3_29
    | ~ spl3_26 ),
    inference(avatar_split_clause,[],[f477,f435,f479])).

fof(f435,plain,
    ( spl3_26
  <=> k1_xboole_0 = k10_relat_1(sK2,k4_xboole_0(k1_xboole_0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f477,plain,
    ( k1_xboole_0 = k10_relat_1(sK2,k1_xboole_0)
    | ~ spl3_26 ),
    inference(subsumption_resolution,[],[f463,f82])).

fof(f463,plain,
    ( k1_xboole_0 = k10_relat_1(sK2,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,sK1)
    | ~ spl3_26 ),
    inference(superposition,[],[f437,f40])).

fof(f437,plain,
    ( k1_xboole_0 = k10_relat_1(sK2,k4_xboole_0(k1_xboole_0,sK1))
    | ~ spl3_26 ),
    inference(avatar_component_clause,[],[f435])).

fof(f438,plain,
    ( spl3_26
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f433,f246,f74,f69,f435])).

fof(f246,plain,
    ( spl3_17
  <=> r1_tarski(k10_relat_1(sK2,k1_xboole_0),k10_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f433,plain,
    ( k1_xboole_0 = k10_relat_1(sK2,k4_xboole_0(k1_xboole_0,sK1))
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_17 ),
    inference(subsumption_resolution,[],[f432,f76])).

fof(f432,plain,
    ( ~ v1_relat_1(sK2)
    | k1_xboole_0 = k10_relat_1(sK2,k4_xboole_0(k1_xboole_0,sK1))
    | ~ spl3_4
    | ~ spl3_17 ),
    inference(subsumption_resolution,[],[f429,f71])).

fof(f429,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_xboole_0 = k10_relat_1(sK2,k4_xboole_0(k1_xboole_0,sK1))
    | ~ spl3_17 ),
    inference(resolution,[],[f248,f157])).

fof(f157,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_tarski(k10_relat_1(X3,X4),k10_relat_1(X3,X5))
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3)
      | k1_xboole_0 = k10_relat_1(X3,k4_xboole_0(X4,X5)) ) ),
    inference(superposition,[],[f156,f40])).

fof(f156,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k4_xboole_0(X0,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(forward_demodulation,[],[f155,f49])).

fof(f49,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f155,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(X2,k6_subset_1(X0,X1)) = k4_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(forward_demodulation,[],[f47,f49])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_funct_1)).

fof(f248,plain,
    ( r1_tarski(k10_relat_1(sK2,k1_xboole_0),k10_relat_1(sK2,sK1))
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f246])).

fof(f367,plain,
    ( ~ spl3_2
    | spl3_19 ),
    inference(avatar_contradiction_clause,[],[f366])).

fof(f366,plain,
    ( $false
    | ~ spl3_2
    | spl3_19 ),
    inference(subsumption_resolution,[],[f362,f46])).

fof(f362,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK1),sK0)
    | ~ spl3_2
    | spl3_19 ),
    inference(resolution,[],[f333,f178])).

fof(f178,plain,
    ( ! [X18] :
        ( r1_tarski(X18,k2_relat_1(sK2))
        | ~ r1_tarski(X18,sK0) )
    | ~ spl3_2 ),
    inference(resolution,[],[f99,f61])).

fof(f61,plain,
    ( r1_tarski(sK0,k2_relat_1(sK2))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl3_2
  <=> r1_tarski(sK0,k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f99,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(X3,X4)
      | r1_tarski(X2,X4)
      | ~ r1_tarski(X2,X3) ) ),
    inference(superposition,[],[f38,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f333,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK1),k2_relat_1(sK2))
    | spl3_19 ),
    inference(avatar_component_clause,[],[f331])).

fof(f331,plain,
    ( spl3_19
  <=> r1_tarski(k4_xboole_0(sK0,sK1),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f338,plain,
    ( ~ spl3_19
    | spl3_20
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f329,f302,f74,f69,f335,f331])).

fof(f302,plain,
    ( spl3_18
  <=> k1_xboole_0 = k10_relat_1(sK2,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f329,plain,
    ( k4_xboole_0(sK0,sK1) = k9_relat_1(sK2,k1_xboole_0)
    | ~ r1_tarski(k4_xboole_0(sK0,sK1),k2_relat_1(sK2))
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_18 ),
    inference(subsumption_resolution,[],[f328,f76])).

fof(f328,plain,
    ( k4_xboole_0(sK0,sK1) = k9_relat_1(sK2,k1_xboole_0)
    | ~ r1_tarski(k4_xboole_0(sK0,sK1),k2_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl3_4
    | ~ spl3_18 ),
    inference(subsumption_resolution,[],[f316,f71])).

fof(f316,plain,
    ( k4_xboole_0(sK0,sK1) = k9_relat_1(sK2,k1_xboole_0)
    | ~ r1_tarski(k4_xboole_0(sK0,sK1),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_18 ),
    inference(superposition,[],[f36,f304])).

fof(f304,plain,
    ( k1_xboole_0 = k10_relat_1(sK2,k4_xboole_0(sK0,sK1))
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f302])).

fof(f305,plain,
    ( spl3_18
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f300,f74,f69,f64,f302])).

fof(f64,plain,
    ( spl3_3
  <=> r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f300,plain,
    ( k1_xboole_0 = k10_relat_1(sK2,k4_xboole_0(sK0,sK1))
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f299,f76])).

fof(f299,plain,
    ( ~ v1_relat_1(sK2)
    | k1_xboole_0 = k10_relat_1(sK2,k4_xboole_0(sK0,sK1))
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f294,f71])).

fof(f294,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_xboole_0 = k10_relat_1(sK2,k4_xboole_0(sK0,sK1))
    | ~ spl3_3 ),
    inference(resolution,[],[f157,f66])).

fof(f66,plain,
    ( r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f64])).

fof(f280,plain,(
    ~ spl3_16 ),
    inference(avatar_contradiction_clause,[],[f261])).

fof(f261,plain,
    ( $false
    | ~ spl3_16 ),
    inference(unit_resulting_resolution,[],[f51,f78,f244,f152])).

fof(f152,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X3)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,k3_xboole_0(X3,X2)) ) ),
    inference(resolution,[],[f37,f38])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

fof(f244,plain,
    ( ! [X0] : ~ r1_tarski(sK0,X0)
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f243])).

fof(f243,plain,
    ( spl3_16
  <=> ! [X0] : ~ r1_tarski(sK0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f78,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(resolution,[],[f38,f51])).

fof(f249,plain,
    ( spl3_16
    | spl3_17
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f240,f74,f69,f64,f246,f243])).

fof(f240,plain,
    ( ! [X0] :
        ( r1_tarski(k10_relat_1(sK2,k1_xboole_0),k10_relat_1(sK2,sK1))
        | ~ r1_tarski(sK0,X0) )
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(superposition,[],[f237,f40])).

fof(f237,plain,
    ( ! [X0] : r1_tarski(k10_relat_1(sK2,k4_xboole_0(sK0,X0)),k10_relat_1(sK2,sK1))
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f236,f76])).

fof(f236,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(sK2)
        | r1_tarski(k10_relat_1(sK2,k4_xboole_0(sK0,X0)),k10_relat_1(sK2,sK1)) )
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f230,f71])).

fof(f230,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2)
        | r1_tarski(k10_relat_1(sK2,k4_xboole_0(sK0,X0)),k10_relat_1(sK2,sK1)) )
    | ~ spl3_3 ),
    inference(resolution,[],[f162,f177])).

fof(f177,plain,
    ( ! [X17] :
        ( ~ r1_tarski(X17,k10_relat_1(sK2,sK0))
        | r1_tarski(X17,k10_relat_1(sK2,sK1)) )
    | ~ spl3_3 ),
    inference(resolution,[],[f99,f66])).

fof(f162,plain,(
    ! [X14,X12,X13] :
      ( r1_tarski(k10_relat_1(X12,k4_xboole_0(X13,X14)),k10_relat_1(X12,X13))
      | ~ v1_funct_1(X12)
      | ~ v1_relat_1(X12) ) ),
    inference(superposition,[],[f46,f156])).

fof(f77,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f31,f74])).

fof(f31,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ~ r1_tarski(sK0,sK1)
    & r1_tarski(sK0,k2_relat_1(sK2))
    & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f26])).

fof(f26,plain,
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_funct_1)).

fof(f72,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f32,f69])).

fof(f32,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f67,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f33,f64])).

fof(f33,plain,(
    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f27])).

fof(f62,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f34,f59])).

fof(f34,plain,(
    r1_tarski(sK0,k2_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f27])).

fof(f57,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f35,f54])).

fof(f35,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n004.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:47:54 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.50  % (17860)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.51  % (17876)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.51  % (17884)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.53  % (17883)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.53  % (17869)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.53  % (17865)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.53  % (17863)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.53  % (17866)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.54  % (17889)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.54  % (17875)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.32/0.54  % (17867)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.32/0.54  % (17862)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.32/0.54  % (17864)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.32/0.54  % (17868)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.32/0.54  % (17876)Refutation not found, incomplete strategy% (17876)------------------------------
% 1.32/0.54  % (17876)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.54  % (17876)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.54  
% 1.32/0.54  % (17876)Memory used [KB]: 10618
% 1.32/0.54  % (17876)Time elapsed: 0.125 s
% 1.32/0.54  % (17876)------------------------------
% 1.32/0.54  % (17876)------------------------------
% 1.32/0.54  % (17882)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.32/0.54  % (17888)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.32/0.54  % (17887)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.32/0.54  % (17881)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.32/0.54  % (17879)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.32/0.54  % (17888)Refutation not found, incomplete strategy% (17888)------------------------------
% 1.32/0.54  % (17888)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.54  % (17888)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.54  
% 1.32/0.54  % (17888)Memory used [KB]: 10746
% 1.32/0.54  % (17888)Time elapsed: 0.131 s
% 1.32/0.54  % (17888)------------------------------
% 1.32/0.54  % (17888)------------------------------
% 1.32/0.55  % (17880)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.32/0.55  % (17861)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.32/0.55  % (17861)Refutation not found, incomplete strategy% (17861)------------------------------
% 1.32/0.55  % (17861)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.55  % (17861)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.55  
% 1.32/0.55  % (17861)Memory used [KB]: 1663
% 1.32/0.55  % (17861)Time elapsed: 0.138 s
% 1.32/0.55  % (17861)------------------------------
% 1.32/0.55  % (17861)------------------------------
% 1.32/0.55  % (17886)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.32/0.55  % (17871)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.32/0.55  % (17878)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.32/0.55  % (17870)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.47/0.55  % (17885)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.47/0.55  % (17873)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.47/0.55  % (17870)Refutation not found, incomplete strategy% (17870)------------------------------
% 1.47/0.55  % (17870)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.55  % (17870)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.55  
% 1.47/0.55  % (17870)Memory used [KB]: 10746
% 1.47/0.55  % (17870)Time elapsed: 0.121 s
% 1.47/0.55  % (17870)------------------------------
% 1.47/0.55  % (17870)------------------------------
% 1.47/0.56  % (17889)Refutation not found, incomplete strategy% (17889)------------------------------
% 1.47/0.56  % (17889)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.56  % (17889)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.56  
% 1.47/0.56  % (17889)Memory used [KB]: 1663
% 1.47/0.56  % (17889)Time elapsed: 0.003 s
% 1.47/0.56  % (17889)------------------------------
% 1.47/0.56  % (17889)------------------------------
% 1.47/0.56  % (17874)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.47/0.56  % (17877)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.47/0.56  % (17872)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.47/0.56  % (17872)Refutation not found, incomplete strategy% (17872)------------------------------
% 1.47/0.56  % (17872)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.56  % (17872)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.56  
% 1.47/0.56  % (17872)Memory used [KB]: 10618
% 1.47/0.56  % (17872)Time elapsed: 0.150 s
% 1.47/0.56  % (17872)------------------------------
% 1.47/0.56  % (17872)------------------------------
% 1.47/0.57  % (17881)Refutation found. Thanks to Tanya!
% 1.47/0.57  % SZS status Theorem for theBenchmark
% 1.47/0.57  % SZS output start Proof for theBenchmark
% 1.47/0.57  fof(f600,plain,(
% 1.47/0.57    $false),
% 1.47/0.57    inference(avatar_sat_refutation,[],[f57,f62,f67,f72,f77,f249,f280,f305,f338,f367,f438,f482,f544,f571,f599])).
% 1.47/0.57  fof(f599,plain,(
% 1.47/0.57    spl3_1 | ~spl3_34),
% 1.47/0.57    inference(avatar_contradiction_clause,[],[f598])).
% 1.47/0.57  fof(f598,plain,(
% 1.47/0.57    $false | (spl3_1 | ~spl3_34)),
% 1.47/0.57    inference(subsumption_resolution,[],[f595,f56])).
% 1.47/0.57  fof(f56,plain,(
% 1.47/0.57    ~r1_tarski(sK0,sK1) | spl3_1),
% 1.47/0.57    inference(avatar_component_clause,[],[f54])).
% 1.47/0.57  fof(f54,plain,(
% 1.47/0.57    spl3_1 <=> r1_tarski(sK0,sK1)),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.47/0.57  fof(f595,plain,(
% 1.47/0.57    r1_tarski(sK0,sK1) | ~spl3_34),
% 1.47/0.57    inference(trivial_inequality_removal,[],[f582])).
% 1.47/0.57  fof(f582,plain,(
% 1.47/0.57    k1_xboole_0 != k1_xboole_0 | r1_tarski(sK0,sK1) | ~spl3_34),
% 1.47/0.57    inference(superposition,[],[f39,f570])).
% 1.47/0.57  fof(f570,plain,(
% 1.47/0.57    k1_xboole_0 = k4_xboole_0(sK0,sK1) | ~spl3_34),
% 1.47/0.57    inference(avatar_component_clause,[],[f568])).
% 1.47/0.57  fof(f568,plain,(
% 1.47/0.57    spl3_34 <=> k1_xboole_0 = k4_xboole_0(sK0,sK1)),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).
% 1.47/0.57  fof(f39,plain,(
% 1.47/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)) )),
% 1.47/0.57    inference(cnf_transformation,[],[f28])).
% 1.47/0.57  fof(f28,plain,(
% 1.47/0.57    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 1.47/0.57    inference(nnf_transformation,[],[f2])).
% 1.47/0.57  fof(f2,axiom,(
% 1.47/0.57    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.47/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.47/0.57  fof(f571,plain,(
% 1.47/0.57    spl3_34 | ~spl3_20 | ~spl3_33),
% 1.47/0.57    inference(avatar_split_clause,[],[f566,f541,f335,f568])).
% 1.47/0.57  fof(f335,plain,(
% 1.47/0.57    spl3_20 <=> k4_xboole_0(sK0,sK1) = k9_relat_1(sK2,k1_xboole_0)),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 1.47/0.57  fof(f541,plain,(
% 1.47/0.57    spl3_33 <=> k1_xboole_0 = k9_relat_1(sK2,k1_xboole_0)),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).
% 1.47/0.57  fof(f566,plain,(
% 1.47/0.57    k1_xboole_0 = k4_xboole_0(sK0,sK1) | (~spl3_20 | ~spl3_33)),
% 1.47/0.57    inference(backward_demodulation,[],[f337,f543])).
% 1.47/0.57  fof(f543,plain,(
% 1.47/0.57    k1_xboole_0 = k9_relat_1(sK2,k1_xboole_0) | ~spl3_33),
% 1.47/0.57    inference(avatar_component_clause,[],[f541])).
% 1.47/0.57  fof(f337,plain,(
% 1.47/0.57    k4_xboole_0(sK0,sK1) = k9_relat_1(sK2,k1_xboole_0) | ~spl3_20),
% 1.47/0.57    inference(avatar_component_clause,[],[f335])).
% 1.47/0.57  fof(f544,plain,(
% 1.47/0.57    spl3_33 | ~spl3_4 | ~spl3_5 | ~spl3_29),
% 1.47/0.57    inference(avatar_split_clause,[],[f539,f479,f74,f69,f541])).
% 1.47/0.57  fof(f69,plain,(
% 1.47/0.57    spl3_4 <=> v1_funct_1(sK2)),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.47/0.57  fof(f74,plain,(
% 1.47/0.57    spl3_5 <=> v1_relat_1(sK2)),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 1.47/0.57  fof(f479,plain,(
% 1.47/0.57    spl3_29 <=> k1_xboole_0 = k10_relat_1(sK2,k1_xboole_0)),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 1.47/0.57  fof(f539,plain,(
% 1.47/0.57    k1_xboole_0 = k9_relat_1(sK2,k1_xboole_0) | (~spl3_4 | ~spl3_5 | ~spl3_29)),
% 1.47/0.57    inference(subsumption_resolution,[],[f538,f76])).
% 1.47/0.57  fof(f76,plain,(
% 1.47/0.57    v1_relat_1(sK2) | ~spl3_5),
% 1.47/0.57    inference(avatar_component_clause,[],[f74])).
% 1.47/0.57  fof(f538,plain,(
% 1.47/0.57    k1_xboole_0 = k9_relat_1(sK2,k1_xboole_0) | ~v1_relat_1(sK2) | (~spl3_4 | ~spl3_29)),
% 1.47/0.57    inference(subsumption_resolution,[],[f537,f71])).
% 1.47/0.57  fof(f71,plain,(
% 1.47/0.57    v1_funct_1(sK2) | ~spl3_4),
% 1.47/0.57    inference(avatar_component_clause,[],[f69])).
% 1.47/0.57  fof(f537,plain,(
% 1.47/0.57    k1_xboole_0 = k9_relat_1(sK2,k1_xboole_0) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl3_29),
% 1.47/0.57    inference(subsumption_resolution,[],[f529,f82])).
% 1.47/0.57  fof(f82,plain,(
% 1.47/0.57    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.47/0.57    inference(resolution,[],[f81,f51])).
% 1.47/0.57  fof(f51,plain,(
% 1.47/0.57    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.47/0.57    inference(equality_resolution,[],[f42])).
% 1.47/0.57  fof(f42,plain,(
% 1.47/0.57    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.47/0.57    inference(cnf_transformation,[],[f30])).
% 1.47/0.57  fof(f30,plain,(
% 1.47/0.57    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.47/0.57    inference(flattening,[],[f29])).
% 1.47/0.57  fof(f29,plain,(
% 1.47/0.57    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.47/0.57    inference(nnf_transformation,[],[f1])).
% 1.47/0.57  fof(f1,axiom,(
% 1.47/0.57    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.47/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.47/0.57  fof(f81,plain,(
% 1.47/0.57    ( ! [X2,X3] : (~r1_tarski(X2,X3) | r1_tarski(k1_xboole_0,X2)) )),
% 1.47/0.57    inference(superposition,[],[f46,f40])).
% 1.47/0.57  fof(f40,plain,(
% 1.47/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 1.47/0.57    inference(cnf_transformation,[],[f28])).
% 1.47/0.57  fof(f46,plain,(
% 1.47/0.57    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.47/0.57    inference(cnf_transformation,[],[f6])).
% 1.47/0.57  fof(f6,axiom,(
% 1.47/0.57    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.47/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.47/0.57  fof(f529,plain,(
% 1.47/0.57    k1_xboole_0 = k9_relat_1(sK2,k1_xboole_0) | ~r1_tarski(k1_xboole_0,k2_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl3_29),
% 1.47/0.57    inference(superposition,[],[f36,f481])).
% 1.47/0.57  fof(f481,plain,(
% 1.47/0.57    k1_xboole_0 = k10_relat_1(sK2,k1_xboole_0) | ~spl3_29),
% 1.47/0.57    inference(avatar_component_clause,[],[f479])).
% 1.47/0.57  fof(f36,plain,(
% 1.47/0.57    ( ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.47/0.57    inference(cnf_transformation,[],[f18])).
% 1.47/0.57  fof(f18,plain,(
% 1.47/0.57    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.47/0.57    inference(flattening,[],[f17])).
% 1.47/0.57  fof(f17,plain,(
% 1.47/0.57    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.47/0.57    inference(ennf_transformation,[],[f12])).
% 1.47/0.57  fof(f12,axiom,(
% 1.47/0.57    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 1.47/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).
% 1.47/0.57  fof(f482,plain,(
% 1.47/0.57    spl3_29 | ~spl3_26),
% 1.47/0.57    inference(avatar_split_clause,[],[f477,f435,f479])).
% 1.47/0.57  fof(f435,plain,(
% 1.47/0.57    spl3_26 <=> k1_xboole_0 = k10_relat_1(sK2,k4_xboole_0(k1_xboole_0,sK1))),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 1.47/0.57  fof(f477,plain,(
% 1.47/0.57    k1_xboole_0 = k10_relat_1(sK2,k1_xboole_0) | ~spl3_26),
% 1.47/0.57    inference(subsumption_resolution,[],[f463,f82])).
% 1.47/0.57  fof(f463,plain,(
% 1.47/0.57    k1_xboole_0 = k10_relat_1(sK2,k1_xboole_0) | ~r1_tarski(k1_xboole_0,sK1) | ~spl3_26),
% 1.47/0.57    inference(superposition,[],[f437,f40])).
% 1.47/0.57  fof(f437,plain,(
% 1.47/0.57    k1_xboole_0 = k10_relat_1(sK2,k4_xboole_0(k1_xboole_0,sK1)) | ~spl3_26),
% 1.47/0.57    inference(avatar_component_clause,[],[f435])).
% 1.47/0.57  fof(f438,plain,(
% 1.47/0.57    spl3_26 | ~spl3_4 | ~spl3_5 | ~spl3_17),
% 1.47/0.57    inference(avatar_split_clause,[],[f433,f246,f74,f69,f435])).
% 1.47/0.57  fof(f246,plain,(
% 1.47/0.57    spl3_17 <=> r1_tarski(k10_relat_1(sK2,k1_xboole_0),k10_relat_1(sK2,sK1))),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 1.47/0.57  fof(f433,plain,(
% 1.47/0.57    k1_xboole_0 = k10_relat_1(sK2,k4_xboole_0(k1_xboole_0,sK1)) | (~spl3_4 | ~spl3_5 | ~spl3_17)),
% 1.47/0.57    inference(subsumption_resolution,[],[f432,f76])).
% 1.47/0.57  fof(f432,plain,(
% 1.47/0.57    ~v1_relat_1(sK2) | k1_xboole_0 = k10_relat_1(sK2,k4_xboole_0(k1_xboole_0,sK1)) | (~spl3_4 | ~spl3_17)),
% 1.47/0.57    inference(subsumption_resolution,[],[f429,f71])).
% 1.47/0.57  fof(f429,plain,(
% 1.47/0.57    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k1_xboole_0 = k10_relat_1(sK2,k4_xboole_0(k1_xboole_0,sK1)) | ~spl3_17),
% 1.47/0.57    inference(resolution,[],[f248,f157])).
% 1.47/0.57  fof(f157,plain,(
% 1.47/0.57    ( ! [X4,X5,X3] : (~r1_tarski(k10_relat_1(X3,X4),k10_relat_1(X3,X5)) | ~v1_funct_1(X3) | ~v1_relat_1(X3) | k1_xboole_0 = k10_relat_1(X3,k4_xboole_0(X4,X5))) )),
% 1.47/0.57    inference(superposition,[],[f156,f40])).
% 1.47/0.57  fof(f156,plain,(
% 1.47/0.57    ( ! [X2,X0,X1] : (k4_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k4_xboole_0(X0,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.47/0.57    inference(forward_demodulation,[],[f155,f49])).
% 1.47/0.57  fof(f49,plain,(
% 1.47/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 1.47/0.57    inference(cnf_transformation,[],[f9])).
% 1.47/0.57  fof(f9,axiom,(
% 1.47/0.57    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 1.47/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 1.47/0.57  fof(f155,plain,(
% 1.47/0.57    ( ! [X2,X0,X1] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k4_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.47/0.57    inference(forward_demodulation,[],[f47,f49])).
% 1.47/0.57  fof(f47,plain,(
% 1.47/0.57    ( ! [X2,X0,X1] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.47/0.57    inference(cnf_transformation,[],[f25])).
% 1.47/0.57  fof(f25,plain,(
% 1.47/0.57    ! [X0,X1,X2] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.47/0.57    inference(flattening,[],[f24])).
% 1.47/0.57  fof(f24,plain,(
% 1.47/0.57    ! [X0,X1,X2] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.47/0.57    inference(ennf_transformation,[],[f11])).
% 1.47/0.57  fof(f11,axiom,(
% 1.47/0.57    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))),
% 1.47/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_funct_1)).
% 1.47/0.57  fof(f248,plain,(
% 1.47/0.57    r1_tarski(k10_relat_1(sK2,k1_xboole_0),k10_relat_1(sK2,sK1)) | ~spl3_17),
% 1.47/0.57    inference(avatar_component_clause,[],[f246])).
% 1.47/0.57  fof(f367,plain,(
% 1.47/0.57    ~spl3_2 | spl3_19),
% 1.47/0.57    inference(avatar_contradiction_clause,[],[f366])).
% 1.47/0.57  fof(f366,plain,(
% 1.47/0.57    $false | (~spl3_2 | spl3_19)),
% 1.47/0.57    inference(subsumption_resolution,[],[f362,f46])).
% 1.47/0.57  fof(f362,plain,(
% 1.47/0.57    ~r1_tarski(k4_xboole_0(sK0,sK1),sK0) | (~spl3_2 | spl3_19)),
% 1.47/0.57    inference(resolution,[],[f333,f178])).
% 1.47/0.57  fof(f178,plain,(
% 1.47/0.57    ( ! [X18] : (r1_tarski(X18,k2_relat_1(sK2)) | ~r1_tarski(X18,sK0)) ) | ~spl3_2),
% 1.47/0.57    inference(resolution,[],[f99,f61])).
% 1.47/0.57  fof(f61,plain,(
% 1.47/0.57    r1_tarski(sK0,k2_relat_1(sK2)) | ~spl3_2),
% 1.47/0.57    inference(avatar_component_clause,[],[f59])).
% 1.47/0.57  fof(f59,plain,(
% 1.47/0.57    spl3_2 <=> r1_tarski(sK0,k2_relat_1(sK2))),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.47/0.57  fof(f99,plain,(
% 1.47/0.57    ( ! [X4,X2,X3] : (~r1_tarski(X3,X4) | r1_tarski(X2,X4) | ~r1_tarski(X2,X3)) )),
% 1.47/0.57    inference(superposition,[],[f38,f45])).
% 1.47/0.57  fof(f45,plain,(
% 1.47/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 1.47/0.57    inference(cnf_transformation,[],[f23])).
% 1.47/0.57  fof(f23,plain,(
% 1.47/0.57    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.47/0.57    inference(ennf_transformation,[],[f4])).
% 1.47/0.57  fof(f4,axiom,(
% 1.47/0.57    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.47/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.47/0.57  fof(f38,plain,(
% 1.47/0.57    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 1.47/0.57    inference(cnf_transformation,[],[f21])).
% 1.47/0.57  fof(f21,plain,(
% 1.47/0.57    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 1.47/0.57    inference(ennf_transformation,[],[f3])).
% 1.47/0.57  fof(f3,axiom,(
% 1.47/0.57    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 1.47/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).
% 1.47/0.57  fof(f333,plain,(
% 1.47/0.57    ~r1_tarski(k4_xboole_0(sK0,sK1),k2_relat_1(sK2)) | spl3_19),
% 1.47/0.57    inference(avatar_component_clause,[],[f331])).
% 1.47/0.57  fof(f331,plain,(
% 1.47/0.57    spl3_19 <=> r1_tarski(k4_xboole_0(sK0,sK1),k2_relat_1(sK2))),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 1.47/0.57  fof(f338,plain,(
% 1.47/0.57    ~spl3_19 | spl3_20 | ~spl3_4 | ~spl3_5 | ~spl3_18),
% 1.47/0.57    inference(avatar_split_clause,[],[f329,f302,f74,f69,f335,f331])).
% 1.47/0.57  fof(f302,plain,(
% 1.47/0.57    spl3_18 <=> k1_xboole_0 = k10_relat_1(sK2,k4_xboole_0(sK0,sK1))),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 1.47/0.57  fof(f329,plain,(
% 1.47/0.57    k4_xboole_0(sK0,sK1) = k9_relat_1(sK2,k1_xboole_0) | ~r1_tarski(k4_xboole_0(sK0,sK1),k2_relat_1(sK2)) | (~spl3_4 | ~spl3_5 | ~spl3_18)),
% 1.47/0.57    inference(subsumption_resolution,[],[f328,f76])).
% 1.47/0.57  fof(f328,plain,(
% 1.47/0.57    k4_xboole_0(sK0,sK1) = k9_relat_1(sK2,k1_xboole_0) | ~r1_tarski(k4_xboole_0(sK0,sK1),k2_relat_1(sK2)) | ~v1_relat_1(sK2) | (~spl3_4 | ~spl3_18)),
% 1.47/0.57    inference(subsumption_resolution,[],[f316,f71])).
% 1.47/0.57  fof(f316,plain,(
% 1.47/0.57    k4_xboole_0(sK0,sK1) = k9_relat_1(sK2,k1_xboole_0) | ~r1_tarski(k4_xboole_0(sK0,sK1),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl3_18),
% 1.47/0.57    inference(superposition,[],[f36,f304])).
% 1.47/0.57  fof(f304,plain,(
% 1.47/0.57    k1_xboole_0 = k10_relat_1(sK2,k4_xboole_0(sK0,sK1)) | ~spl3_18),
% 1.47/0.57    inference(avatar_component_clause,[],[f302])).
% 1.47/0.57  fof(f305,plain,(
% 1.47/0.57    spl3_18 | ~spl3_3 | ~spl3_4 | ~spl3_5),
% 1.47/0.57    inference(avatar_split_clause,[],[f300,f74,f69,f64,f302])).
% 1.47/0.57  fof(f64,plain,(
% 1.47/0.57    spl3_3 <=> r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.47/0.57  fof(f300,plain,(
% 1.47/0.57    k1_xboole_0 = k10_relat_1(sK2,k4_xboole_0(sK0,sK1)) | (~spl3_3 | ~spl3_4 | ~spl3_5)),
% 1.47/0.57    inference(subsumption_resolution,[],[f299,f76])).
% 1.47/0.57  fof(f299,plain,(
% 1.47/0.57    ~v1_relat_1(sK2) | k1_xboole_0 = k10_relat_1(sK2,k4_xboole_0(sK0,sK1)) | (~spl3_3 | ~spl3_4)),
% 1.47/0.57    inference(subsumption_resolution,[],[f294,f71])).
% 1.47/0.57  fof(f294,plain,(
% 1.47/0.57    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k1_xboole_0 = k10_relat_1(sK2,k4_xboole_0(sK0,sK1)) | ~spl3_3),
% 1.47/0.57    inference(resolution,[],[f157,f66])).
% 1.47/0.57  fof(f66,plain,(
% 1.47/0.57    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) | ~spl3_3),
% 1.47/0.57    inference(avatar_component_clause,[],[f64])).
% 1.47/0.57  fof(f280,plain,(
% 1.47/0.57    ~spl3_16),
% 1.47/0.57    inference(avatar_contradiction_clause,[],[f261])).
% 1.47/0.57  fof(f261,plain,(
% 1.47/0.57    $false | ~spl3_16),
% 1.47/0.57    inference(unit_resulting_resolution,[],[f51,f78,f244,f152])).
% 1.47/0.57  fof(f152,plain,(
% 1.47/0.57    ( ! [X2,X0,X3,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X3) | ~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,k3_xboole_0(X3,X2))) )),
% 1.47/0.57    inference(resolution,[],[f37,f38])).
% 1.47/0.57  fof(f37,plain,(
% 1.47/0.57    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 1.47/0.57    inference(cnf_transformation,[],[f20])).
% 1.47/0.57  fof(f20,plain,(
% 1.47/0.57    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 1.47/0.57    inference(flattening,[],[f19])).
% 1.47/0.57  fof(f19,plain,(
% 1.47/0.57    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 1.47/0.57    inference(ennf_transformation,[],[f5])).
% 1.47/0.57  fof(f5,axiom,(
% 1.47/0.57    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 1.47/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).
% 1.47/0.57  fof(f244,plain,(
% 1.47/0.57    ( ! [X0] : (~r1_tarski(sK0,X0)) ) | ~spl3_16),
% 1.47/0.57    inference(avatar_component_clause,[],[f243])).
% 1.47/0.57  fof(f243,plain,(
% 1.47/0.57    spl3_16 <=> ! [X0] : ~r1_tarski(sK0,X0)),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 1.47/0.57  fof(f78,plain,(
% 1.47/0.57    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.47/0.57    inference(resolution,[],[f38,f51])).
% 1.47/0.57  fof(f249,plain,(
% 1.47/0.57    spl3_16 | spl3_17 | ~spl3_3 | ~spl3_4 | ~spl3_5),
% 1.47/0.57    inference(avatar_split_clause,[],[f240,f74,f69,f64,f246,f243])).
% 1.47/0.57  fof(f240,plain,(
% 1.47/0.57    ( ! [X0] : (r1_tarski(k10_relat_1(sK2,k1_xboole_0),k10_relat_1(sK2,sK1)) | ~r1_tarski(sK0,X0)) ) | (~spl3_3 | ~spl3_4 | ~spl3_5)),
% 1.47/0.57    inference(superposition,[],[f237,f40])).
% 1.47/0.57  fof(f237,plain,(
% 1.47/0.57    ( ! [X0] : (r1_tarski(k10_relat_1(sK2,k4_xboole_0(sK0,X0)),k10_relat_1(sK2,sK1))) ) | (~spl3_3 | ~spl3_4 | ~spl3_5)),
% 1.47/0.57    inference(subsumption_resolution,[],[f236,f76])).
% 1.47/0.57  fof(f236,plain,(
% 1.47/0.57    ( ! [X0] : (~v1_relat_1(sK2) | r1_tarski(k10_relat_1(sK2,k4_xboole_0(sK0,X0)),k10_relat_1(sK2,sK1))) ) | (~spl3_3 | ~spl3_4)),
% 1.47/0.57    inference(subsumption_resolution,[],[f230,f71])).
% 1.47/0.57  fof(f230,plain,(
% 1.47/0.57    ( ! [X0] : (~v1_funct_1(sK2) | ~v1_relat_1(sK2) | r1_tarski(k10_relat_1(sK2,k4_xboole_0(sK0,X0)),k10_relat_1(sK2,sK1))) ) | ~spl3_3),
% 1.47/0.57    inference(resolution,[],[f162,f177])).
% 1.47/0.57  fof(f177,plain,(
% 1.47/0.57    ( ! [X17] : (~r1_tarski(X17,k10_relat_1(sK2,sK0)) | r1_tarski(X17,k10_relat_1(sK2,sK1))) ) | ~spl3_3),
% 1.47/0.57    inference(resolution,[],[f99,f66])).
% 1.47/0.57  fof(f162,plain,(
% 1.47/0.57    ( ! [X14,X12,X13] : (r1_tarski(k10_relat_1(X12,k4_xboole_0(X13,X14)),k10_relat_1(X12,X13)) | ~v1_funct_1(X12) | ~v1_relat_1(X12)) )),
% 1.47/0.57    inference(superposition,[],[f46,f156])).
% 1.47/0.57  fof(f77,plain,(
% 1.47/0.57    spl3_5),
% 1.47/0.57    inference(avatar_split_clause,[],[f31,f74])).
% 1.47/0.57  fof(f31,plain,(
% 1.47/0.57    v1_relat_1(sK2)),
% 1.47/0.57    inference(cnf_transformation,[],[f27])).
% 1.47/0.57  fof(f27,plain,(
% 1.47/0.57    ~r1_tarski(sK0,sK1) & r1_tarski(sK0,k2_relat_1(sK2)) & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 1.47/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f26])).
% 1.47/0.57  fof(f26,plain,(
% 1.47/0.57    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_tarski(sK0,sK1) & r1_tarski(sK0,k2_relat_1(sK2)) & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 1.47/0.57    introduced(choice_axiom,[])).
% 1.47/0.57  fof(f16,plain,(
% 1.47/0.57    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 1.47/0.57    inference(flattening,[],[f15])).
% 1.47/0.57  fof(f15,plain,(
% 1.47/0.57    ? [X0,X1,X2] : ((~r1_tarski(X0,X1) & (r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 1.47/0.57    inference(ennf_transformation,[],[f14])).
% 1.47/0.57  fof(f14,negated_conjecture,(
% 1.47/0.57    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 1.47/0.57    inference(negated_conjecture,[],[f13])).
% 1.47/0.57  fof(f13,conjecture,(
% 1.47/0.57    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 1.47/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_funct_1)).
% 1.47/0.57  fof(f72,plain,(
% 1.47/0.57    spl3_4),
% 1.47/0.57    inference(avatar_split_clause,[],[f32,f69])).
% 1.47/0.57  fof(f32,plain,(
% 1.47/0.57    v1_funct_1(sK2)),
% 1.47/0.57    inference(cnf_transformation,[],[f27])).
% 1.47/0.57  fof(f67,plain,(
% 1.47/0.57    spl3_3),
% 1.47/0.57    inference(avatar_split_clause,[],[f33,f64])).
% 1.47/0.57  fof(f33,plain,(
% 1.47/0.57    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),
% 1.47/0.57    inference(cnf_transformation,[],[f27])).
% 1.47/0.57  fof(f62,plain,(
% 1.47/0.57    spl3_2),
% 1.47/0.57    inference(avatar_split_clause,[],[f34,f59])).
% 1.47/0.57  fof(f34,plain,(
% 1.47/0.57    r1_tarski(sK0,k2_relat_1(sK2))),
% 1.47/0.57    inference(cnf_transformation,[],[f27])).
% 1.47/0.57  fof(f57,plain,(
% 1.47/0.57    ~spl3_1),
% 1.47/0.57    inference(avatar_split_clause,[],[f35,f54])).
% 1.47/0.57  fof(f35,plain,(
% 1.47/0.57    ~r1_tarski(sK0,sK1)),
% 1.47/0.57    inference(cnf_transformation,[],[f27])).
% 1.47/0.57  % SZS output end Proof for theBenchmark
% 1.47/0.57  % (17881)------------------------------
% 1.47/0.57  % (17881)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.57  % (17881)Termination reason: Refutation
% 1.47/0.57  
% 1.47/0.57  % (17881)Memory used [KB]: 6652
% 1.47/0.57  % (17881)Time elapsed: 0.163 s
% 1.47/0.57  % (17881)------------------------------
% 1.47/0.57  % (17881)------------------------------
% 1.47/0.57  % (17859)Success in time 0.202 s
%------------------------------------------------------------------------------
