%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:03:36 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 218 expanded)
%              Number of leaves         :   31 (  92 expanded)
%              Depth                    :    7
%              Number of atoms          :  353 ( 730 expanded)
%              Number of equality atoms :   66 ( 157 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f410,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f65,f70,f75,f80,f89,f110,f120,f129,f135,f181,f187,f192,f239,f253,f260,f279,f306,f317,f337,f400,f407])).

fof(f407,plain,
    ( ~ spl4_8
    | spl4_18
    | ~ spl4_32 ),
    inference(avatar_contradiction_clause,[],[f402])).

fof(f402,plain,
    ( $false
    | ~ spl4_8
    | spl4_18
    | ~ spl4_32 ),
    inference(unit_resulting_resolution,[],[f109,f191,f399,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

fof(f399,plain,
    ( r1_tarski(sK2,k1_relat_1(sK3))
    | ~ spl4_32 ),
    inference(avatar_component_clause,[],[f397])).

fof(f397,plain,
    ( spl4_32
  <=> r1_tarski(sK2,k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f191,plain,
    ( ~ r1_tarski(sK2,k10_relat_1(sK3,k9_relat_1(sK3,sK2)))
    | spl4_18 ),
    inference(avatar_component_clause,[],[f189])).

fof(f189,plain,
    ( spl4_18
  <=> r1_tarski(sK2,k10_relat_1(sK3,k9_relat_1(sK3,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f109,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl4_8
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f400,plain,
    ( spl4_32
    | ~ spl4_12
    | ~ spl4_29 ),
    inference(avatar_split_clause,[],[f393,f314,f133,f397])).

fof(f133,plain,
    ( spl4_12
  <=> ! [X7] :
        ( ~ r1_tarski(sK0,X7)
        | r1_tarski(sK2,X7) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f314,plain,
    ( spl4_29
  <=> r1_tarski(sK0,k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).

fof(f393,plain,
    ( r1_tarski(sK2,k1_relat_1(sK3))
    | ~ spl4_12
    | ~ spl4_29 ),
    inference(resolution,[],[f134,f316])).

fof(f316,plain,
    ( r1_tarski(sK0,k1_relat_1(sK3))
    | ~ spl4_29 ),
    inference(avatar_component_clause,[],[f314])).

fof(f134,plain,
    ( ! [X7] :
        ( ~ r1_tarski(sK0,X7)
        | r1_tarski(sK2,X7) )
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f133])).

fof(f337,plain,
    ( ~ spl4_6
    | spl4_28 ),
    inference(avatar_contradiction_clause,[],[f336])).

fof(f336,plain,
    ( $false
    | ~ spl4_6
    | spl4_28 ),
    inference(subsumption_resolution,[],[f335,f39])).

fof(f39,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f335,plain,
    ( ~ r1_tarski(k1_xboole_0,k10_relat_1(sK3,k9_relat_1(sK3,k1_xboole_0)))
    | ~ spl4_6
    | spl4_28 ),
    inference(backward_demodulation,[],[f305,f88])).

fof(f88,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl4_6
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f305,plain,
    ( ~ r1_tarski(sK0,k10_relat_1(sK3,k9_relat_1(sK3,sK0)))
    | spl4_28 ),
    inference(avatar_component_clause,[],[f303])).

fof(f303,plain,
    ( spl4_28
  <=> r1_tarski(sK0,k10_relat_1(sK3,k9_relat_1(sK3,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f317,plain,
    ( spl4_29
    | ~ spl4_8
    | ~ spl4_26 ),
    inference(avatar_split_clause,[],[f311,f257,f107,f314])).

fof(f257,plain,
    ( spl4_26
  <=> sK0 = k10_relat_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f311,plain,
    ( r1_tarski(sK0,k1_relat_1(sK3))
    | ~ spl4_8
    | ~ spl4_26 ),
    inference(subsumption_resolution,[],[f309,f109])).

fof(f309,plain,
    ( r1_tarski(sK0,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ spl4_26 ),
    inference(superposition,[],[f40,f259])).

fof(f259,plain,
    ( sK0 = k10_relat_1(sK3,sK1)
    | ~ spl4_26 ),
    inference(avatar_component_clause,[],[f257])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

fof(f306,plain,
    ( ~ spl4_28
    | ~ spl4_10
    | spl4_18 ),
    inference(avatar_split_clause,[],[f292,f189,f122,f303])).

fof(f122,plain,
    ( spl4_10
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f292,plain,
    ( ~ r1_tarski(sK0,k10_relat_1(sK3,k9_relat_1(sK3,sK0)))
    | ~ spl4_10
    | spl4_18 ),
    inference(backward_demodulation,[],[f191,f124])).

fof(f124,plain,
    ( sK0 = sK2
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f122])).

fof(f279,plain,
    ( ~ spl4_6
    | spl4_11 ),
    inference(avatar_contradiction_clause,[],[f278])).

fof(f278,plain,
    ( $false
    | ~ spl4_6
    | spl4_11 ),
    inference(subsumption_resolution,[],[f276,f39])).

fof(f276,plain,
    ( ~ r1_tarski(k1_xboole_0,sK2)
    | ~ spl4_6
    | spl4_11 ),
    inference(backward_demodulation,[],[f128,f88])).

fof(f128,plain,
    ( ~ r1_tarski(sK0,sK2)
    | spl4_11 ),
    inference(avatar_component_clause,[],[f126])).

fof(f126,plain,
    ( spl4_11
  <=> r1_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f260,plain,
    ( spl4_26
    | ~ spl4_17
    | ~ spl4_25 ),
    inference(avatar_split_clause,[],[f254,f250,f185,f257])).

fof(f185,plain,
    ( spl4_17
  <=> ! [X0] : k10_relat_1(sK3,X0) = k8_relset_1(sK0,sK1,sK3,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f250,plain,
    ( spl4_25
  <=> sK0 = k8_relset_1(sK0,sK1,sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f254,plain,
    ( sK0 = k10_relat_1(sK3,sK1)
    | ~ spl4_17
    | ~ spl4_25 ),
    inference(superposition,[],[f252,f186])).

fof(f186,plain,
    ( ! [X0] : k10_relat_1(sK3,X0) = k8_relset_1(sK0,sK1,sK3,X0)
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f185])).

fof(f252,plain,
    ( sK0 = k8_relset_1(sK0,sK1,sK3,sK1)
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f250])).

fof(f253,plain,
    ( spl4_25
    | ~ spl4_3
    | ~ spl4_4
    | spl4_5
    | ~ spl4_23 ),
    inference(avatar_split_clause,[],[f248,f237,f82,f77,f72,f250])).

fof(f72,plain,
    ( spl4_3
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f77,plain,
    ( spl4_4
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f82,plain,
    ( spl4_5
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f237,plain,
    ( spl4_23
  <=> ! [X1,X0] :
        ( k1_xboole_0 = X0
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(sK3,X1,X0)
        | k8_relset_1(X1,X0,sK3,X0) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f248,plain,
    ( sK0 = k8_relset_1(sK0,sK1,sK3,sK1)
    | ~ spl4_3
    | ~ spl4_4
    | spl4_5
    | ~ spl4_23 ),
    inference(subsumption_resolution,[],[f247,f84])).

fof(f84,plain,
    ( k1_xboole_0 != sK1
    | spl4_5 ),
    inference(avatar_component_clause,[],[f82])).

fof(f247,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k8_relset_1(sK0,sK1,sK3,sK1)
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_23 ),
    inference(subsumption_resolution,[],[f246,f79])).

fof(f79,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f77])).

fof(f246,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_xboole_0 = sK1
    | sK0 = k8_relset_1(sK0,sK1,sK3,sK1)
    | ~ spl4_3
    | ~ spl4_23 ),
    inference(resolution,[],[f238,f74])).

fof(f74,plain,
    ( v1_funct_2(sK3,sK0,sK1)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f72])).

fof(f238,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(sK3,X1,X0)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | k1_xboole_0 = X0
        | k8_relset_1(X1,X0,sK3,X0) = X1 )
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f237])).

fof(f239,plain,
    ( spl4_23
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f156,f62,f237])).

fof(f62,plain,
    ( spl4_1
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f156,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 = X0
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(sK3,X1,X0)
        | k8_relset_1(X1,X0,sK3,X0) = X1 )
    | ~ spl4_1 ),
    inference(resolution,[],[f51,f64])).

fof(f64,plain,
    ( v1_funct_1(sK3)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f62])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k8_relset_1(X0,X1,X2,X1) = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,X1) = X0
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,X1) = X0
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => k8_relset_1(X0,X1,X2,X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_2)).

fof(f192,plain,
    ( ~ spl4_18
    | ~ spl4_4
    | spl4_16 ),
    inference(avatar_split_clause,[],[f183,f178,f77,f189])).

fof(f178,plain,
    ( spl4_16
  <=> r1_tarski(sK2,k8_relset_1(sK0,sK1,sK3,k9_relat_1(sK3,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f183,plain,
    ( ~ r1_tarski(sK2,k10_relat_1(sK3,k9_relat_1(sK3,sK2)))
    | ~ spl4_4
    | spl4_16 ),
    inference(backward_demodulation,[],[f180,f143])).

fof(f143,plain,
    ( ! [X0] : k10_relat_1(sK3,X0) = k8_relset_1(sK0,sK1,sK3,X0)
    | ~ spl4_4 ),
    inference(resolution,[],[f55,f79])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f180,plain,
    ( ~ r1_tarski(sK2,k8_relset_1(sK0,sK1,sK3,k9_relat_1(sK3,sK2)))
    | spl4_16 ),
    inference(avatar_component_clause,[],[f178])).

fof(f187,plain,
    ( spl4_17
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f143,f77,f185])).

fof(f181,plain,
    ( ~ spl4_16
    | ~ spl4_4
    | spl4_9 ),
    inference(avatar_split_clause,[],[f168,f117,f77,f178])).

fof(f117,plain,
    ( spl4_9
  <=> r1_tarski(sK2,k8_relset_1(sK0,sK1,sK3,k7_relset_1(sK0,sK1,sK3,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f168,plain,
    ( ~ r1_tarski(sK2,k8_relset_1(sK0,sK1,sK3,k9_relat_1(sK3,sK2)))
    | ~ spl4_4
    | spl4_9 ),
    inference(backward_demodulation,[],[f119,f138])).

fof(f138,plain,
    ( ! [X0] : k9_relat_1(sK3,X0) = k7_relset_1(sK0,sK1,sK3,X0)
    | ~ spl4_4 ),
    inference(resolution,[],[f54,f79])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f119,plain,
    ( ~ r1_tarski(sK2,k8_relset_1(sK0,sK1,sK3,k7_relset_1(sK0,sK1,sK3,sK2)))
    | spl4_9 ),
    inference(avatar_component_clause,[],[f117])).

fof(f135,plain,
    ( spl4_12
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f114,f67,f133])).

fof(f67,plain,
    ( spl4_2
  <=> r1_tarski(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f114,plain,
    ( ! [X7] :
        ( ~ r1_tarski(sK0,X7)
        | r1_tarski(sK2,X7) )
    | ~ spl4_2 ),
    inference(resolution,[],[f53,f69])).

fof(f69,plain,
    ( r1_tarski(sK2,sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f67])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f129,plain,
    ( spl4_10
    | ~ spl4_11
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f104,f67,f126,f122])).

fof(f104,plain,
    ( ~ r1_tarski(sK0,sK2)
    | sK0 = sK2
    | ~ spl4_2 ),
    inference(resolution,[],[f44,f69])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
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

fof(f120,plain,(
    ~ spl4_9 ),
    inference(avatar_split_clause,[],[f38,f117])).

fof(f38,plain,(
    ~ r1_tarski(sK2,k8_relset_1(sK0,sK1,sK3,k7_relset_1(sK0,sK1,sK3,sK2))) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ~ r1_tarski(sK2,k8_relset_1(sK0,sK1,sK3,k7_relset_1(sK0,sK1,sK3,sK2)))
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_tarski(sK2,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f26])).

fof(f26,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2)))
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & r1_tarski(X2,X0)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ~ r1_tarski(sK2,k8_relset_1(sK0,sK1,sK3,k7_relset_1(sK0,sK1,sK3,sK2)))
      & ( k1_xboole_0 = sK0
        | k1_xboole_0 != sK1 )
      & r1_tarski(sK2,sK0)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2)))
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2)))
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(X2,X0)
         => ( r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2)))
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X2,X0)
       => ( r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2)))
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_funct_2)).

fof(f110,plain,
    ( spl4_8
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f97,f77,f107])).

fof(f97,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_4 ),
    inference(resolution,[],[f50,f79])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f89,plain,
    ( ~ spl4_5
    | spl4_6 ),
    inference(avatar_split_clause,[],[f37,f86,f82])).

fof(f37,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f27])).

fof(f80,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f35,f77])).

fof(f35,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f27])).

fof(f75,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f34,f72])).

fof(f34,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f70,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f36,f67])).

fof(f36,plain,(
    r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f65,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f33,f62])).

fof(f33,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:42:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.45  % (15099)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.46  % (15107)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.47  % (15099)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f410,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(avatar_sat_refutation,[],[f65,f70,f75,f80,f89,f110,f120,f129,f135,f181,f187,f192,f239,f253,f260,f279,f306,f317,f337,f400,f407])).
% 0.20/0.47  fof(f407,plain,(
% 0.20/0.47    ~spl4_8 | spl4_18 | ~spl4_32),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f402])).
% 0.20/0.47  fof(f402,plain,(
% 0.20/0.47    $false | (~spl4_8 | spl4_18 | ~spl4_32)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f109,f191,f399,f41])).
% 0.20/0.47  fof(f41,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f18])).
% 0.20/0.47  fof(f18,plain,(
% 0.20/0.47    ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.20/0.47    inference(flattening,[],[f17])).
% 0.20/0.47  fof(f17,plain,(
% 0.20/0.47    ! [X0,X1] : ((r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.20/0.47    inference(ennf_transformation,[],[f7])).
% 0.20/0.47  fof(f7,axiom,(
% 0.20/0.47    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).
% 0.20/0.47  fof(f399,plain,(
% 0.20/0.47    r1_tarski(sK2,k1_relat_1(sK3)) | ~spl4_32),
% 0.20/0.47    inference(avatar_component_clause,[],[f397])).
% 0.20/0.47  fof(f397,plain,(
% 0.20/0.47    spl4_32 <=> r1_tarski(sK2,k1_relat_1(sK3))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).
% 0.20/0.47  fof(f191,plain,(
% 0.20/0.47    ~r1_tarski(sK2,k10_relat_1(sK3,k9_relat_1(sK3,sK2))) | spl4_18),
% 0.20/0.47    inference(avatar_component_clause,[],[f189])).
% 0.20/0.47  fof(f189,plain,(
% 0.20/0.47    spl4_18 <=> r1_tarski(sK2,k10_relat_1(sK3,k9_relat_1(sK3,sK2)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.20/0.47  fof(f109,plain,(
% 0.20/0.47    v1_relat_1(sK3) | ~spl4_8),
% 0.20/0.47    inference(avatar_component_clause,[],[f107])).
% 0.20/0.47  fof(f107,plain,(
% 0.20/0.47    spl4_8 <=> v1_relat_1(sK3)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.20/0.47  fof(f400,plain,(
% 0.20/0.47    spl4_32 | ~spl4_12 | ~spl4_29),
% 0.20/0.47    inference(avatar_split_clause,[],[f393,f314,f133,f397])).
% 0.20/0.47  fof(f133,plain,(
% 0.20/0.47    spl4_12 <=> ! [X7] : (~r1_tarski(sK0,X7) | r1_tarski(sK2,X7))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.20/0.47  fof(f314,plain,(
% 0.20/0.47    spl4_29 <=> r1_tarski(sK0,k1_relat_1(sK3))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).
% 0.20/0.47  fof(f393,plain,(
% 0.20/0.47    r1_tarski(sK2,k1_relat_1(sK3)) | (~spl4_12 | ~spl4_29)),
% 0.20/0.47    inference(resolution,[],[f134,f316])).
% 0.20/0.47  fof(f316,plain,(
% 0.20/0.47    r1_tarski(sK0,k1_relat_1(sK3)) | ~spl4_29),
% 0.20/0.47    inference(avatar_component_clause,[],[f314])).
% 0.20/0.47  fof(f134,plain,(
% 0.20/0.47    ( ! [X7] : (~r1_tarski(sK0,X7) | r1_tarski(sK2,X7)) ) | ~spl4_12),
% 0.20/0.47    inference(avatar_component_clause,[],[f133])).
% 0.20/0.47  fof(f337,plain,(
% 0.20/0.47    ~spl4_6 | spl4_28),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f336])).
% 0.20/0.47  fof(f336,plain,(
% 0.20/0.47    $false | (~spl4_6 | spl4_28)),
% 0.20/0.47    inference(subsumption_resolution,[],[f335,f39])).
% 0.20/0.47  fof(f39,plain,(
% 0.20/0.47    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f3])).
% 0.20/0.47  fof(f3,axiom,(
% 0.20/0.47    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.20/0.47  fof(f335,plain,(
% 0.20/0.47    ~r1_tarski(k1_xboole_0,k10_relat_1(sK3,k9_relat_1(sK3,k1_xboole_0))) | (~spl4_6 | spl4_28)),
% 0.20/0.47    inference(backward_demodulation,[],[f305,f88])).
% 0.20/0.47  fof(f88,plain,(
% 0.20/0.47    k1_xboole_0 = sK0 | ~spl4_6),
% 0.20/0.47    inference(avatar_component_clause,[],[f86])).
% 0.20/0.47  fof(f86,plain,(
% 0.20/0.47    spl4_6 <=> k1_xboole_0 = sK0),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.20/0.47  fof(f305,plain,(
% 0.20/0.47    ~r1_tarski(sK0,k10_relat_1(sK3,k9_relat_1(sK3,sK0))) | spl4_28),
% 0.20/0.47    inference(avatar_component_clause,[],[f303])).
% 0.20/0.47  fof(f303,plain,(
% 0.20/0.47    spl4_28 <=> r1_tarski(sK0,k10_relat_1(sK3,k9_relat_1(sK3,sK0)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 0.20/0.47  fof(f317,plain,(
% 0.20/0.47    spl4_29 | ~spl4_8 | ~spl4_26),
% 0.20/0.47    inference(avatar_split_clause,[],[f311,f257,f107,f314])).
% 0.20/0.47  fof(f257,plain,(
% 0.20/0.47    spl4_26 <=> sK0 = k10_relat_1(sK3,sK1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 0.20/0.47  fof(f311,plain,(
% 0.20/0.47    r1_tarski(sK0,k1_relat_1(sK3)) | (~spl4_8 | ~spl4_26)),
% 0.20/0.47    inference(subsumption_resolution,[],[f309,f109])).
% 0.20/0.47  fof(f309,plain,(
% 0.20/0.47    r1_tarski(sK0,k1_relat_1(sK3)) | ~v1_relat_1(sK3) | ~spl4_26),
% 0.20/0.47    inference(superposition,[],[f40,f259])).
% 0.20/0.47  fof(f259,plain,(
% 0.20/0.47    sK0 = k10_relat_1(sK3,sK1) | ~spl4_26),
% 0.20/0.47    inference(avatar_component_clause,[],[f257])).
% 0.20/0.47  fof(f40,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f16])).
% 0.20/0.47  fof(f16,plain,(
% 0.20/0.47    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.20/0.47    inference(ennf_transformation,[],[f6])).
% 0.20/0.47  fof(f6,axiom,(
% 0.20/0.47    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).
% 0.20/0.47  fof(f306,plain,(
% 0.20/0.47    ~spl4_28 | ~spl4_10 | spl4_18),
% 0.20/0.47    inference(avatar_split_clause,[],[f292,f189,f122,f303])).
% 0.20/0.47  fof(f122,plain,(
% 0.20/0.47    spl4_10 <=> sK0 = sK2),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.20/0.47  fof(f292,plain,(
% 0.20/0.47    ~r1_tarski(sK0,k10_relat_1(sK3,k9_relat_1(sK3,sK0))) | (~spl4_10 | spl4_18)),
% 0.20/0.47    inference(backward_demodulation,[],[f191,f124])).
% 0.20/0.47  fof(f124,plain,(
% 0.20/0.47    sK0 = sK2 | ~spl4_10),
% 0.20/0.47    inference(avatar_component_clause,[],[f122])).
% 0.20/0.47  fof(f279,plain,(
% 0.20/0.47    ~spl4_6 | spl4_11),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f278])).
% 0.20/0.47  fof(f278,plain,(
% 0.20/0.47    $false | (~spl4_6 | spl4_11)),
% 0.20/0.47    inference(subsumption_resolution,[],[f276,f39])).
% 0.20/0.47  fof(f276,plain,(
% 0.20/0.47    ~r1_tarski(k1_xboole_0,sK2) | (~spl4_6 | spl4_11)),
% 0.20/0.47    inference(backward_demodulation,[],[f128,f88])).
% 0.20/0.47  fof(f128,plain,(
% 0.20/0.47    ~r1_tarski(sK0,sK2) | spl4_11),
% 0.20/0.47    inference(avatar_component_clause,[],[f126])).
% 0.20/0.47  fof(f126,plain,(
% 0.20/0.47    spl4_11 <=> r1_tarski(sK0,sK2)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.20/0.47  fof(f260,plain,(
% 0.20/0.47    spl4_26 | ~spl4_17 | ~spl4_25),
% 0.20/0.47    inference(avatar_split_clause,[],[f254,f250,f185,f257])).
% 0.20/0.47  fof(f185,plain,(
% 0.20/0.47    spl4_17 <=> ! [X0] : k10_relat_1(sK3,X0) = k8_relset_1(sK0,sK1,sK3,X0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 0.20/0.47  fof(f250,plain,(
% 0.20/0.47    spl4_25 <=> sK0 = k8_relset_1(sK0,sK1,sK3,sK1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 0.20/0.47  fof(f254,plain,(
% 0.20/0.47    sK0 = k10_relat_1(sK3,sK1) | (~spl4_17 | ~spl4_25)),
% 0.20/0.47    inference(superposition,[],[f252,f186])).
% 0.20/0.47  fof(f186,plain,(
% 0.20/0.47    ( ! [X0] : (k10_relat_1(sK3,X0) = k8_relset_1(sK0,sK1,sK3,X0)) ) | ~spl4_17),
% 0.20/0.47    inference(avatar_component_clause,[],[f185])).
% 0.20/0.47  fof(f252,plain,(
% 0.20/0.47    sK0 = k8_relset_1(sK0,sK1,sK3,sK1) | ~spl4_25),
% 0.20/0.47    inference(avatar_component_clause,[],[f250])).
% 0.20/0.47  fof(f253,plain,(
% 0.20/0.47    spl4_25 | ~spl4_3 | ~spl4_4 | spl4_5 | ~spl4_23),
% 0.20/0.47    inference(avatar_split_clause,[],[f248,f237,f82,f77,f72,f250])).
% 0.20/0.47  fof(f72,plain,(
% 0.20/0.47    spl4_3 <=> v1_funct_2(sK3,sK0,sK1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.47  fof(f77,plain,(
% 0.20/0.47    spl4_4 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.20/0.47  fof(f82,plain,(
% 0.20/0.47    spl4_5 <=> k1_xboole_0 = sK1),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.20/0.47  fof(f237,plain,(
% 0.20/0.47    spl4_23 <=> ! [X1,X0] : (k1_xboole_0 = X0 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(sK3,X1,X0) | k8_relset_1(X1,X0,sK3,X0) = X1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 0.20/0.47  fof(f248,plain,(
% 0.20/0.47    sK0 = k8_relset_1(sK0,sK1,sK3,sK1) | (~spl4_3 | ~spl4_4 | spl4_5 | ~spl4_23)),
% 0.20/0.47    inference(subsumption_resolution,[],[f247,f84])).
% 0.20/0.47  fof(f84,plain,(
% 0.20/0.47    k1_xboole_0 != sK1 | spl4_5),
% 0.20/0.47    inference(avatar_component_clause,[],[f82])).
% 0.20/0.47  fof(f247,plain,(
% 0.20/0.47    k1_xboole_0 = sK1 | sK0 = k8_relset_1(sK0,sK1,sK3,sK1) | (~spl4_3 | ~spl4_4 | ~spl4_23)),
% 0.20/0.47    inference(subsumption_resolution,[],[f246,f79])).
% 0.20/0.47  fof(f79,plain,(
% 0.20/0.47    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_4),
% 0.20/0.47    inference(avatar_component_clause,[],[f77])).
% 0.20/0.47  fof(f246,plain,(
% 0.20/0.47    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | k1_xboole_0 = sK1 | sK0 = k8_relset_1(sK0,sK1,sK3,sK1) | (~spl4_3 | ~spl4_23)),
% 0.20/0.47    inference(resolution,[],[f238,f74])).
% 0.20/0.47  fof(f74,plain,(
% 0.20/0.47    v1_funct_2(sK3,sK0,sK1) | ~spl4_3),
% 0.20/0.47    inference(avatar_component_clause,[],[f72])).
% 0.20/0.47  fof(f238,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~v1_funct_2(sK3,X1,X0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k1_xboole_0 = X0 | k8_relset_1(X1,X0,sK3,X0) = X1) ) | ~spl4_23),
% 0.20/0.47    inference(avatar_component_clause,[],[f237])).
% 0.20/0.47  fof(f239,plain,(
% 0.20/0.47    spl4_23 | ~spl4_1),
% 0.20/0.47    inference(avatar_split_clause,[],[f156,f62,f237])).
% 0.20/0.47  fof(f62,plain,(
% 0.20/0.47    spl4_1 <=> v1_funct_1(sK3)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.47  fof(f156,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k1_xboole_0 = X0 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(sK3,X1,X0) | k8_relset_1(X1,X0,sK3,X0) = X1) ) | ~spl4_1),
% 0.20/0.47    inference(resolution,[],[f51,f64])).
% 0.20/0.47  fof(f64,plain,(
% 0.20/0.47    v1_funct_1(sK3) | ~spl4_1),
% 0.20/0.47    inference(avatar_component_clause,[],[f62])).
% 0.20/0.47  fof(f51,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k8_relset_1(X0,X1,X2,X1) = X0) )),
% 0.20/0.47    inference(cnf_transformation,[],[f21])).
% 0.20/0.47  fof(f21,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (k8_relset_1(X0,X1,X2,X1) = X0 | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.20/0.47    inference(flattening,[],[f20])).
% 0.20/0.47  fof(f20,plain,(
% 0.20/0.47    ! [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,X1) = X0 | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.20/0.47    inference(ennf_transformation,[],[f11])).
% 0.20/0.47  fof(f11,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => k8_relset_1(X0,X1,X2,X1) = X0))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_2)).
% 0.20/0.47  fof(f192,plain,(
% 0.20/0.47    ~spl4_18 | ~spl4_4 | spl4_16),
% 0.20/0.47    inference(avatar_split_clause,[],[f183,f178,f77,f189])).
% 0.20/0.47  fof(f178,plain,(
% 0.20/0.47    spl4_16 <=> r1_tarski(sK2,k8_relset_1(sK0,sK1,sK3,k9_relat_1(sK3,sK2)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.20/0.47  fof(f183,plain,(
% 0.20/0.47    ~r1_tarski(sK2,k10_relat_1(sK3,k9_relat_1(sK3,sK2))) | (~spl4_4 | spl4_16)),
% 0.20/0.47    inference(backward_demodulation,[],[f180,f143])).
% 0.20/0.47  fof(f143,plain,(
% 0.20/0.47    ( ! [X0] : (k10_relat_1(sK3,X0) = k8_relset_1(sK0,sK1,sK3,X0)) ) | ~spl4_4),
% 0.20/0.47    inference(resolution,[],[f55,f79])).
% 0.20/0.47  fof(f55,plain,(
% 0.20/0.47    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f25])).
% 0.20/0.47  fof(f25,plain,(
% 0.20/0.47    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.47    inference(ennf_transformation,[],[f10])).
% 0.20/0.47  fof(f10,axiom,(
% 0.20/0.47    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.20/0.47  fof(f180,plain,(
% 0.20/0.47    ~r1_tarski(sK2,k8_relset_1(sK0,sK1,sK3,k9_relat_1(sK3,sK2))) | spl4_16),
% 0.20/0.47    inference(avatar_component_clause,[],[f178])).
% 0.20/0.47  fof(f187,plain,(
% 0.20/0.47    spl4_17 | ~spl4_4),
% 0.20/0.47    inference(avatar_split_clause,[],[f143,f77,f185])).
% 0.20/0.47  fof(f181,plain,(
% 0.20/0.47    ~spl4_16 | ~spl4_4 | spl4_9),
% 0.20/0.47    inference(avatar_split_clause,[],[f168,f117,f77,f178])).
% 0.20/0.47  fof(f117,plain,(
% 0.20/0.47    spl4_9 <=> r1_tarski(sK2,k8_relset_1(sK0,sK1,sK3,k7_relset_1(sK0,sK1,sK3,sK2)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.20/0.47  fof(f168,plain,(
% 0.20/0.47    ~r1_tarski(sK2,k8_relset_1(sK0,sK1,sK3,k9_relat_1(sK3,sK2))) | (~spl4_4 | spl4_9)),
% 0.20/0.47    inference(backward_demodulation,[],[f119,f138])).
% 0.20/0.47  fof(f138,plain,(
% 0.20/0.47    ( ! [X0] : (k9_relat_1(sK3,X0) = k7_relset_1(sK0,sK1,sK3,X0)) ) | ~spl4_4),
% 0.20/0.47    inference(resolution,[],[f54,f79])).
% 0.20/0.47  fof(f54,plain,(
% 0.20/0.47    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f24])).
% 0.20/0.47  fof(f24,plain,(
% 0.20/0.47    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.47    inference(ennf_transformation,[],[f9])).
% 0.20/0.47  fof(f9,axiom,(
% 0.20/0.47    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.20/0.47  fof(f119,plain,(
% 0.20/0.47    ~r1_tarski(sK2,k8_relset_1(sK0,sK1,sK3,k7_relset_1(sK0,sK1,sK3,sK2))) | spl4_9),
% 0.20/0.47    inference(avatar_component_clause,[],[f117])).
% 0.20/0.47  fof(f135,plain,(
% 0.20/0.47    spl4_12 | ~spl4_2),
% 0.20/0.47    inference(avatar_split_clause,[],[f114,f67,f133])).
% 0.20/0.47  fof(f67,plain,(
% 0.20/0.47    spl4_2 <=> r1_tarski(sK2,sK0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.47  fof(f114,plain,(
% 0.20/0.47    ( ! [X7] : (~r1_tarski(sK0,X7) | r1_tarski(sK2,X7)) ) | ~spl4_2),
% 0.20/0.47    inference(resolution,[],[f53,f69])).
% 0.20/0.47  fof(f69,plain,(
% 0.20/0.47    r1_tarski(sK2,sK0) | ~spl4_2),
% 0.20/0.47    inference(avatar_component_clause,[],[f67])).
% 0.20/0.47  fof(f53,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X2) | r1_tarski(X0,X2)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f23])).
% 0.20/0.47  fof(f23,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.20/0.47    inference(flattening,[],[f22])).
% 0.20/0.47  fof(f22,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.20/0.47    inference(ennf_transformation,[],[f2])).
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.20/0.47  fof(f129,plain,(
% 0.20/0.47    spl4_10 | ~spl4_11 | ~spl4_2),
% 0.20/0.47    inference(avatar_split_clause,[],[f104,f67,f126,f122])).
% 0.20/0.47  fof(f104,plain,(
% 0.20/0.47    ~r1_tarski(sK0,sK2) | sK0 = sK2 | ~spl4_2),
% 0.20/0.47    inference(resolution,[],[f44,f69])).
% 0.20/0.47  fof(f44,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.20/0.47    inference(cnf_transformation,[],[f29])).
% 0.20/0.47  fof(f29,plain,(
% 0.20/0.47    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.47    inference(flattening,[],[f28])).
% 0.20/0.47  fof(f28,plain,(
% 0.20/0.47    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.47    inference(nnf_transformation,[],[f1])).
% 0.20/0.47  fof(f1,axiom,(
% 0.20/0.47    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.47  fof(f120,plain,(
% 0.20/0.47    ~spl4_9),
% 0.20/0.47    inference(avatar_split_clause,[],[f38,f117])).
% 0.20/0.47  fof(f38,plain,(
% 0.20/0.47    ~r1_tarski(sK2,k8_relset_1(sK0,sK1,sK3,k7_relset_1(sK0,sK1,sK3,sK2)))),
% 0.20/0.47    inference(cnf_transformation,[],[f27])).
% 0.20/0.47  fof(f27,plain,(
% 0.20/0.47    ~r1_tarski(sK2,k8_relset_1(sK0,sK1,sK3,k7_relset_1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f26])).
% 0.20/0.47  fof(f26,plain,(
% 0.20/0.47    ? [X0,X1,X2,X3] : (~r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (~r1_tarski(sK2,k8_relset_1(sK0,sK1,sK3,k7_relset_1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f15,plain,(
% 0.20/0.47    ? [X0,X1,X2,X3] : (~r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.20/0.47    inference(flattening,[],[f14])).
% 0.20/0.47  fof(f14,plain,(
% 0.20/0.47    ? [X0,X1,X2,X3] : (((~r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.20/0.47    inference(ennf_transformation,[],[f13])).
% 0.20/0.47  fof(f13,negated_conjecture,(
% 0.20/0.47    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => (r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.20/0.47    inference(negated_conjecture,[],[f12])).
% 0.20/0.47  fof(f12,conjecture,(
% 0.20/0.47    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => (r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_funct_2)).
% 0.20/0.47  fof(f110,plain,(
% 0.20/0.47    spl4_8 | ~spl4_4),
% 0.20/0.47    inference(avatar_split_clause,[],[f97,f77,f107])).
% 0.20/0.47  fof(f97,plain,(
% 0.20/0.47    v1_relat_1(sK3) | ~spl4_4),
% 0.20/0.47    inference(resolution,[],[f50,f79])).
% 0.20/0.47  fof(f50,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f19])).
% 0.20/0.47  fof(f19,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.47    inference(ennf_transformation,[],[f8])).
% 0.20/0.48  fof(f8,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.20/0.48  fof(f89,plain,(
% 0.20/0.48    ~spl4_5 | spl4_6),
% 0.20/0.48    inference(avatar_split_clause,[],[f37,f86,f82])).
% 0.20/0.48  fof(f37,plain,(
% 0.20/0.48    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 0.20/0.48    inference(cnf_transformation,[],[f27])).
% 0.20/0.48  fof(f80,plain,(
% 0.20/0.48    spl4_4),
% 0.20/0.48    inference(avatar_split_clause,[],[f35,f77])).
% 0.20/0.48  fof(f35,plain,(
% 0.20/0.48    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.48    inference(cnf_transformation,[],[f27])).
% 0.20/0.48  fof(f75,plain,(
% 0.20/0.48    spl4_3),
% 0.20/0.48    inference(avatar_split_clause,[],[f34,f72])).
% 0.20/0.48  fof(f34,plain,(
% 0.20/0.48    v1_funct_2(sK3,sK0,sK1)),
% 0.20/0.48    inference(cnf_transformation,[],[f27])).
% 0.20/0.48  fof(f70,plain,(
% 0.20/0.48    spl4_2),
% 0.20/0.48    inference(avatar_split_clause,[],[f36,f67])).
% 0.20/0.48  fof(f36,plain,(
% 0.20/0.48    r1_tarski(sK2,sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f27])).
% 0.20/0.48  fof(f65,plain,(
% 0.20/0.48    spl4_1),
% 0.20/0.48    inference(avatar_split_clause,[],[f33,f62])).
% 0.20/0.48  fof(f33,plain,(
% 0.20/0.48    v1_funct_1(sK3)),
% 0.20/0.48    inference(cnf_transformation,[],[f27])).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (15099)------------------------------
% 0.20/0.48  % (15099)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (15099)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (15099)Memory used [KB]: 6396
% 0.20/0.48  % (15099)Time elapsed: 0.059 s
% 0.20/0.48  % (15099)------------------------------
% 0.20/0.48  % (15099)------------------------------
% 0.20/0.48  % (15096)Success in time 0.12 s
%------------------------------------------------------------------------------
