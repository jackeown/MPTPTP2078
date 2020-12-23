%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:01:24 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.89s
% Verified   : 
% Statistics : Number of formulae       :  147 ( 282 expanded)
%              Number of leaves         :   32 ( 103 expanded)
%              Depth                    :   13
%              Number of atoms          :  493 (1044 expanded)
%              Number of equality atoms :   51 ( 123 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1247,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f75,f80,f85,f90,f95,f100,f106,f122,f143,f163,f185,f276,f306,f882,f972,f1210,f1227])).

fof(f1227,plain,
    ( ~ spl4_9
    | ~ spl4_11
    | spl4_14
    | ~ spl4_68 ),
    inference(avatar_contradiction_clause,[],[f1226])).

fof(f1226,plain,
    ( $false
    | ~ spl4_9
    | ~ spl4_11
    | spl4_14
    | ~ spl4_68 ),
    inference(subsumption_resolution,[],[f1225,f121])).

fof(f121,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl4_9
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f1225,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl4_11
    | spl4_14
    | ~ spl4_68 ),
    inference(subsumption_resolution,[],[f1224,f142])).

fof(f142,plain,
    ( v5_relat_1(sK2,sK1)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f140])).

fof(f140,plain,
    ( spl4_11
  <=> v5_relat_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f1224,plain,
    ( ~ v5_relat_1(sK2,sK1)
    | ~ v1_relat_1(sK2)
    | spl4_14
    | ~ spl4_68 ),
    inference(subsumption_resolution,[],[f1215,f162])).

fof(f162,plain,
    ( sK1 != k2_relat_1(sK2)
    | spl4_14 ),
    inference(avatar_component_clause,[],[f160])).

fof(f160,plain,
    ( spl4_14
  <=> sK1 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f1215,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ v5_relat_1(sK2,sK1)
    | ~ v1_relat_1(sK2)
    | ~ spl4_68 ),
    inference(resolution,[],[f1209,f474])).

fof(f474,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(k6_relat_1(X0),k2_relat_1(X1))
      | k2_relat_1(X1) = X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f444,f123])).

fof(f123,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(subsumption_resolution,[],[f110,f63])).

fof(f63,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f110,plain,(
    ! [X0] :
      ( v1_relat_1(k6_relat_1(X0))
      | ~ v1_relat_1(k2_zfmisc_1(X0,X0)) ) ),
    inference(resolution,[],[f62,f107])).

fof(f107,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(forward_demodulation,[],[f56,f55])).

fof(f55,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f56,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f444,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ~ v1_relat_1(k6_relat_1(X0))
      | ~ v5_relat_1(k6_relat_1(X0),k2_relat_1(X1))
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(superposition,[],[f208,f54])).

fof(f54,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f208,plain,(
    ! [X2,X1] :
      ( k2_relat_1(X1) = k2_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v5_relat_1(X1,k2_relat_1(X2))
      | ~ v5_relat_1(X2,k2_relat_1(X1))
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f125,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f125,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | k2_relat_1(X0) = X1
      | ~ v5_relat_1(X0,X1) ) ),
    inference(resolution,[],[f64,f52])).

fof(f52,plain,(
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

fof(f1209,plain,
    ( v5_relat_1(k6_relat_1(sK1),k2_relat_1(sK2))
    | ~ spl4_68 ),
    inference(avatar_component_clause,[],[f1207])).

fof(f1207,plain,
    ( spl4_68
  <=> v5_relat_1(k6_relat_1(sK1),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_68])])).

fof(f1210,plain,
    ( spl4_68
    | ~ spl4_6
    | ~ spl4_9
    | ~ spl4_46 ),
    inference(avatar_split_clause,[],[f1202,f740,f119,f97,f1207])).

fof(f97,plain,
    ( spl4_6
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f740,plain,
    ( spl4_46
  <=> ! [X5,X6] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
        | v5_relat_1(k6_relat_1(sK1),X6) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).

fof(f1202,plain,
    ( v5_relat_1(k6_relat_1(sK1),k2_relat_1(sK2))
    | ~ spl4_6
    | ~ spl4_9
    | ~ spl4_46 ),
    inference(resolution,[],[f1177,f68])).

fof(f68,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f1177,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_relat_1(sK2),X0)
        | v5_relat_1(k6_relat_1(sK1),X0) )
    | ~ spl4_6
    | ~ spl4_9
    | ~ spl4_46 ),
    inference(subsumption_resolution,[],[f1176,f121])).

fof(f1176,plain,
    ( ! [X0] :
        ( v5_relat_1(k6_relat_1(sK1),X0)
        | ~ r1_tarski(k2_relat_1(sK2),X0)
        | ~ v1_relat_1(sK2) )
    | ~ spl4_6
    | ~ spl4_46 ),
    inference(subsumption_resolution,[],[f1175,f99])).

fof(f99,plain,
    ( v1_funct_1(sK2)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f97])).

fof(f1175,plain,
    ( ! [X0] :
        ( v5_relat_1(k6_relat_1(sK1),X0)
        | ~ r1_tarski(k2_relat_1(sK2),X0)
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl4_46 ),
    inference(resolution,[],[f741,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_1(X1) ) ) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

fof(f741,plain,
    ( ! [X6,X5] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
        | v5_relat_1(k6_relat_1(sK1),X6) )
    | ~ spl4_46 ),
    inference(avatar_component_clause,[],[f740])).

fof(f972,plain,
    ( spl4_45
    | spl4_46
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_27 ),
    inference(avatar_split_clause,[],[f949,f273,f97,f87,f740,f737])).

fof(f737,plain,
    ( spl4_45
  <=> ! [X7,X8] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X7,X8))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).

fof(f87,plain,
    ( spl4_4
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f273,plain,
    ( spl4_27
  <=> k6_relat_1(sK1) = k5_relat_1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f949,plain,
    ( ! [X6,X8,X7,X5] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
        | v5_relat_1(k6_relat_1(sK1),X6) )
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_27 ),
    inference(resolution,[],[f315,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f315,plain,
    ( ! [X2,X0,X3,X1] :
        ( m1_subset_1(k6_relat_1(sK1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) )
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_27 ),
    inference(subsumption_resolution,[],[f314,f89])).

fof(f89,plain,
    ( v1_funct_1(sK3)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f87])).

fof(f314,plain,
    ( ! [X2,X0,X3,X1] :
        ( m1_subset_1(k6_relat_1(sK1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        | ~ v1_funct_1(sK3) )
    | ~ spl4_6
    | ~ spl4_27 ),
    inference(subsumption_resolution,[],[f312,f99])).

fof(f312,plain,
    ( ! [X2,X0,X3,X1] :
        ( m1_subset_1(k6_relat_1(sK1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        | ~ v1_funct_1(sK2)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        | ~ v1_funct_1(sK3) )
    | ~ spl4_27 ),
    inference(superposition,[],[f191,f275])).

fof(f275,plain,
    ( k6_relat_1(sK1) = k5_relat_1(sK3,sK2)
    | ~ spl4_27 ),
    inference(avatar_component_clause,[],[f273])).

fof(f191,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(duplicate_literal_removal,[],[f190])).

fof(f190,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(superposition,[],[f58,f59])).

fof(f59,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f58,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f882,plain,
    ( ~ spl4_3
    | ~ spl4_45 ),
    inference(avatar_contradiction_clause,[],[f877])).

fof(f877,plain,
    ( $false
    | ~ spl4_3
    | ~ spl4_45 ),
    inference(unit_resulting_resolution,[],[f84,f738])).

fof(f738,plain,
    ( ! [X8,X7] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
    | ~ spl4_45 ),
    inference(avatar_component_clause,[],[f737])).

fof(f84,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl4_3
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f306,plain,
    ( ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | spl4_26 ),
    inference(avatar_contradiction_clause,[],[f296])).

fof(f296,plain,
    ( $false
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | spl4_26 ),
    inference(unit_resulting_resolution,[],[f89,f99,f84,f94,f271,f191])).

fof(f271,plain,
    ( ~ m1_subset_1(k5_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | spl4_26 ),
    inference(avatar_component_clause,[],[f269])).

fof(f269,plain,
    ( spl4_26
  <=> m1_subset_1(k5_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f94,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl4_5
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f276,plain,
    ( ~ spl4_26
    | spl4_27
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f258,f182,f273,f269])).

fof(f182,plain,
    ( spl4_15
  <=> r2_relset_1(sK1,sK1,k5_relat_1(sK3,sK2),k6_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f258,plain,
    ( k6_relat_1(sK1) = k5_relat_1(sK3,sK2)
    | ~ m1_subset_1(k5_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ spl4_15 ),
    inference(resolution,[],[f171,f184])).

fof(f184,plain,
    ( r2_relset_1(sK1,sK1,k5_relat_1(sK3,sK2),k6_relat_1(sK1))
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f182])).

fof(f171,plain,(
    ! [X4,X3] :
      ( ~ r2_relset_1(X3,X3,X4,k6_relat_1(X3))
      | k6_relat_1(X3) = X4
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X3))) ) ),
    inference(resolution,[],[f47,f107])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f185,plain,
    ( spl4_15
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f180,f103,f97,f92,f87,f82,f182])).

fof(f103,plain,
    ( spl4_7
  <=> r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2),k6_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f180,plain,
    ( r2_relset_1(sK1,sK1,k5_relat_1(sK3,sK2),k6_relat_1(sK1))
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f179,f89])).

fof(f179,plain,
    ( r2_relset_1(sK1,sK1,k5_relat_1(sK3,sK2),k6_relat_1(sK1))
    | ~ v1_funct_1(sK3)
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f178,f84])).

fof(f178,plain,
    ( r2_relset_1(sK1,sK1,k5_relat_1(sK3,sK2),k6_relat_1(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f177,f99])).

fof(f177,plain,
    ( r2_relset_1(sK1,sK1,k5_relat_1(sK3,sK2),k6_relat_1(sK1))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ spl4_5
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f174,f94])).

fof(f174,plain,
    ( r2_relset_1(sK1,sK1,k5_relat_1(sK3,sK2),k6_relat_1(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ spl4_7 ),
    inference(superposition,[],[f105,f59])).

fof(f105,plain,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2),k6_relat_1(sK1))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f103])).

fof(f163,plain,
    ( ~ spl4_14
    | spl4_1
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f158,f92,f72,f160])).

fof(f72,plain,
    ( spl4_1
  <=> sK1 = k2_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f158,plain,
    ( sK1 != k2_relat_1(sK2)
    | spl4_1
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f157,f94])).

fof(f157,plain,
    ( sK1 != k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl4_1 ),
    inference(superposition,[],[f74,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f74,plain,
    ( sK1 != k2_relset_1(sK0,sK1,sK2)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f72])).

fof(f143,plain,
    ( spl4_11
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f132,f92,f140])).

fof(f132,plain,
    ( v5_relat_1(sK2,sK1)
    | ~ spl4_5 ),
    inference(resolution,[],[f66,f94])).

fof(f122,plain,
    ( spl4_9
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f117,f92,f119])).

fof(f117,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f109,f63])).

fof(f109,plain,
    ( v1_relat_1(sK2)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | ~ spl4_5 ),
    inference(resolution,[],[f62,f94])).

fof(f106,plain,
    ( spl4_7
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f101,f77,f103])).

fof(f77,plain,
    ( spl4_2
  <=> r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2),k6_partfun1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f101,plain,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2),k6_relat_1(sK1))
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f79,f55])).

fof(f79,plain,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2),k6_partfun1(sK1))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f77])).

fof(f100,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f41,f97])).

fof(f41,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( sK1 != k2_relset_1(sK0,sK1,sK2)
    & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2),k6_partfun1(sK1))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f21,f35,f34])).

fof(f34,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( k2_relset_1(X0,X1,X2) != X1
            & r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( sK1 != k2_relset_1(sK0,sK1,sK2)
          & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK0,sK0,sK1,X3,sK2),k6_partfun1(sK1))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X3] :
        ( sK1 != k2_relset_1(sK0,sK1,sK2)
        & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK0,sK0,sK1,X3,sK2),k6_partfun1(sK1))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        & v1_funct_1(X3) )
   => ( sK1 != k2_relset_1(sK0,sK1,sK2)
      & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2),k6_partfun1(sK1))
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_relset_1(X0,X1,X2) != X1
          & r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_relset_1(X0,X1,X2) != X1
          & r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_1(X3) )
           => ( r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
             => k2_relset_1(X0,X1,X2) = X1 ) ) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
           => ( r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
             => k2_relset_1(X0,X1,X2) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
           => k2_relset_1(X0,X1,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_funct_2)).

fof(f95,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f42,f92])).

fof(f42,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f36])).

fof(f90,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f43,f87])).

fof(f43,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f85,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f44,f82])).

fof(f44,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f36])).

fof(f80,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f45,f77])).

fof(f45,plain,(
    r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2),k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f36])).

fof(f75,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f46,f72])).

fof(f46,plain,(
    sK1 != k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:18:44 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.50  % (10416)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.50  % (10437)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.50  % (10432)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.50  % (10417)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (10415)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.52  % (10423)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.52  % (10420)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.53  % (10425)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.53  % (10411)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.53  % (10414)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.54  % (10412)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.54  % (10413)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.54  % (10435)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.54  % (10439)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.54  % (10421)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.54  % (10439)Refutation not found, incomplete strategy% (10439)------------------------------
% 0.21/0.54  % (10439)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (10439)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (10439)Memory used [KB]: 10874
% 0.21/0.54  % (10439)Time elapsed: 0.131 s
% 0.21/0.54  % (10439)------------------------------
% 0.21/0.54  % (10439)------------------------------
% 0.21/0.54  % (10428)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.54  % (10426)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.55  % (10419)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.55  % (10431)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.55  % (10438)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.55  % (10422)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.55  % (10438)Refutation not found, incomplete strategy% (10438)------------------------------
% 0.21/0.55  % (10438)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (10438)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (10438)Memory used [KB]: 6268
% 0.21/0.55  % (10438)Time elapsed: 0.138 s
% 0.21/0.55  % (10438)------------------------------
% 0.21/0.55  % (10438)------------------------------
% 0.21/0.55  % (10436)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.55  % (10429)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.55  % (10418)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.55  % (10433)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.56  % (10424)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.56  % (10434)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.56  % (10440)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.57  % (10427)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.57  % (10430)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.57  % (10421)Refutation not found, incomplete strategy% (10421)------------------------------
% 0.21/0.57  % (10421)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (10427)Refutation not found, incomplete strategy% (10427)------------------------------
% 0.21/0.57  % (10427)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (10427)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (10427)Memory used [KB]: 10618
% 0.21/0.57  % (10427)Time elapsed: 0.169 s
% 0.21/0.57  % (10427)------------------------------
% 0.21/0.57  % (10427)------------------------------
% 0.21/0.58  % (10421)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.58  
% 0.21/0.58  % (10421)Memory used [KB]: 10874
% 0.21/0.58  % (10421)Time elapsed: 0.141 s
% 0.21/0.58  % (10421)------------------------------
% 0.21/0.58  % (10421)------------------------------
% 0.21/0.59  % (10432)Refutation found. Thanks to Tanya!
% 0.21/0.59  % SZS status Theorem for theBenchmark
% 1.77/0.61  % SZS output start Proof for theBenchmark
% 1.77/0.61  fof(f1247,plain,(
% 1.77/0.61    $false),
% 1.77/0.61    inference(avatar_sat_refutation,[],[f75,f80,f85,f90,f95,f100,f106,f122,f143,f163,f185,f276,f306,f882,f972,f1210,f1227])).
% 1.77/0.61  fof(f1227,plain,(
% 1.77/0.61    ~spl4_9 | ~spl4_11 | spl4_14 | ~spl4_68),
% 1.77/0.61    inference(avatar_contradiction_clause,[],[f1226])).
% 1.77/0.61  fof(f1226,plain,(
% 1.77/0.61    $false | (~spl4_9 | ~spl4_11 | spl4_14 | ~spl4_68)),
% 1.77/0.61    inference(subsumption_resolution,[],[f1225,f121])).
% 1.89/0.61  fof(f121,plain,(
% 1.89/0.61    v1_relat_1(sK2) | ~spl4_9),
% 1.89/0.61    inference(avatar_component_clause,[],[f119])).
% 1.89/0.61  fof(f119,plain,(
% 1.89/0.61    spl4_9 <=> v1_relat_1(sK2)),
% 1.89/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 1.89/0.61  fof(f1225,plain,(
% 1.89/0.61    ~v1_relat_1(sK2) | (~spl4_11 | spl4_14 | ~spl4_68)),
% 1.89/0.61    inference(subsumption_resolution,[],[f1224,f142])).
% 1.89/0.61  fof(f142,plain,(
% 1.89/0.61    v5_relat_1(sK2,sK1) | ~spl4_11),
% 1.89/0.61    inference(avatar_component_clause,[],[f140])).
% 1.89/0.61  fof(f140,plain,(
% 1.89/0.61    spl4_11 <=> v5_relat_1(sK2,sK1)),
% 1.89/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 1.89/0.61  fof(f1224,plain,(
% 1.89/0.61    ~v5_relat_1(sK2,sK1) | ~v1_relat_1(sK2) | (spl4_14 | ~spl4_68)),
% 1.89/0.61    inference(subsumption_resolution,[],[f1215,f162])).
% 1.89/0.61  fof(f162,plain,(
% 1.89/0.61    sK1 != k2_relat_1(sK2) | spl4_14),
% 1.89/0.61    inference(avatar_component_clause,[],[f160])).
% 1.89/0.61  fof(f160,plain,(
% 1.89/0.61    spl4_14 <=> sK1 = k2_relat_1(sK2)),
% 1.89/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 1.89/0.61  fof(f1215,plain,(
% 1.89/0.61    sK1 = k2_relat_1(sK2) | ~v5_relat_1(sK2,sK1) | ~v1_relat_1(sK2) | ~spl4_68),
% 1.89/0.61    inference(resolution,[],[f1209,f474])).
% 1.89/0.61  fof(f474,plain,(
% 1.89/0.61    ( ! [X0,X1] : (~v5_relat_1(k6_relat_1(X0),k2_relat_1(X1)) | k2_relat_1(X1) = X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.89/0.61    inference(subsumption_resolution,[],[f444,f123])).
% 1.89/0.61  fof(f123,plain,(
% 1.89/0.61    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.89/0.61    inference(subsumption_resolution,[],[f110,f63])).
% 1.89/0.61  fof(f63,plain,(
% 1.89/0.61    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.89/0.61    inference(cnf_transformation,[],[f4])).
% 1.89/0.61  fof(f4,axiom,(
% 1.89/0.61    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.89/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.89/0.61  fof(f110,plain,(
% 1.89/0.61    ( ! [X0] : (v1_relat_1(k6_relat_1(X0)) | ~v1_relat_1(k2_zfmisc_1(X0,X0))) )),
% 1.89/0.61    inference(resolution,[],[f62,f107])).
% 1.89/0.61  fof(f107,plain,(
% 1.89/0.61    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.89/0.61    inference(forward_demodulation,[],[f56,f55])).
% 1.89/0.61  fof(f55,plain,(
% 1.89/0.61    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.89/0.61    inference(cnf_transformation,[],[f12])).
% 1.89/0.61  fof(f12,axiom,(
% 1.89/0.61    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.89/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.89/0.61  fof(f56,plain,(
% 1.89/0.61    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.89/0.61    inference(cnf_transformation,[],[f18])).
% 1.89/0.61  fof(f18,plain,(
% 1.89/0.61    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 1.89/0.61    inference(pure_predicate_removal,[],[f10])).
% 1.89/0.61  fof(f10,axiom,(
% 1.89/0.61    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 1.89/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 1.89/0.61  fof(f62,plain,(
% 1.89/0.61    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.89/0.61    inference(cnf_transformation,[],[f31])).
% 1.89/0.61  fof(f31,plain,(
% 1.89/0.61    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.89/0.61    inference(ennf_transformation,[],[f2])).
% 1.89/0.61  fof(f2,axiom,(
% 1.89/0.61    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.89/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.89/0.61  fof(f444,plain,(
% 1.89/0.61    ( ! [X0,X1] : (k2_relat_1(X1) = X0 | ~v1_relat_1(k6_relat_1(X0)) | ~v5_relat_1(k6_relat_1(X0),k2_relat_1(X1)) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.89/0.61    inference(superposition,[],[f208,f54])).
% 1.89/0.61  fof(f54,plain,(
% 1.89/0.61    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 1.89/0.61    inference(cnf_transformation,[],[f5])).
% 1.89/0.61  fof(f5,axiom,(
% 1.89/0.61    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.89/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 1.89/0.61  fof(f208,plain,(
% 1.89/0.61    ( ! [X2,X1] : (k2_relat_1(X1) = k2_relat_1(X2) | ~v1_relat_1(X1) | ~v5_relat_1(X1,k2_relat_1(X2)) | ~v5_relat_1(X2,k2_relat_1(X1)) | ~v1_relat_1(X2)) )),
% 1.89/0.61    inference(resolution,[],[f125,f64])).
% 1.89/0.61  fof(f64,plain,(
% 1.89/0.61    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.89/0.61    inference(cnf_transformation,[],[f40])).
% 1.89/0.61  fof(f40,plain,(
% 1.89/0.61    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.89/0.61    inference(nnf_transformation,[],[f32])).
% 1.89/0.61  fof(f32,plain,(
% 1.89/0.61    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.89/0.61    inference(ennf_transformation,[],[f3])).
% 1.89/0.61  fof(f3,axiom,(
% 1.89/0.61    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.89/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 1.89/0.61  fof(f125,plain,(
% 1.89/0.61    ( ! [X0,X1] : (~r1_tarski(X1,k2_relat_1(X0)) | ~v1_relat_1(X0) | k2_relat_1(X0) = X1 | ~v5_relat_1(X0,X1)) )),
% 1.89/0.61    inference(resolution,[],[f64,f52])).
% 1.89/0.61  fof(f52,plain,(
% 1.89/0.61    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.89/0.61    inference(cnf_transformation,[],[f39])).
% 1.89/0.61  fof(f39,plain,(
% 1.89/0.61    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.89/0.61    inference(flattening,[],[f38])).
% 1.89/0.61  fof(f38,plain,(
% 1.89/0.61    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.89/0.61    inference(nnf_transformation,[],[f1])).
% 1.89/0.61  fof(f1,axiom,(
% 1.89/0.61    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.89/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.89/0.61  fof(f1209,plain,(
% 1.89/0.61    v5_relat_1(k6_relat_1(sK1),k2_relat_1(sK2)) | ~spl4_68),
% 1.89/0.61    inference(avatar_component_clause,[],[f1207])).
% 1.89/0.61  fof(f1207,plain,(
% 1.89/0.61    spl4_68 <=> v5_relat_1(k6_relat_1(sK1),k2_relat_1(sK2))),
% 1.89/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_68])])).
% 1.89/0.61  fof(f1210,plain,(
% 1.89/0.61    spl4_68 | ~spl4_6 | ~spl4_9 | ~spl4_46),
% 1.89/0.61    inference(avatar_split_clause,[],[f1202,f740,f119,f97,f1207])).
% 1.89/0.61  fof(f97,plain,(
% 1.89/0.61    spl4_6 <=> v1_funct_1(sK2)),
% 1.89/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.89/0.61  fof(f740,plain,(
% 1.89/0.61    spl4_46 <=> ! [X5,X6] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) | v5_relat_1(k6_relat_1(sK1),X6))),
% 1.89/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).
% 1.89/0.61  fof(f1202,plain,(
% 1.89/0.61    v5_relat_1(k6_relat_1(sK1),k2_relat_1(sK2)) | (~spl4_6 | ~spl4_9 | ~spl4_46)),
% 1.89/0.61    inference(resolution,[],[f1177,f68])).
% 1.89/0.61  fof(f68,plain,(
% 1.89/0.61    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.89/0.61    inference(equality_resolution,[],[f51])).
% 1.89/0.61  fof(f51,plain,(
% 1.89/0.61    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.89/0.61    inference(cnf_transformation,[],[f39])).
% 1.89/0.61  fof(f1177,plain,(
% 1.89/0.61    ( ! [X0] : (~r1_tarski(k2_relat_1(sK2),X0) | v5_relat_1(k6_relat_1(sK1),X0)) ) | (~spl4_6 | ~spl4_9 | ~spl4_46)),
% 1.89/0.61    inference(subsumption_resolution,[],[f1176,f121])).
% 1.89/0.61  fof(f1176,plain,(
% 1.89/0.61    ( ! [X0] : (v5_relat_1(k6_relat_1(sK1),X0) | ~r1_tarski(k2_relat_1(sK2),X0) | ~v1_relat_1(sK2)) ) | (~spl4_6 | ~spl4_46)),
% 1.89/0.61    inference(subsumption_resolution,[],[f1175,f99])).
% 1.89/0.61  fof(f99,plain,(
% 1.89/0.61    v1_funct_1(sK2) | ~spl4_6),
% 1.89/0.61    inference(avatar_component_clause,[],[f97])).
% 1.89/0.61  fof(f1175,plain,(
% 1.89/0.61    ( ! [X0] : (v5_relat_1(k6_relat_1(sK1),X0) | ~r1_tarski(k2_relat_1(sK2),X0) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) ) | ~spl4_46),
% 1.89/0.61    inference(resolution,[],[f741,f61])).
% 1.89/0.61  fof(f61,plain,(
% 1.89/0.61    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.89/0.61    inference(cnf_transformation,[],[f30])).
% 1.89/0.61  fof(f30,plain,(
% 1.89/0.61    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.89/0.61    inference(flattening,[],[f29])).
% 1.89/0.61  fof(f29,plain,(
% 1.89/0.61    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.89/0.61    inference(ennf_transformation,[],[f17])).
% 1.89/0.61  fof(f17,plain,(
% 1.89/0.61    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_1(X1))))),
% 1.89/0.61    inference(pure_predicate_removal,[],[f13])).
% 1.89/0.61  fof(f13,axiom,(
% 1.89/0.61    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 1.89/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).
% 1.89/0.61  fof(f741,plain,(
% 1.89/0.61    ( ! [X6,X5] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) | v5_relat_1(k6_relat_1(sK1),X6)) ) | ~spl4_46),
% 1.89/0.61    inference(avatar_component_clause,[],[f740])).
% 1.89/0.61  fof(f972,plain,(
% 1.89/0.61    spl4_45 | spl4_46 | ~spl4_4 | ~spl4_6 | ~spl4_27),
% 1.89/0.61    inference(avatar_split_clause,[],[f949,f273,f97,f87,f740,f737])).
% 1.89/0.61  fof(f737,plain,(
% 1.89/0.61    spl4_45 <=> ! [X7,X8] : ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))),
% 1.89/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).
% 1.89/0.61  fof(f87,plain,(
% 1.89/0.61    spl4_4 <=> v1_funct_1(sK3)),
% 1.89/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.89/0.61  fof(f273,plain,(
% 1.89/0.61    spl4_27 <=> k6_relat_1(sK1) = k5_relat_1(sK3,sK2)),
% 1.89/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).
% 1.89/0.62  fof(f949,plain,(
% 1.89/0.62    ( ! [X6,X8,X7,X5] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X7,X8))) | v5_relat_1(k6_relat_1(sK1),X6)) ) | (~spl4_4 | ~spl4_6 | ~spl4_27)),
% 1.89/0.62    inference(resolution,[],[f315,f66])).
% 1.89/0.62  fof(f66,plain,(
% 1.89/0.62    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.89/0.62    inference(cnf_transformation,[],[f33])).
% 1.89/0.62  fof(f33,plain,(
% 1.89/0.62    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.89/0.62    inference(ennf_transformation,[],[f19])).
% 1.89/0.62  fof(f19,plain,(
% 1.89/0.62    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 1.89/0.62    inference(pure_predicate_removal,[],[f6])).
% 1.89/0.62  fof(f6,axiom,(
% 1.89/0.62    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.89/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.89/0.62  fof(f315,plain,(
% 1.89/0.62    ( ! [X2,X0,X3,X1] : (m1_subset_1(k6_relat_1(sK1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))) ) | (~spl4_4 | ~spl4_6 | ~spl4_27)),
% 1.89/0.62    inference(subsumption_resolution,[],[f314,f89])).
% 1.89/0.62  fof(f89,plain,(
% 1.89/0.62    v1_funct_1(sK3) | ~spl4_4),
% 1.89/0.62    inference(avatar_component_clause,[],[f87])).
% 1.89/0.62  fof(f314,plain,(
% 1.89/0.62    ( ! [X2,X0,X3,X1] : (m1_subset_1(k6_relat_1(sK1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~v1_funct_1(sK3)) ) | (~spl4_6 | ~spl4_27)),
% 1.89/0.62    inference(subsumption_resolution,[],[f312,f99])).
% 1.89/0.62  fof(f312,plain,(
% 1.89/0.62    ( ! [X2,X0,X3,X1] : (m1_subset_1(k6_relat_1(sK1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~v1_funct_1(sK3)) ) | ~spl4_27),
% 1.89/0.62    inference(superposition,[],[f191,f275])).
% 1.89/0.62  fof(f275,plain,(
% 1.89/0.62    k6_relat_1(sK1) = k5_relat_1(sK3,sK2) | ~spl4_27),
% 1.89/0.62    inference(avatar_component_clause,[],[f273])).
% 1.89/0.62  fof(f191,plain,(
% 1.89/0.62    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.89/0.62    inference(duplicate_literal_removal,[],[f190])).
% 1.89/0.62  fof(f190,plain,(
% 1.89/0.62    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.89/0.62    inference(superposition,[],[f58,f59])).
% 1.89/0.62  fof(f59,plain,(
% 1.89/0.62    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.89/0.62    inference(cnf_transformation,[],[f28])).
% 1.89/0.62  fof(f28,plain,(
% 1.89/0.62    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.89/0.62    inference(flattening,[],[f27])).
% 1.89/0.62  fof(f27,plain,(
% 1.89/0.62    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.89/0.62    inference(ennf_transformation,[],[f11])).
% 1.89/0.62  fof(f11,axiom,(
% 1.89/0.62    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.89/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 1.89/0.62  fof(f58,plain,(
% 1.89/0.62    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.89/0.62    inference(cnf_transformation,[],[f26])).
% 1.89/0.62  fof(f26,plain,(
% 1.89/0.62    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.89/0.62    inference(flattening,[],[f25])).
% 1.89/0.62  fof(f25,plain,(
% 1.89/0.62    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.89/0.62    inference(ennf_transformation,[],[f9])).
% 1.89/0.62  fof(f9,axiom,(
% 1.89/0.62    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 1.89/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 1.89/0.62  fof(f882,plain,(
% 1.89/0.62    ~spl4_3 | ~spl4_45),
% 1.89/0.62    inference(avatar_contradiction_clause,[],[f877])).
% 1.89/0.62  fof(f877,plain,(
% 1.89/0.62    $false | (~spl4_3 | ~spl4_45)),
% 1.89/0.62    inference(unit_resulting_resolution,[],[f84,f738])).
% 1.89/0.62  fof(f738,plain,(
% 1.89/0.62    ( ! [X8,X7] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))) ) | ~spl4_45),
% 1.89/0.62    inference(avatar_component_clause,[],[f737])).
% 1.89/0.62  fof(f84,plain,(
% 1.89/0.62    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_3),
% 1.89/0.62    inference(avatar_component_clause,[],[f82])).
% 1.89/0.62  fof(f82,plain,(
% 1.89/0.62    spl4_3 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.89/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.89/0.62  fof(f306,plain,(
% 1.89/0.62    ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_6 | spl4_26),
% 1.89/0.62    inference(avatar_contradiction_clause,[],[f296])).
% 1.89/0.62  fof(f296,plain,(
% 1.89/0.62    $false | (~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_6 | spl4_26)),
% 1.89/0.62    inference(unit_resulting_resolution,[],[f89,f99,f84,f94,f271,f191])).
% 1.89/0.62  fof(f271,plain,(
% 1.89/0.62    ~m1_subset_1(k5_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) | spl4_26),
% 1.89/0.62    inference(avatar_component_clause,[],[f269])).
% 1.89/0.62  fof(f269,plain,(
% 1.89/0.62    spl4_26 <=> m1_subset_1(k5_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))),
% 1.89/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 1.89/0.62  fof(f94,plain,(
% 1.89/0.62    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_5),
% 1.89/0.62    inference(avatar_component_clause,[],[f92])).
% 1.89/0.62  fof(f92,plain,(
% 1.89/0.62    spl4_5 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.89/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.89/0.62  fof(f276,plain,(
% 1.89/0.62    ~spl4_26 | spl4_27 | ~spl4_15),
% 1.89/0.62    inference(avatar_split_clause,[],[f258,f182,f273,f269])).
% 1.89/0.62  fof(f182,plain,(
% 1.89/0.62    spl4_15 <=> r2_relset_1(sK1,sK1,k5_relat_1(sK3,sK2),k6_relat_1(sK1))),
% 1.89/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 1.89/0.62  fof(f258,plain,(
% 1.89/0.62    k6_relat_1(sK1) = k5_relat_1(sK3,sK2) | ~m1_subset_1(k5_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) | ~spl4_15),
% 1.89/0.62    inference(resolution,[],[f171,f184])).
% 1.89/0.62  fof(f184,plain,(
% 1.89/0.62    r2_relset_1(sK1,sK1,k5_relat_1(sK3,sK2),k6_relat_1(sK1)) | ~spl4_15),
% 1.89/0.62    inference(avatar_component_clause,[],[f182])).
% 1.89/0.62  fof(f171,plain,(
% 1.89/0.62    ( ! [X4,X3] : (~r2_relset_1(X3,X3,X4,k6_relat_1(X3)) | k6_relat_1(X3) = X4 | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X3)))) )),
% 1.89/0.62    inference(resolution,[],[f47,f107])).
% 1.89/0.62  fof(f47,plain,(
% 1.89/0.62    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.89/0.62    inference(cnf_transformation,[],[f37])).
% 1.89/0.62  fof(f37,plain,(
% 1.89/0.62    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.89/0.62    inference(nnf_transformation,[],[f23])).
% 1.89/0.62  fof(f23,plain,(
% 1.89/0.62    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.89/0.62    inference(flattening,[],[f22])).
% 1.89/0.62  fof(f22,plain,(
% 1.89/0.62    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.89/0.62    inference(ennf_transformation,[],[f8])).
% 1.89/0.62  fof(f8,axiom,(
% 1.89/0.62    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.89/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.89/0.62  fof(f185,plain,(
% 1.89/0.62    spl4_15 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_6 | ~spl4_7),
% 1.89/0.62    inference(avatar_split_clause,[],[f180,f103,f97,f92,f87,f82,f182])).
% 1.89/0.62  fof(f103,plain,(
% 1.89/0.62    spl4_7 <=> r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2),k6_relat_1(sK1))),
% 1.89/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 1.89/0.62  fof(f180,plain,(
% 1.89/0.62    r2_relset_1(sK1,sK1,k5_relat_1(sK3,sK2),k6_relat_1(sK1)) | (~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_6 | ~spl4_7)),
% 1.89/0.62    inference(subsumption_resolution,[],[f179,f89])).
% 1.89/0.62  fof(f179,plain,(
% 1.89/0.62    r2_relset_1(sK1,sK1,k5_relat_1(sK3,sK2),k6_relat_1(sK1)) | ~v1_funct_1(sK3) | (~spl4_3 | ~spl4_5 | ~spl4_6 | ~spl4_7)),
% 1.89/0.62    inference(subsumption_resolution,[],[f178,f84])).
% 1.89/0.62  fof(f178,plain,(
% 1.89/0.62    r2_relset_1(sK1,sK1,k5_relat_1(sK3,sK2),k6_relat_1(sK1)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | (~spl4_5 | ~spl4_6 | ~spl4_7)),
% 1.89/0.62    inference(subsumption_resolution,[],[f177,f99])).
% 1.89/0.62  fof(f177,plain,(
% 1.89/0.62    r2_relset_1(sK1,sK1,k5_relat_1(sK3,sK2),k6_relat_1(sK1)) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | (~spl4_5 | ~spl4_7)),
% 1.89/0.62    inference(subsumption_resolution,[],[f174,f94])).
% 1.89/0.62  fof(f174,plain,(
% 1.89/0.62    r2_relset_1(sK1,sK1,k5_relat_1(sK3,sK2),k6_relat_1(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~spl4_7),
% 1.89/0.62    inference(superposition,[],[f105,f59])).
% 1.89/0.62  fof(f105,plain,(
% 1.89/0.62    r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2),k6_relat_1(sK1)) | ~spl4_7),
% 1.89/0.62    inference(avatar_component_clause,[],[f103])).
% 1.89/0.62  fof(f163,plain,(
% 1.89/0.62    ~spl4_14 | spl4_1 | ~spl4_5),
% 1.89/0.62    inference(avatar_split_clause,[],[f158,f92,f72,f160])).
% 1.89/0.62  fof(f72,plain,(
% 1.89/0.62    spl4_1 <=> sK1 = k2_relset_1(sK0,sK1,sK2)),
% 1.89/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.89/0.62  fof(f158,plain,(
% 1.89/0.62    sK1 != k2_relat_1(sK2) | (spl4_1 | ~spl4_5)),
% 1.89/0.62    inference(subsumption_resolution,[],[f157,f94])).
% 1.89/0.62  fof(f157,plain,(
% 1.89/0.62    sK1 != k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl4_1),
% 1.89/0.62    inference(superposition,[],[f74,f49])).
% 1.89/0.62  fof(f49,plain,(
% 1.89/0.62    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.89/0.62    inference(cnf_transformation,[],[f24])).
% 1.89/0.62  fof(f24,plain,(
% 1.89/0.62    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.89/0.62    inference(ennf_transformation,[],[f7])).
% 1.89/0.62  fof(f7,axiom,(
% 1.89/0.62    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.89/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.89/0.62  fof(f74,plain,(
% 1.89/0.62    sK1 != k2_relset_1(sK0,sK1,sK2) | spl4_1),
% 1.89/0.62    inference(avatar_component_clause,[],[f72])).
% 1.89/0.62  fof(f143,plain,(
% 1.89/0.62    spl4_11 | ~spl4_5),
% 1.89/0.62    inference(avatar_split_clause,[],[f132,f92,f140])).
% 1.89/0.62  fof(f132,plain,(
% 1.89/0.62    v5_relat_1(sK2,sK1) | ~spl4_5),
% 1.89/0.62    inference(resolution,[],[f66,f94])).
% 1.89/0.62  fof(f122,plain,(
% 1.89/0.62    spl4_9 | ~spl4_5),
% 1.89/0.62    inference(avatar_split_clause,[],[f117,f92,f119])).
% 1.89/0.62  fof(f117,plain,(
% 1.89/0.62    v1_relat_1(sK2) | ~spl4_5),
% 1.89/0.62    inference(subsumption_resolution,[],[f109,f63])).
% 1.89/0.62  fof(f109,plain,(
% 1.89/0.62    v1_relat_1(sK2) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | ~spl4_5),
% 1.89/0.62    inference(resolution,[],[f62,f94])).
% 1.89/0.62  fof(f106,plain,(
% 1.89/0.62    spl4_7 | ~spl4_2),
% 1.89/0.62    inference(avatar_split_clause,[],[f101,f77,f103])).
% 1.89/0.62  fof(f77,plain,(
% 1.89/0.62    spl4_2 <=> r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2),k6_partfun1(sK1))),
% 1.89/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.89/0.62  fof(f101,plain,(
% 1.89/0.62    r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2),k6_relat_1(sK1)) | ~spl4_2),
% 1.89/0.62    inference(backward_demodulation,[],[f79,f55])).
% 1.89/0.62  fof(f79,plain,(
% 1.89/0.62    r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2),k6_partfun1(sK1)) | ~spl4_2),
% 1.89/0.62    inference(avatar_component_clause,[],[f77])).
% 1.89/0.62  fof(f100,plain,(
% 1.89/0.62    spl4_6),
% 1.89/0.62    inference(avatar_split_clause,[],[f41,f97])).
% 1.89/0.62  fof(f41,plain,(
% 1.89/0.62    v1_funct_1(sK2)),
% 1.89/0.62    inference(cnf_transformation,[],[f36])).
% 1.89/0.62  fof(f36,plain,(
% 1.89/0.62    (sK1 != k2_relset_1(sK0,sK1,sK2) & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2),k6_partfun1(sK1)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK2)),
% 1.89/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f21,f35,f34])).
% 1.89/0.62  fof(f34,plain,(
% 1.89/0.62    ? [X0,X1,X2] : (? [X3] : (k2_relset_1(X0,X1,X2) != X1 & r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (? [X3] : (sK1 != k2_relset_1(sK0,sK1,sK2) & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK0,sK0,sK1,X3,sK2),k6_partfun1(sK1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK2))),
% 1.89/0.62    introduced(choice_axiom,[])).
% 1.89/0.62  fof(f35,plain,(
% 1.89/0.62    ? [X3] : (sK1 != k2_relset_1(sK0,sK1,sK2) & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK0,sK0,sK1,X3,sK2),k6_partfun1(sK1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_1(X3)) => (sK1 != k2_relset_1(sK0,sK1,sK2) & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2),k6_partfun1(sK1)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_1(sK3))),
% 1.89/0.62    introduced(choice_axiom,[])).
% 1.89/0.62  fof(f21,plain,(
% 1.89/0.62    ? [X0,X1,X2] : (? [X3] : (k2_relset_1(X0,X1,X2) != X1 & r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 1.89/0.62    inference(flattening,[],[f20])).
% 1.89/0.62  fof(f20,plain,(
% 1.89/0.62    ? [X0,X1,X2] : (? [X3] : ((k2_relset_1(X0,X1,X2) != X1 & r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)))),
% 1.89/0.62    inference(ennf_transformation,[],[f16])).
% 1.89/0.62  fof(f16,plain,(
% 1.89/0.62    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 1.89/0.62    inference(pure_predicate_removal,[],[f15])).
% 1.89/0.62  fof(f15,negated_conjecture,(
% 1.89/0.62    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 1.89/0.62    inference(negated_conjecture,[],[f14])).
% 1.89/0.62  fof(f14,conjecture,(
% 1.89/0.62    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 1.89/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_funct_2)).
% 1.89/0.62  fof(f95,plain,(
% 1.89/0.62    spl4_5),
% 1.89/0.62    inference(avatar_split_clause,[],[f42,f92])).
% 1.89/0.62  fof(f42,plain,(
% 1.89/0.62    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.89/0.62    inference(cnf_transformation,[],[f36])).
% 1.89/0.62  fof(f90,plain,(
% 1.89/0.62    spl4_4),
% 1.89/0.62    inference(avatar_split_clause,[],[f43,f87])).
% 1.89/0.62  fof(f43,plain,(
% 1.89/0.62    v1_funct_1(sK3)),
% 1.89/0.62    inference(cnf_transformation,[],[f36])).
% 1.89/0.62  fof(f85,plain,(
% 1.89/0.62    spl4_3),
% 1.89/0.62    inference(avatar_split_clause,[],[f44,f82])).
% 1.89/0.62  fof(f44,plain,(
% 1.89/0.62    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.89/0.62    inference(cnf_transformation,[],[f36])).
% 1.89/0.62  fof(f80,plain,(
% 1.89/0.62    spl4_2),
% 1.89/0.62    inference(avatar_split_clause,[],[f45,f77])).
% 1.89/0.62  fof(f45,plain,(
% 1.89/0.62    r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2),k6_partfun1(sK1))),
% 1.89/0.62    inference(cnf_transformation,[],[f36])).
% 1.89/0.62  fof(f75,plain,(
% 1.89/0.62    ~spl4_1),
% 1.89/0.62    inference(avatar_split_clause,[],[f46,f72])).
% 1.89/0.62  fof(f46,plain,(
% 1.89/0.62    sK1 != k2_relset_1(sK0,sK1,sK2)),
% 1.89/0.62    inference(cnf_transformation,[],[f36])).
% 1.89/0.62  % SZS output end Proof for theBenchmark
% 1.89/0.62  % (10432)------------------------------
% 1.89/0.62  % (10432)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.89/0.62  % (10432)Termination reason: Refutation
% 1.89/0.62  
% 1.89/0.62  % (10432)Memory used [KB]: 7547
% 1.89/0.62  % (10432)Time elapsed: 0.169 s
% 1.89/0.62  % (10432)------------------------------
% 1.89/0.62  % (10432)------------------------------
% 1.89/0.62  % (10410)Success in time 0.26 s
%------------------------------------------------------------------------------
