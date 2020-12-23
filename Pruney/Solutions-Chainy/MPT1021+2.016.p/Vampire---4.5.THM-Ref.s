%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:52 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  197 ( 436 expanded)
%              Number of leaves         :   42 ( 173 expanded)
%              Depth                    :   15
%              Number of atoms          :  714 (1434 expanded)
%              Number of equality atoms :  126 ( 201 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f689,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f123,f128,f133,f138,f143,f196,f233,f250,f274,f289,f294,f299,f326,f349,f398,f445,f450,f486,f500,f509,f672,f688])).

fof(f688,plain,
    ( ~ spl2_28
    | spl2_31
    | ~ spl2_32 ),
    inference(avatar_contradiction_clause,[],[f687])).

fof(f687,plain,
    ( $false
    | ~ spl2_28
    | spl2_31
    | ~ spl2_32 ),
    inference(subsumption_resolution,[],[f685,f200])).

fof(f200,plain,(
    ! [X0] : r2_relset_1(X0,X0,k6_partfun1(X0),k6_partfun1(X0)) ),
    inference(unit_resulting_resolution,[],[f62,f114])).

fof(f114,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f113])).

fof(f113,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f96])).

fof(f96,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f62,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f685,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0))
    | ~ spl2_28
    | spl2_31
    | ~ spl2_32 ),
    inference(backward_demodulation,[],[f499,f682])).

fof(f682,plain,
    ( sK0 = k1_relat_1(sK1)
    | ~ spl2_28
    | ~ spl2_32 ),
    inference(backward_demodulation,[],[f444,f504])).

fof(f504,plain,
    ( sK0 = k1_relset_1(sK0,sK0,sK1)
    | ~ spl2_32 ),
    inference(avatar_component_clause,[],[f502])).

fof(f502,plain,
    ( spl2_32
  <=> sK0 = k1_relset_1(sK0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).

fof(f444,plain,
    ( k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1)
    | ~ spl2_28 ),
    inference(avatar_component_clause,[],[f442])).

fof(f442,plain,
    ( spl2_28
  <=> k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).

fof(f499,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_partfun1(k1_relat_1(sK1)),k6_partfun1(sK0))
    | spl2_31 ),
    inference(avatar_component_clause,[],[f497])).

fof(f497,plain,
    ( spl2_31
  <=> r2_relset_1(sK0,sK0,k6_partfun1(k1_relat_1(sK1)),k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).

fof(f672,plain,
    ( ~ spl2_5
    | ~ spl2_19
    | ~ spl2_27
    | spl2_31
    | ~ spl2_33 ),
    inference(avatar_contradiction_clause,[],[f671])).

fof(f671,plain,
    ( $false
    | ~ spl2_5
    | ~ spl2_19
    | ~ spl2_27
    | spl2_31
    | ~ spl2_33 ),
    inference(subsumption_resolution,[],[f670,f404])).

fof(f404,plain,(
    ! [X0,X1] : r2_relset_1(X0,X1,k1_xboole_0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f162,f114])).

fof(f162,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f59,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f59,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f670,plain,
    ( ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl2_5
    | ~ spl2_19
    | ~ spl2_27
    | spl2_31
    | ~ spl2_33 ),
    inference(forward_demodulation,[],[f669,f142])).

fof(f142,plain,
    ( k1_xboole_0 = k6_partfun1(k1_xboole_0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f140])).

fof(f140,plain,
    ( spl2_5
  <=> k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f669,plain,
    ( ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),k1_xboole_0)
    | ~ spl2_5
    | ~ spl2_19
    | ~ spl2_27
    | spl2_31
    | ~ spl2_33 ),
    inference(forward_demodulation,[],[f668,f397])).

fof(f397,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl2_27 ),
    inference(avatar_component_clause,[],[f395])).

fof(f395,plain,
    ( spl2_27
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).

fof(f668,plain,
    ( ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_relat_1(k1_xboole_0)),k1_xboole_0)
    | ~ spl2_5
    | ~ spl2_19
    | spl2_31
    | ~ spl2_33 ),
    inference(forward_demodulation,[],[f667,f564])).

fof(f564,plain,
    ( k1_xboole_0 = sK1
    | ~ spl2_19
    | ~ spl2_33 ),
    inference(subsumption_resolution,[],[f563,f59])).

fof(f563,plain,
    ( ~ r1_tarski(k1_xboole_0,sK1)
    | k1_xboole_0 = sK1
    | ~ spl2_19
    | ~ spl2_33 ),
    inference(forward_demodulation,[],[f562,f106])).

fof(f106,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f562,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),sK1)
    | k1_xboole_0 = sK1
    | ~ spl2_19
    | ~ spl2_33 ),
    inference(forward_demodulation,[],[f561,f508])).

fof(f508,plain,
    ( k1_xboole_0 = sK0
    | ~ spl2_33 ),
    inference(avatar_component_clause,[],[f506])).

fof(f506,plain,
    ( spl2_33
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_33])])).

fof(f561,plain,
    ( k1_xboole_0 = sK1
    | ~ r1_tarski(k2_zfmisc_1(sK0,sK0),sK1)
    | ~ spl2_19
    | ~ spl2_33 ),
    inference(forward_demodulation,[],[f536,f106])).

fof(f536,plain,
    ( sK1 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
    | ~ r1_tarski(k2_zfmisc_1(sK0,sK0),sK1)
    | ~ spl2_19
    | ~ spl2_33 ),
    inference(backward_demodulation,[],[f371,f508])).

fof(f371,plain,
    ( sK1 = k2_zfmisc_1(sK0,sK0)
    | ~ r1_tarski(k2_zfmisc_1(sK0,sK0),sK1)
    | ~ spl2_19 ),
    inference(resolution,[],[f348,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
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

fof(f348,plain,
    ( r1_tarski(sK1,k2_zfmisc_1(sK0,sK0))
    | ~ spl2_19 ),
    inference(avatar_component_clause,[],[f346])).

fof(f346,plain,
    ( spl2_19
  <=> r1_tarski(sK1,k2_zfmisc_1(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f667,plain,
    ( ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_relat_1(sK1)),k1_xboole_0)
    | ~ spl2_5
    | spl2_31
    | ~ spl2_33 ),
    inference(forward_demodulation,[],[f555,f142])).

fof(f555,plain,
    ( ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_relat_1(sK1)),k6_partfun1(k1_xboole_0))
    | spl2_31
    | ~ spl2_33 ),
    inference(backward_demodulation,[],[f499,f508])).

fof(f509,plain,
    ( spl2_32
    | spl2_33
    | ~ spl2_2
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f261,f135,f125,f506,f502])).

fof(f125,plain,
    ( spl2_2
  <=> v1_funct_2(sK1,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f135,plain,
    ( spl2_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f261,plain,
    ( k1_xboole_0 = sK0
    | sK0 = k1_relset_1(sK0,sK0,sK1)
    | ~ spl2_2
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f256,f127])).

fof(f127,plain,
    ( v1_funct_2(sK1,sK0,sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f125])).

fof(f256,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | k1_xboole_0 = sK0
    | sK0 = k1_relset_1(sK0,sK0,sK1)
    | ~ spl2_4 ),
    inference(resolution,[],[f86,f137])).

fof(f137,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f135])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f500,plain,
    ( ~ spl2_31
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_7
    | ~ spl2_10
    | spl2_15
    | ~ spl2_18
    | ~ spl2_29 ),
    inference(avatar_split_clause,[],[f482,f447,f323,f286,f230,f193,f135,f120,f497])).

fof(f120,plain,
    ( spl2_1
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f193,plain,
    ( spl2_7
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f230,plain,
    ( spl2_10
  <=> v2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f286,plain,
    ( spl2_15
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f323,plain,
    ( spl2_18
  <=> v1_funct_1(k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f447,plain,
    ( spl2_29
  <=> m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).

fof(f482,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_partfun1(k1_relat_1(sK1)),k6_partfun1(sK0))
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_7
    | ~ spl2_10
    | spl2_15
    | ~ spl2_18
    | ~ spl2_29 ),
    inference(backward_demodulation,[],[f288,f481])).

fof(f481,plain,
    ( k6_partfun1(k1_relat_1(sK1)) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1))
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_7
    | ~ spl2_10
    | ~ spl2_18
    | ~ spl2_29 ),
    inference(forward_demodulation,[],[f459,f235])).

fof(f235,plain,
    ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1))
    | ~ spl2_1
    | ~ spl2_7
    | ~ spl2_10 ),
    inference(unit_resulting_resolution,[],[f195,f122,f232,f102])).

fof(f102,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f65,f60])).

fof(f60,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f65,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

fof(f232,plain,
    ( v2_funct_1(sK1)
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f230])).

fof(f122,plain,
    ( v1_funct_1(sK1)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f120])).

fof(f195,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f193])).

fof(f459,plain,
    ( k5_relat_1(sK1,k2_funct_1(sK1)) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1))
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_18
    | ~ spl2_29 ),
    inference(unit_resulting_resolution,[],[f122,f137,f325,f449,f97])).

fof(f97,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f449,plain,
    ( m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl2_29 ),
    inference(avatar_component_clause,[],[f447])).

fof(f325,plain,
    ( v1_funct_1(k2_funct_1(sK1))
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f323])).

fof(f288,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0))
    | spl2_15 ),
    inference(avatar_component_clause,[],[f286])).

fof(f486,plain,
    ( ~ spl2_1
    | ~ spl2_4
    | ~ spl2_7
    | ~ spl2_10
    | ~ spl2_14
    | spl2_16
    | ~ spl2_17
    | ~ spl2_18
    | ~ spl2_29 ),
    inference(avatar_contradiction_clause,[],[f485])).

fof(f485,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_7
    | ~ spl2_10
    | ~ spl2_14
    | spl2_16
    | ~ spl2_17
    | ~ spl2_18
    | ~ spl2_29 ),
    inference(subsumption_resolution,[],[f484,f200])).

fof(f484,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0))
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_7
    | ~ spl2_10
    | ~ spl2_14
    | spl2_16
    | ~ spl2_17
    | ~ spl2_18
    | ~ spl2_29 ),
    inference(backward_demodulation,[],[f293,f483])).

fof(f483,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1)
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_7
    | ~ spl2_10
    | ~ spl2_14
    | ~ spl2_17
    | ~ spl2_18
    | ~ spl2_29 ),
    inference(forward_demodulation,[],[f457,f328])).

fof(f328,plain,
    ( k6_partfun1(sK0) = k5_relat_1(k2_funct_1(sK1),sK1)
    | ~ spl2_1
    | ~ spl2_7
    | ~ spl2_10
    | ~ spl2_14
    | ~ spl2_17 ),
    inference(backward_demodulation,[],[f236,f327])).

fof(f327,plain,
    ( sK0 = k2_relat_1(sK1)
    | ~ spl2_7
    | ~ spl2_14
    | ~ spl2_17 ),
    inference(unit_resulting_resolution,[],[f195,f273,f298,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | k2_relat_1(X1) = X0 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

fof(f298,plain,
    ( v2_funct_2(sK1,sK0)
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f296])).

fof(f296,plain,
    ( spl2_17
  <=> v2_funct_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f273,plain,
    ( v5_relat_1(sK1,sK0)
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f271])).

fof(f271,plain,
    ( spl2_14
  <=> v5_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f236,plain,
    ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(k2_relat_1(sK1))
    | ~ spl2_1
    | ~ spl2_7
    | ~ spl2_10 ),
    inference(unit_resulting_resolution,[],[f195,f122,f232,f101])).

fof(f101,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f66,f60])).

fof(f66,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f457,plain,
    ( k5_relat_1(k2_funct_1(sK1),sK1) = k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1)
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_18
    | ~ spl2_29 ),
    inference(unit_resulting_resolution,[],[f122,f325,f137,f449,f97])).

fof(f293,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0))
    | spl2_16 ),
    inference(avatar_component_clause,[],[f291])).

fof(f291,plain,
    ( spl2_16
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f450,plain,
    ( spl2_29
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f318,f135,f130,f125,f120,f447])).

fof(f130,plain,
    ( spl2_3
  <=> v3_funct_2(sK1,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f318,plain,
    ( m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(forward_demodulation,[],[f306,f280])).

fof(f280,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(unit_resulting_resolution,[],[f122,f127,f132,f137,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | k2_funct_2(X0,X1) = k2_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_2(X0,X1) = k2_funct_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

fof(f132,plain,
    ( v3_funct_2(sK1,sK0,sK0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f130])).

fof(f306,plain,
    ( m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(unit_resulting_resolution,[],[f122,f127,f132,f137,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_2)).

fof(f445,plain,
    ( spl2_28
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f218,f135,f442])).

fof(f218,plain,
    ( k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1)
    | ~ spl2_4 ),
    inference(unit_resulting_resolution,[],[f137,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f398,plain,
    ( spl2_27
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f146,f140,f395])).

fof(f146,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl2_5 ),
    inference(superposition,[],[f100,f142])).

fof(f100,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f63,f60])).

fof(f63,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f349,plain,
    ( spl2_19
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f158,f135,f346])).

fof(f158,plain,
    ( r1_tarski(sK1,k2_zfmisc_1(sK0,sK0))
    | ~ spl2_4 ),
    inference(unit_resulting_resolution,[],[f137,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f326,plain,
    ( spl2_18
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f282,f135,f130,f125,f120,f323])).

fof(f282,plain,
    ( v1_funct_1(k2_funct_1(sK1))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(backward_demodulation,[],[f268,f280])).

fof(f268,plain,
    ( v1_funct_1(k2_funct_2(sK0,sK1))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(unit_resulting_resolution,[],[f122,f127,f132,f137,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | v1_funct_1(k2_funct_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f299,plain,
    ( spl2_17
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f240,f135,f130,f120,f296])).

fof(f240,plain,
    ( v2_funct_2(sK1,sK0)
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(unit_resulting_resolution,[],[f122,f132,f137,f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v3_funct_2(X2,X0,X1)
      | v2_funct_2(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

fof(f294,plain,
    ( ~ spl2_16
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4
    | spl2_12 ),
    inference(avatar_split_clause,[],[f284,f247,f135,f130,f125,f120,f291])).

fof(f247,plain,
    ( spl2_12
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f284,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4
    | spl2_12 ),
    inference(backward_demodulation,[],[f249,f280])).

fof(f249,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
    | spl2_12 ),
    inference(avatar_component_clause,[],[f247])).

fof(f289,plain,
    ( ~ spl2_15
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4
    | spl2_11 ),
    inference(avatar_split_clause,[],[f283,f243,f135,f130,f125,f120,f286])).

fof(f243,plain,
    ( spl2_11
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f283,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4
    | spl2_11 ),
    inference(backward_demodulation,[],[f245,f280])).

fof(f245,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))
    | spl2_11 ),
    inference(avatar_component_clause,[],[f243])).

fof(f274,plain,
    ( spl2_14
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f185,f135,f271])).

fof(f185,plain,
    ( v5_relat_1(sK1,sK0)
    | ~ spl2_4 ),
    inference(unit_resulting_resolution,[],[f137,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f250,plain,
    ( ~ spl2_11
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f57,f247,f243])).

fof(f57,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,
    ( ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) )
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v3_funct_2(sK1,sK0,sK0)
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f43])).

fof(f43,plain,
    ( ? [X0,X1] :
        ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
        | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v3_funct_2(sK1,sK0,sK0)
      & v1_funct_2(sK1,sK0,sK0)
      & v1_funct_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X1,X0,X0)
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_funct_2)).

fof(f233,plain,
    ( spl2_10
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f227,f135,f130,f120,f230])).

fof(f227,plain,
    ( v2_funct_1(sK1)
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(unit_resulting_resolution,[],[f122,f132,f137,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v3_funct_2(X2,X0,X1)
      | v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f196,plain,
    ( spl2_7
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f165,f135,f193])).

fof(f165,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_4 ),
    inference(unit_resulting_resolution,[],[f137,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f143,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f98,f140])).

fof(f98,plain,(
    k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    inference(definition_unfolding,[],[f58,f60])).

fof(f58,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

fof(f138,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f56,f135])).

fof(f56,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f44])).

fof(f133,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f55,f130])).

fof(f55,plain,(
    v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f128,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f54,f125])).

fof(f54,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f123,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f53,f120])).

fof(f53,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f44])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:55:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.52  % (31851)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.52  % (31852)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.52  % (31854)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.52  % (31856)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (31853)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.53  % (31855)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.53  % (31874)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.54  % (31850)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.54  % (31875)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.54  % (31879)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.54  % (31877)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.54  % (31873)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.54  % (31878)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.54  % (31876)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (31858)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.54  % (31872)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.54  % (31865)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.55  % (31869)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.55  % (31868)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.55  % (31866)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.55  % (31860)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.55  % (31866)Refutation not found, incomplete strategy% (31866)------------------------------
% 0.21/0.55  % (31866)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (31866)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (31866)Memory used [KB]: 10746
% 0.21/0.55  % (31866)Time elapsed: 0.139 s
% 0.21/0.55  % (31866)------------------------------
% 0.21/0.55  % (31866)------------------------------
% 0.21/0.55  % (31863)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.55  % (31870)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.55  % (31871)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.56  % (31864)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.56  % (31859)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.56  % (31867)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.56  % (31862)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.56  % (31861)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.57  % (31857)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.61  % (31870)Refutation found. Thanks to Tanya!
% 0.21/0.61  % SZS status Theorem for theBenchmark
% 0.21/0.61  % SZS output start Proof for theBenchmark
% 0.21/0.61  fof(f689,plain,(
% 0.21/0.61    $false),
% 0.21/0.61    inference(avatar_sat_refutation,[],[f123,f128,f133,f138,f143,f196,f233,f250,f274,f289,f294,f299,f326,f349,f398,f445,f450,f486,f500,f509,f672,f688])).
% 0.21/0.61  fof(f688,plain,(
% 0.21/0.61    ~spl2_28 | spl2_31 | ~spl2_32),
% 0.21/0.61    inference(avatar_contradiction_clause,[],[f687])).
% 0.21/0.61  fof(f687,plain,(
% 0.21/0.61    $false | (~spl2_28 | spl2_31 | ~spl2_32)),
% 0.21/0.61    inference(subsumption_resolution,[],[f685,f200])).
% 0.21/0.61  fof(f200,plain,(
% 0.21/0.61    ( ! [X0] : (r2_relset_1(X0,X0,k6_partfun1(X0),k6_partfun1(X0))) )),
% 0.21/0.61    inference(unit_resulting_resolution,[],[f62,f114])).
% 0.21/0.61  fof(f114,plain,(
% 0.21/0.61    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 0.21/0.61    inference(duplicate_literal_removal,[],[f113])).
% 0.21/0.61  fof(f113,plain,(
% 0.21/0.61    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.61    inference(equality_resolution,[],[f96])).
% 0.21/0.61  fof(f96,plain,(
% 0.21/0.61    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.61    inference(cnf_transformation,[],[f52])).
% 0.21/0.61  fof(f52,plain,(
% 0.21/0.61    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.61    inference(nnf_transformation,[],[f40])).
% 0.21/0.61  fof(f40,plain,(
% 0.21/0.61    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.61    inference(flattening,[],[f39])).
% 0.21/0.61  fof(f39,plain,(
% 0.21/0.61    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.21/0.61    inference(ennf_transformation,[],[f11])).
% 0.21/0.61  fof(f11,axiom,(
% 0.21/0.61    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 0.21/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 0.21/0.61  fof(f62,plain,(
% 0.21/0.61    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.21/0.61    inference(cnf_transformation,[],[f16])).
% 0.21/0.61  fof(f16,axiom,(
% 0.21/0.61    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 0.21/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 0.21/0.61  fof(f685,plain,(
% 0.21/0.61    ~r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) | (~spl2_28 | spl2_31 | ~spl2_32)),
% 0.21/0.61    inference(backward_demodulation,[],[f499,f682])).
% 0.21/0.61  fof(f682,plain,(
% 0.21/0.61    sK0 = k1_relat_1(sK1) | (~spl2_28 | ~spl2_32)),
% 0.21/0.61    inference(backward_demodulation,[],[f444,f504])).
% 0.21/0.61  fof(f504,plain,(
% 0.21/0.61    sK0 = k1_relset_1(sK0,sK0,sK1) | ~spl2_32),
% 0.21/0.61    inference(avatar_component_clause,[],[f502])).
% 0.21/0.61  fof(f502,plain,(
% 0.21/0.61    spl2_32 <=> sK0 = k1_relset_1(sK0,sK0,sK1)),
% 0.21/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).
% 0.21/0.61  fof(f444,plain,(
% 0.21/0.61    k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1) | ~spl2_28),
% 0.21/0.61    inference(avatar_component_clause,[],[f442])).
% 0.21/0.61  fof(f442,plain,(
% 0.21/0.61    spl2_28 <=> k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1)),
% 0.21/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).
% 0.21/0.61  fof(f499,plain,(
% 0.21/0.61    ~r2_relset_1(sK0,sK0,k6_partfun1(k1_relat_1(sK1)),k6_partfun1(sK0)) | spl2_31),
% 0.21/0.61    inference(avatar_component_clause,[],[f497])).
% 0.21/0.61  fof(f497,plain,(
% 0.21/0.61    spl2_31 <=> r2_relset_1(sK0,sK0,k6_partfun1(k1_relat_1(sK1)),k6_partfun1(sK0))),
% 0.21/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).
% 0.21/0.61  fof(f672,plain,(
% 0.21/0.61    ~spl2_5 | ~spl2_19 | ~spl2_27 | spl2_31 | ~spl2_33),
% 0.21/0.61    inference(avatar_contradiction_clause,[],[f671])).
% 0.21/0.61  fof(f671,plain,(
% 0.21/0.61    $false | (~spl2_5 | ~spl2_19 | ~spl2_27 | spl2_31 | ~spl2_33)),
% 0.21/0.61    inference(subsumption_resolution,[],[f670,f404])).
% 0.21/0.61  fof(f404,plain,(
% 0.21/0.61    ( ! [X0,X1] : (r2_relset_1(X0,X1,k1_xboole_0,k1_xboole_0)) )),
% 0.21/0.61    inference(unit_resulting_resolution,[],[f162,f114])).
% 0.21/0.61  fof(f162,plain,(
% 0.21/0.61    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.21/0.61    inference(unit_resulting_resolution,[],[f59,f78])).
% 0.21/0.61  fof(f78,plain,(
% 0.21/0.61    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.61    inference(cnf_transformation,[],[f48])).
% 0.21/0.61  fof(f48,plain,(
% 0.21/0.61    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.61    inference(nnf_transformation,[],[f4])).
% 0.21/0.61  fof(f4,axiom,(
% 0.21/0.61    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.61  fof(f59,plain,(
% 0.21/0.61    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.61    inference(cnf_transformation,[],[f2])).
% 0.21/0.61  fof(f2,axiom,(
% 0.21/0.61    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.61  fof(f670,plain,(
% 0.21/0.61    ~r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl2_5 | ~spl2_19 | ~spl2_27 | spl2_31 | ~spl2_33)),
% 0.21/0.61    inference(forward_demodulation,[],[f669,f142])).
% 0.21/0.61  fof(f142,plain,(
% 0.21/0.61    k1_xboole_0 = k6_partfun1(k1_xboole_0) | ~spl2_5),
% 0.21/0.61    inference(avatar_component_clause,[],[f140])).
% 0.21/0.61  fof(f140,plain,(
% 0.21/0.61    spl2_5 <=> k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 0.21/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.61  fof(f669,plain,(
% 0.21/0.61    ~r2_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),k1_xboole_0) | (~spl2_5 | ~spl2_19 | ~spl2_27 | spl2_31 | ~spl2_33)),
% 0.21/0.61    inference(forward_demodulation,[],[f668,f397])).
% 0.21/0.61  fof(f397,plain,(
% 0.21/0.61    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl2_27),
% 0.21/0.61    inference(avatar_component_clause,[],[f395])).
% 0.21/0.61  fof(f395,plain,(
% 0.21/0.61    spl2_27 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).
% 0.21/0.61  fof(f668,plain,(
% 0.21/0.61    ~r2_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_relat_1(k1_xboole_0)),k1_xboole_0) | (~spl2_5 | ~spl2_19 | spl2_31 | ~spl2_33)),
% 0.21/0.61    inference(forward_demodulation,[],[f667,f564])).
% 0.21/0.61  fof(f564,plain,(
% 0.21/0.61    k1_xboole_0 = sK1 | (~spl2_19 | ~spl2_33)),
% 0.21/0.61    inference(subsumption_resolution,[],[f563,f59])).
% 0.21/0.61  fof(f563,plain,(
% 0.21/0.61    ~r1_tarski(k1_xboole_0,sK1) | k1_xboole_0 = sK1 | (~spl2_19 | ~spl2_33)),
% 0.21/0.61    inference(forward_demodulation,[],[f562,f106])).
% 0.21/0.61  fof(f106,plain,(
% 0.21/0.61    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.21/0.61    inference(equality_resolution,[],[f81])).
% 0.21/0.61  fof(f81,plain,(
% 0.21/0.61    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.21/0.61    inference(cnf_transformation,[],[f50])).
% 0.21/0.61  fof(f50,plain,(
% 0.21/0.61    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.61    inference(flattening,[],[f49])).
% 0.21/0.61  fof(f49,plain,(
% 0.21/0.61    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.61    inference(nnf_transformation,[],[f3])).
% 0.21/0.61  fof(f3,axiom,(
% 0.21/0.61    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.61  fof(f562,plain,(
% 0.21/0.61    ~r1_tarski(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),sK1) | k1_xboole_0 = sK1 | (~spl2_19 | ~spl2_33)),
% 0.21/0.61    inference(forward_demodulation,[],[f561,f508])).
% 0.21/0.61  fof(f508,plain,(
% 0.21/0.61    k1_xboole_0 = sK0 | ~spl2_33),
% 0.21/0.61    inference(avatar_component_clause,[],[f506])).
% 0.21/0.61  fof(f506,plain,(
% 0.21/0.61    spl2_33 <=> k1_xboole_0 = sK0),
% 0.21/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_33])])).
% 0.21/0.61  fof(f561,plain,(
% 0.21/0.61    k1_xboole_0 = sK1 | ~r1_tarski(k2_zfmisc_1(sK0,sK0),sK1) | (~spl2_19 | ~spl2_33)),
% 0.21/0.61    inference(forward_demodulation,[],[f536,f106])).
% 0.21/0.61  fof(f536,plain,(
% 0.21/0.61    sK1 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0) | ~r1_tarski(k2_zfmisc_1(sK0,sK0),sK1) | (~spl2_19 | ~spl2_33)),
% 0.21/0.61    inference(backward_demodulation,[],[f371,f508])).
% 0.21/0.61  fof(f371,plain,(
% 0.21/0.61    sK1 = k2_zfmisc_1(sK0,sK0) | ~r1_tarski(k2_zfmisc_1(sK0,sK0),sK1) | ~spl2_19),
% 0.21/0.61    inference(resolution,[],[f348,f76])).
% 0.21/0.61  fof(f76,plain,(
% 0.21/0.61    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.61    inference(cnf_transformation,[],[f47])).
% 0.21/0.61  fof(f47,plain,(
% 0.21/0.61    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.61    inference(flattening,[],[f46])).
% 0.21/0.61  fof(f46,plain,(
% 0.21/0.61    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.61    inference(nnf_transformation,[],[f1])).
% 0.21/0.61  fof(f1,axiom,(
% 0.21/0.61    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.61  fof(f348,plain,(
% 0.21/0.61    r1_tarski(sK1,k2_zfmisc_1(sK0,sK0)) | ~spl2_19),
% 0.21/0.61    inference(avatar_component_clause,[],[f346])).
% 0.21/0.61  fof(f346,plain,(
% 0.21/0.61    spl2_19 <=> r1_tarski(sK1,k2_zfmisc_1(sK0,sK0))),
% 0.21/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 0.21/0.61  fof(f667,plain,(
% 0.21/0.61    ~r2_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_relat_1(sK1)),k1_xboole_0) | (~spl2_5 | spl2_31 | ~spl2_33)),
% 0.21/0.61    inference(forward_demodulation,[],[f555,f142])).
% 0.21/0.61  fof(f555,plain,(
% 0.21/0.61    ~r2_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_relat_1(sK1)),k6_partfun1(k1_xboole_0)) | (spl2_31 | ~spl2_33)),
% 0.21/0.61    inference(backward_demodulation,[],[f499,f508])).
% 0.21/0.61  fof(f509,plain,(
% 0.21/0.61    spl2_32 | spl2_33 | ~spl2_2 | ~spl2_4),
% 0.21/0.61    inference(avatar_split_clause,[],[f261,f135,f125,f506,f502])).
% 0.21/0.61  fof(f125,plain,(
% 0.21/0.61    spl2_2 <=> v1_funct_2(sK1,sK0,sK0)),
% 0.21/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.61  fof(f135,plain,(
% 0.21/0.61    spl2_4 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.61  fof(f261,plain,(
% 0.21/0.61    k1_xboole_0 = sK0 | sK0 = k1_relset_1(sK0,sK0,sK1) | (~spl2_2 | ~spl2_4)),
% 0.21/0.61    inference(subsumption_resolution,[],[f256,f127])).
% 0.21/0.61  fof(f127,plain,(
% 0.21/0.61    v1_funct_2(sK1,sK0,sK0) | ~spl2_2),
% 0.21/0.61    inference(avatar_component_clause,[],[f125])).
% 0.21/0.61  fof(f256,plain,(
% 0.21/0.61    ~v1_funct_2(sK1,sK0,sK0) | k1_xboole_0 = sK0 | sK0 = k1_relset_1(sK0,sK0,sK1) | ~spl2_4),
% 0.21/0.61    inference(resolution,[],[f86,f137])).
% 0.21/0.61  fof(f137,plain,(
% 0.21/0.61    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl2_4),
% 0.21/0.61    inference(avatar_component_clause,[],[f135])).
% 0.21/0.61  fof(f86,plain,(
% 0.21/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 0.21/0.61    inference(cnf_transformation,[],[f51])).
% 0.21/0.61  fof(f51,plain,(
% 0.21/0.61    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.61    inference(nnf_transformation,[],[f36])).
% 0.21/0.61  fof(f36,plain,(
% 0.21/0.61    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.61    inference(flattening,[],[f35])).
% 0.21/0.61  fof(f35,plain,(
% 0.21/0.61    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.61    inference(ennf_transformation,[],[f13])).
% 0.21/0.61  fof(f13,axiom,(
% 0.21/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.61  fof(f500,plain,(
% 0.21/0.61    ~spl2_31 | ~spl2_1 | ~spl2_4 | ~spl2_7 | ~spl2_10 | spl2_15 | ~spl2_18 | ~spl2_29),
% 0.21/0.61    inference(avatar_split_clause,[],[f482,f447,f323,f286,f230,f193,f135,f120,f497])).
% 0.21/0.61  fof(f120,plain,(
% 0.21/0.61    spl2_1 <=> v1_funct_1(sK1)),
% 0.21/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.61  fof(f193,plain,(
% 0.21/0.61    spl2_7 <=> v1_relat_1(sK1)),
% 0.21/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.21/0.61  fof(f230,plain,(
% 0.21/0.61    spl2_10 <=> v2_funct_1(sK1)),
% 0.21/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.21/0.61  fof(f286,plain,(
% 0.21/0.61    spl2_15 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0))),
% 0.21/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.21/0.61  fof(f323,plain,(
% 0.21/0.61    spl2_18 <=> v1_funct_1(k2_funct_1(sK1))),
% 0.21/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 0.21/0.61  fof(f447,plain,(
% 0.21/0.61    spl2_29 <=> m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).
% 0.21/0.61  fof(f482,plain,(
% 0.21/0.61    ~r2_relset_1(sK0,sK0,k6_partfun1(k1_relat_1(sK1)),k6_partfun1(sK0)) | (~spl2_1 | ~spl2_4 | ~spl2_7 | ~spl2_10 | spl2_15 | ~spl2_18 | ~spl2_29)),
% 0.21/0.61    inference(backward_demodulation,[],[f288,f481])).
% 0.21/0.61  fof(f481,plain,(
% 0.21/0.61    k6_partfun1(k1_relat_1(sK1)) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) | (~spl2_1 | ~spl2_4 | ~spl2_7 | ~spl2_10 | ~spl2_18 | ~spl2_29)),
% 0.21/0.61    inference(forward_demodulation,[],[f459,f235])).
% 0.21/0.61  fof(f235,plain,(
% 0.21/0.61    k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) | (~spl2_1 | ~spl2_7 | ~spl2_10)),
% 0.21/0.61    inference(unit_resulting_resolution,[],[f195,f122,f232,f102])).
% 0.21/0.61  fof(f102,plain,(
% 0.21/0.61    ( ! [X0] : (~v2_funct_1(X0) | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.61    inference(definition_unfolding,[],[f65,f60])).
% 0.21/0.61  fof(f60,plain,(
% 0.21/0.61    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 0.21/0.61    inference(cnf_transformation,[],[f19])).
% 0.21/0.61  fof(f19,axiom,(
% 0.21/0.61    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 0.21/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 0.21/0.61  fof(f65,plain,(
% 0.21/0.61    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.61    inference(cnf_transformation,[],[f25])).
% 0.21/0.61  fof(f25,plain,(
% 0.21/0.61    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.61    inference(flattening,[],[f24])).
% 0.21/0.61  fof(f24,plain,(
% 0.21/0.61    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.61    inference(ennf_transformation,[],[f7])).
% 0.21/0.61  fof(f7,axiom,(
% 0.21/0.61    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 0.21/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).
% 0.21/0.61  fof(f232,plain,(
% 0.21/0.61    v2_funct_1(sK1) | ~spl2_10),
% 0.21/0.61    inference(avatar_component_clause,[],[f230])).
% 0.21/0.61  fof(f122,plain,(
% 0.21/0.61    v1_funct_1(sK1) | ~spl2_1),
% 0.21/0.61    inference(avatar_component_clause,[],[f120])).
% 0.21/0.61  fof(f195,plain,(
% 0.21/0.61    v1_relat_1(sK1) | ~spl2_7),
% 0.21/0.61    inference(avatar_component_clause,[],[f193])).
% 0.21/0.61  fof(f459,plain,(
% 0.21/0.61    k5_relat_1(sK1,k2_funct_1(sK1)) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) | (~spl2_1 | ~spl2_4 | ~spl2_18 | ~spl2_29)),
% 0.21/0.61    inference(unit_resulting_resolution,[],[f122,f137,f325,f449,f97])).
% 0.21/0.61  fof(f97,plain,(
% 0.21/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 0.21/0.61    inference(cnf_transformation,[],[f42])).
% 0.21/0.61  fof(f42,plain,(
% 0.21/0.61    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 0.21/0.61    inference(flattening,[],[f41])).
% 0.21/0.61  fof(f41,plain,(
% 0.21/0.61    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 0.21/0.61    inference(ennf_transformation,[],[f17])).
% 0.21/0.61  fof(f17,axiom,(
% 0.21/0.61    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 0.21/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 0.21/0.61  fof(f449,plain,(
% 0.21/0.61    m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl2_29),
% 0.21/0.61    inference(avatar_component_clause,[],[f447])).
% 0.21/0.61  fof(f325,plain,(
% 0.21/0.61    v1_funct_1(k2_funct_1(sK1)) | ~spl2_18),
% 0.21/0.61    inference(avatar_component_clause,[],[f323])).
% 0.21/0.61  fof(f288,plain,(
% 0.21/0.61    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) | spl2_15),
% 0.21/0.61    inference(avatar_component_clause,[],[f286])).
% 0.21/0.61  fof(f486,plain,(
% 0.21/0.61    ~spl2_1 | ~spl2_4 | ~spl2_7 | ~spl2_10 | ~spl2_14 | spl2_16 | ~spl2_17 | ~spl2_18 | ~spl2_29),
% 0.21/0.61    inference(avatar_contradiction_clause,[],[f485])).
% 0.21/0.61  fof(f485,plain,(
% 0.21/0.61    $false | (~spl2_1 | ~spl2_4 | ~spl2_7 | ~spl2_10 | ~spl2_14 | spl2_16 | ~spl2_17 | ~spl2_18 | ~spl2_29)),
% 0.21/0.61    inference(subsumption_resolution,[],[f484,f200])).
% 0.21/0.61  fof(f484,plain,(
% 0.21/0.61    ~r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) | (~spl2_1 | ~spl2_4 | ~spl2_7 | ~spl2_10 | ~spl2_14 | spl2_16 | ~spl2_17 | ~spl2_18 | ~spl2_29)),
% 0.21/0.61    inference(backward_demodulation,[],[f293,f483])).
% 0.21/0.61  fof(f483,plain,(
% 0.21/0.61    k6_partfun1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) | (~spl2_1 | ~spl2_4 | ~spl2_7 | ~spl2_10 | ~spl2_14 | ~spl2_17 | ~spl2_18 | ~spl2_29)),
% 0.21/0.61    inference(forward_demodulation,[],[f457,f328])).
% 0.21/0.61  fof(f328,plain,(
% 0.21/0.61    k6_partfun1(sK0) = k5_relat_1(k2_funct_1(sK1),sK1) | (~spl2_1 | ~spl2_7 | ~spl2_10 | ~spl2_14 | ~spl2_17)),
% 0.21/0.61    inference(backward_demodulation,[],[f236,f327])).
% 0.21/0.61  fof(f327,plain,(
% 0.21/0.61    sK0 = k2_relat_1(sK1) | (~spl2_7 | ~spl2_14 | ~spl2_17)),
% 0.21/0.61    inference(unit_resulting_resolution,[],[f195,f273,f298,f67])).
% 0.21/0.61  fof(f67,plain,(
% 0.21/0.61    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | k2_relat_1(X1) = X0) )),
% 0.21/0.61    inference(cnf_transformation,[],[f45])).
% 0.21/0.61  fof(f45,plain,(
% 0.21/0.61    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.61    inference(nnf_transformation,[],[f27])).
% 0.21/0.61  fof(f27,plain,(
% 0.21/0.61    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.61    inference(flattening,[],[f26])).
% 0.21/0.61  fof(f26,plain,(
% 0.21/0.61    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.61    inference(ennf_transformation,[],[f14])).
% 0.21/0.61  fof(f14,axiom,(
% 0.21/0.61    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 0.21/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).
% 0.21/0.61  fof(f298,plain,(
% 0.21/0.61    v2_funct_2(sK1,sK0) | ~spl2_17),
% 0.21/0.61    inference(avatar_component_clause,[],[f296])).
% 0.21/0.61  fof(f296,plain,(
% 0.21/0.61    spl2_17 <=> v2_funct_2(sK1,sK0)),
% 0.21/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 0.21/0.61  fof(f273,plain,(
% 0.21/0.61    v5_relat_1(sK1,sK0) | ~spl2_14),
% 0.21/0.61    inference(avatar_component_clause,[],[f271])).
% 0.21/0.61  fof(f271,plain,(
% 0.21/0.61    spl2_14 <=> v5_relat_1(sK1,sK0)),
% 0.21/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.21/0.61  fof(f236,plain,(
% 0.21/0.61    k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(k2_relat_1(sK1)) | (~spl2_1 | ~spl2_7 | ~spl2_10)),
% 0.21/0.61    inference(unit_resulting_resolution,[],[f195,f122,f232,f101])).
% 0.21/0.61  fof(f101,plain,(
% 0.21/0.61    ( ! [X0] : (~v2_funct_1(X0) | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.61    inference(definition_unfolding,[],[f66,f60])).
% 0.21/0.61  fof(f66,plain,(
% 0.21/0.61    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.61    inference(cnf_transformation,[],[f25])).
% 0.21/0.61  fof(f457,plain,(
% 0.21/0.61    k5_relat_1(k2_funct_1(sK1),sK1) = k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) | (~spl2_1 | ~spl2_4 | ~spl2_18 | ~spl2_29)),
% 0.21/0.61    inference(unit_resulting_resolution,[],[f122,f325,f137,f449,f97])).
% 0.21/0.61  fof(f293,plain,(
% 0.21/0.61    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0)) | spl2_16),
% 0.21/0.61    inference(avatar_component_clause,[],[f291])).
% 0.21/0.61  fof(f291,plain,(
% 0.21/0.61    spl2_16 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0))),
% 0.21/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.21/0.61  fof(f450,plain,(
% 0.21/0.61    spl2_29 | ~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_4),
% 0.21/0.61    inference(avatar_split_clause,[],[f318,f135,f130,f125,f120,f447])).
% 0.21/0.61  fof(f130,plain,(
% 0.21/0.61    spl2_3 <=> v3_funct_2(sK1,sK0,sK0)),
% 0.21/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.61  fof(f318,plain,(
% 0.21/0.61    m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | (~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_4)),
% 0.21/0.61    inference(forward_demodulation,[],[f306,f280])).
% 0.21/0.61  fof(f280,plain,(
% 0.21/0.61    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | (~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_4)),
% 0.21/0.61    inference(unit_resulting_resolution,[],[f122,f127,f132,f137,f69])).
% 0.21/0.61  fof(f69,plain,(
% 0.21/0.61    ( ! [X0,X1] : (~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | k2_funct_2(X0,X1) = k2_funct_1(X1)) )),
% 0.21/0.61    inference(cnf_transformation,[],[f29])).
% 0.21/0.61  fof(f29,plain,(
% 0.21/0.61    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 0.21/0.61    inference(flattening,[],[f28])).
% 0.21/0.61  fof(f28,plain,(
% 0.21/0.61    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 0.21/0.61    inference(ennf_transformation,[],[f18])).
% 0.21/0.61  fof(f18,axiom,(
% 0.21/0.61    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_2(X0,X1) = k2_funct_1(X1))),
% 0.21/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).
% 0.21/0.61  fof(f132,plain,(
% 0.21/0.61    v3_funct_2(sK1,sK0,sK0) | ~spl2_3),
% 0.21/0.61    inference(avatar_component_clause,[],[f130])).
% 0.21/0.61  fof(f306,plain,(
% 0.21/0.61    m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | (~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_4)),
% 0.21/0.61    inference(unit_resulting_resolution,[],[f122,f127,f132,f137,f73])).
% 0.21/0.61  fof(f73,plain,(
% 0.21/0.61    ( ! [X0,X1] : (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 0.21/0.61    inference(cnf_transformation,[],[f31])).
% 0.21/0.61  fof(f31,plain,(
% 0.21/0.61    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 0.21/0.61    inference(flattening,[],[f30])).
% 0.21/0.61  fof(f30,plain,(
% 0.21/0.61    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 0.21/0.61    inference(ennf_transformation,[],[f15])).
% 0.21/0.61  fof(f15,axiom,(
% 0.21/0.61    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))))),
% 0.21/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_2)).
% 0.21/0.61  fof(f445,plain,(
% 0.21/0.61    spl2_28 | ~spl2_4),
% 0.21/0.61    inference(avatar_split_clause,[],[f218,f135,f442])).
% 0.21/0.61  fof(f218,plain,(
% 0.21/0.61    k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1) | ~spl2_4),
% 0.21/0.61    inference(unit_resulting_resolution,[],[f137,f83])).
% 0.21/0.61  fof(f83,plain,(
% 0.21/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.21/0.61    inference(cnf_transformation,[],[f33])).
% 0.21/0.61  fof(f33,plain,(
% 0.21/0.61    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.61    inference(ennf_transformation,[],[f10])).
% 0.21/0.61  fof(f10,axiom,(
% 0.21/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.61  fof(f398,plain,(
% 0.21/0.61    spl2_27 | ~spl2_5),
% 0.21/0.61    inference(avatar_split_clause,[],[f146,f140,f395])).
% 0.21/0.61  fof(f146,plain,(
% 0.21/0.61    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl2_5),
% 0.21/0.61    inference(superposition,[],[f100,f142])).
% 0.21/0.61  fof(f100,plain,(
% 0.21/0.61    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 0.21/0.61    inference(definition_unfolding,[],[f63,f60])).
% 0.21/0.61  fof(f63,plain,(
% 0.21/0.61    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.61    inference(cnf_transformation,[],[f5])).
% 0.21/0.61  fof(f5,axiom,(
% 0.21/0.61    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.21/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.21/0.61  fof(f349,plain,(
% 0.21/0.61    spl2_19 | ~spl2_4),
% 0.21/0.61    inference(avatar_split_clause,[],[f158,f135,f346])).
% 0.21/0.61  fof(f158,plain,(
% 0.21/0.61    r1_tarski(sK1,k2_zfmisc_1(sK0,sK0)) | ~spl2_4),
% 0.21/0.61    inference(unit_resulting_resolution,[],[f137,f77])).
% 0.21/0.61  fof(f77,plain,(
% 0.21/0.61    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.61    inference(cnf_transformation,[],[f48])).
% 0.21/0.61  fof(f326,plain,(
% 0.21/0.61    spl2_18 | ~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_4),
% 0.21/0.61    inference(avatar_split_clause,[],[f282,f135,f130,f125,f120,f323])).
% 0.21/0.61  fof(f282,plain,(
% 0.21/0.61    v1_funct_1(k2_funct_1(sK1)) | (~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_4)),
% 0.21/0.61    inference(backward_demodulation,[],[f268,f280])).
% 0.21/0.61  fof(f268,plain,(
% 0.21/0.61    v1_funct_1(k2_funct_2(sK0,sK1)) | (~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_4)),
% 0.21/0.61    inference(unit_resulting_resolution,[],[f122,f127,f132,f137,f70])).
% 0.21/0.61  fof(f70,plain,(
% 0.21/0.61    ( ! [X0,X1] : (~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | v1_funct_1(k2_funct_2(X0,X1))) )),
% 0.21/0.61    inference(cnf_transformation,[],[f31])).
% 0.21/0.61  fof(f299,plain,(
% 0.21/0.61    spl2_17 | ~spl2_1 | ~spl2_3 | ~spl2_4),
% 0.21/0.61    inference(avatar_split_clause,[],[f240,f135,f130,f120,f296])).
% 0.21/0.61  fof(f240,plain,(
% 0.21/0.61    v2_funct_2(sK1,sK0) | (~spl2_1 | ~spl2_3 | ~spl2_4)),
% 0.21/0.61    inference(unit_resulting_resolution,[],[f122,f132,f137,f94])).
% 0.21/0.61  fof(f94,plain,(
% 0.21/0.61    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v3_funct_2(X2,X0,X1) | v2_funct_2(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.61    inference(cnf_transformation,[],[f38])).
% 0.21/0.61  fof(f38,plain,(
% 0.21/0.61    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.61    inference(flattening,[],[f37])).
% 0.21/0.61  fof(f37,plain,(
% 0.21/0.61    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.61    inference(ennf_transformation,[],[f12])).
% 0.21/0.61  fof(f12,axiom,(
% 0.21/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 0.21/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).
% 0.21/0.61  fof(f294,plain,(
% 0.21/0.61    ~spl2_16 | ~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_4 | spl2_12),
% 0.21/0.61    inference(avatar_split_clause,[],[f284,f247,f135,f130,f125,f120,f291])).
% 0.21/0.61  fof(f247,plain,(
% 0.21/0.61    spl2_12 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))),
% 0.21/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.21/0.61  fof(f284,plain,(
% 0.21/0.61    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0)) | (~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_4 | spl2_12)),
% 0.21/0.61    inference(backward_demodulation,[],[f249,f280])).
% 0.21/0.61  fof(f249,plain,(
% 0.21/0.61    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | spl2_12),
% 0.21/0.61    inference(avatar_component_clause,[],[f247])).
% 0.21/0.61  fof(f289,plain,(
% 0.21/0.61    ~spl2_15 | ~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_4 | spl2_11),
% 0.21/0.61    inference(avatar_split_clause,[],[f283,f243,f135,f130,f125,f120,f286])).
% 0.21/0.61  fof(f243,plain,(
% 0.21/0.61    spl2_11 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))),
% 0.21/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.21/0.61  fof(f283,plain,(
% 0.21/0.61    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) | (~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_4 | spl2_11)),
% 0.21/0.61    inference(backward_demodulation,[],[f245,f280])).
% 0.21/0.61  fof(f245,plain,(
% 0.21/0.61    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) | spl2_11),
% 0.21/0.61    inference(avatar_component_clause,[],[f243])).
% 0.21/0.61  fof(f274,plain,(
% 0.21/0.61    spl2_14 | ~spl2_4),
% 0.21/0.61    inference(avatar_split_clause,[],[f185,f135,f271])).
% 0.21/0.61  fof(f185,plain,(
% 0.21/0.61    v5_relat_1(sK1,sK0) | ~spl2_4),
% 0.21/0.61    inference(unit_resulting_resolution,[],[f137,f85])).
% 0.21/0.61  fof(f85,plain,(
% 0.21/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.21/0.61    inference(cnf_transformation,[],[f34])).
% 0.21/0.61  fof(f34,plain,(
% 0.21/0.61    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.61    inference(ennf_transformation,[],[f9])).
% 0.21/0.61  fof(f9,axiom,(
% 0.21/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.61  fof(f250,plain,(
% 0.21/0.61    ~spl2_11 | ~spl2_12),
% 0.21/0.61    inference(avatar_split_clause,[],[f57,f247,f243])).
% 0.21/0.61  fof(f57,plain,(
% 0.21/0.61    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))),
% 0.21/0.61    inference(cnf_transformation,[],[f44])).
% 0.21/0.61  fof(f44,plain,(
% 0.21/0.61    (~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 0.21/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f43])).
% 0.21/0.61  fof(f43,plain,(
% 0.21/0.61    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ((~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 0.21/0.61    introduced(choice_axiom,[])).
% 0.21/0.61  fof(f23,plain,(
% 0.21/0.61    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.21/0.61    inference(flattening,[],[f22])).
% 0.21/0.61  fof(f22,plain,(
% 0.21/0.61    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 0.21/0.61    inference(ennf_transformation,[],[f21])).
% 0.21/0.61  fof(f21,negated_conjecture,(
% 0.21/0.61    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 0.21/0.61    inference(negated_conjecture,[],[f20])).
% 0.21/0.61  fof(f20,conjecture,(
% 0.21/0.61    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 0.21/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_funct_2)).
% 0.21/0.61  fof(f233,plain,(
% 0.21/0.61    spl2_10 | ~spl2_1 | ~spl2_3 | ~spl2_4),
% 0.21/0.61    inference(avatar_split_clause,[],[f227,f135,f130,f120,f230])).
% 0.21/0.61  fof(f227,plain,(
% 0.21/0.61    v2_funct_1(sK1) | (~spl2_1 | ~spl2_3 | ~spl2_4)),
% 0.21/0.61    inference(unit_resulting_resolution,[],[f122,f132,f137,f93])).
% 0.21/0.61  fof(f93,plain,(
% 0.21/0.61    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v3_funct_2(X2,X0,X1) | v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.61    inference(cnf_transformation,[],[f38])).
% 0.21/0.61  fof(f196,plain,(
% 0.21/0.61    spl2_7 | ~spl2_4),
% 0.21/0.61    inference(avatar_split_clause,[],[f165,f135,f193])).
% 0.21/0.61  fof(f165,plain,(
% 0.21/0.61    v1_relat_1(sK1) | ~spl2_4),
% 0.21/0.61    inference(unit_resulting_resolution,[],[f137,f82])).
% 0.21/0.61  fof(f82,plain,(
% 0.21/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.61    inference(cnf_transformation,[],[f32])).
% 0.21/0.61  fof(f32,plain,(
% 0.21/0.61    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.61    inference(ennf_transformation,[],[f8])).
% 0.21/0.61  fof(f8,axiom,(
% 0.21/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.61  fof(f143,plain,(
% 0.21/0.61    spl2_5),
% 0.21/0.61    inference(avatar_split_clause,[],[f98,f140])).
% 0.21/0.61  fof(f98,plain,(
% 0.21/0.61    k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 0.21/0.61    inference(definition_unfolding,[],[f58,f60])).
% 0.21/0.61  fof(f58,plain,(
% 0.21/0.61    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.21/0.61    inference(cnf_transformation,[],[f6])).
% 0.21/0.61  fof(f6,axiom,(
% 0.21/0.61    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.21/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).
% 0.21/0.61  fof(f138,plain,(
% 0.21/0.61    spl2_4),
% 0.21/0.61    inference(avatar_split_clause,[],[f56,f135])).
% 0.21/0.61  fof(f56,plain,(
% 0.21/0.61    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.61    inference(cnf_transformation,[],[f44])).
% 0.21/0.61  fof(f133,plain,(
% 0.21/0.61    spl2_3),
% 0.21/0.61    inference(avatar_split_clause,[],[f55,f130])).
% 0.21/0.61  fof(f55,plain,(
% 0.21/0.61    v3_funct_2(sK1,sK0,sK0)),
% 0.21/0.61    inference(cnf_transformation,[],[f44])).
% 0.21/0.61  fof(f128,plain,(
% 0.21/0.61    spl2_2),
% 0.21/0.61    inference(avatar_split_clause,[],[f54,f125])).
% 0.21/0.61  fof(f54,plain,(
% 0.21/0.61    v1_funct_2(sK1,sK0,sK0)),
% 0.21/0.61    inference(cnf_transformation,[],[f44])).
% 0.21/0.61  fof(f123,plain,(
% 0.21/0.61    spl2_1),
% 0.21/0.61    inference(avatar_split_clause,[],[f53,f120])).
% 0.21/0.61  fof(f53,plain,(
% 0.21/0.61    v1_funct_1(sK1)),
% 0.21/0.61    inference(cnf_transformation,[],[f44])).
% 0.21/0.61  % SZS output end Proof for theBenchmark
% 0.21/0.61  % (31870)------------------------------
% 0.21/0.61  % (31870)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.61  % (31870)Termination reason: Refutation
% 0.21/0.61  
% 0.21/0.61  % (31870)Memory used [KB]: 11257
% 0.21/0.61  % (31870)Time elapsed: 0.184 s
% 0.21/0.61  % (31870)------------------------------
% 0.21/0.61  % (31870)------------------------------
% 0.21/0.61  % (31849)Success in time 0.246 s
%------------------------------------------------------------------------------
