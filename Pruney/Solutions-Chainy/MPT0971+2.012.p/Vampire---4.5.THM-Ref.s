%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:01:00 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  153 ( 275 expanded)
%              Number of leaves         :   35 ( 117 expanded)
%              Depth                    :    9
%              Number of atoms          :  420 ( 808 expanded)
%              Number of equality atoms :   97 ( 199 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f629,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f90,f97,f102,f107,f123,f131,f141,f151,f161,f171,f230,f265,f272,f302,f368,f381,f406,f415,f439,f460,f520,f534,f594,f605,f625,f628])).

fof(f628,plain,
    ( k1_xboole_0 != sK1
    | k1_relset_1(sK0,sK1,sK3) != k1_relat_1(sK3)
    | sK0 != k1_relset_1(sK0,k1_xboole_0,sK3)
    | r2_hidden(sK6(sK3,sK2),sK0)
    | ~ r2_hidden(sK6(sK3,sK2),k1_relat_1(sK3)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f625,plain,
    ( ~ spl12_48
    | spl12_56
    | ~ spl12_58 ),
    inference(avatar_contradiction_clause,[],[f624])).

fof(f624,plain,
    ( $false
    | ~ spl12_48
    | spl12_56
    | ~ spl12_58 ),
    inference(subsumption_resolution,[],[f623,f519])).

fof(f519,plain,
    ( v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | ~ spl12_48 ),
    inference(avatar_component_clause,[],[f517])).

fof(f517,plain,
    ( spl12_48
  <=> v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_48])])).

fof(f623,plain,
    ( ~ v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | spl12_56
    | ~ spl12_58 ),
    inference(subsumption_resolution,[],[f611,f593])).

fof(f593,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | spl12_56 ),
    inference(avatar_component_clause,[],[f591])).

fof(f591,plain,
    ( spl12_56
  <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_56])])).

fof(f611,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | ~ v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | ~ spl12_58 ),
    inference(resolution,[],[f604,f79])).

fof(f79,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f28,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f604,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl12_58 ),
    inference(avatar_component_clause,[],[f602])).

fof(f602,plain,
    ( spl12_58
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_58])])).

fof(f605,plain,
    ( spl12_58
    | ~ spl12_42
    | ~ spl12_43 ),
    inference(avatar_split_clause,[],[f500,f457,f436,f602])).

fof(f436,plain,
    ( spl12_42
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_42])])).

fof(f457,plain,
    ( spl12_43
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_43])])).

fof(f500,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl12_42
    | ~ spl12_43 ),
    inference(superposition,[],[f438,f459])).

fof(f459,plain,
    ( k1_xboole_0 = sK0
    | ~ spl12_43 ),
    inference(avatar_component_clause,[],[f457])).

fof(f438,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl12_42 ),
    inference(avatar_component_clause,[],[f436])).

fof(f594,plain,
    ( ~ spl12_56
    | spl12_36
    | ~ spl12_43 ),
    inference(avatar_split_clause,[],[f497,f457,f370,f591])).

fof(f370,plain,
    ( spl12_36
  <=> sK0 = k1_relset_1(sK0,k1_xboole_0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_36])])).

fof(f497,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | spl12_36
    | ~ spl12_43 ),
    inference(superposition,[],[f372,f459])).

fof(f372,plain,
    ( sK0 != k1_relset_1(sK0,k1_xboole_0,sK3)
    | spl12_36 ),
    inference(avatar_component_clause,[],[f370])).

fof(f534,plain,
    ( spl12_50
    | ~ spl12_10 ),
    inference(avatar_split_clause,[],[f163,f158,f531])).

fof(f531,plain,
    ( spl12_50
  <=> r2_hidden(sK6(sK3,sK2),k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_50])])).

fof(f158,plain,
    ( spl12_10
  <=> sP5(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_10])])).

fof(f163,plain,
    ( r2_hidden(sK6(sK3,sK2),k1_relat_1(sK3))
    | ~ spl12_10 ),
    inference(resolution,[],[f160,f46])).

fof(f46,plain,(
    ! [X2,X0] :
      ( ~ sP5(X2,X0)
      | r2_hidden(sK6(X0,X2),k1_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

fof(f160,plain,
    ( sP5(sK2,sK3)
    | ~ spl12_10 ),
    inference(avatar_component_clause,[],[f158])).

fof(f520,plain,
    ( spl12_48
    | ~ spl12_28
    | ~ spl12_43 ),
    inference(avatar_split_clause,[],[f491,f457,f299,f517])).

fof(f299,plain,
    ( spl12_28
  <=> v1_funct_2(sK3,sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_28])])).

fof(f491,plain,
    ( v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | ~ spl12_28
    | ~ spl12_43 ),
    inference(superposition,[],[f301,f459])).

fof(f301,plain,
    ( v1_funct_2(sK3,sK0,k1_xboole_0)
    | ~ spl12_28 ),
    inference(avatar_component_clause,[],[f299])).

fof(f460,plain,
    ( spl12_43
    | spl12_13
    | ~ spl12_28
    | ~ spl12_42 ),
    inference(avatar_split_clause,[],[f453,f436,f299,f182,f457])).

fof(f182,plain,
    ( spl12_13
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_13])])).

fof(f453,plain,
    ( k1_xboole_0 = sK0
    | spl12_13
    | ~ spl12_28
    | ~ spl12_42 ),
    inference(subsumption_resolution,[],[f452,f301])).

fof(f452,plain,
    ( k1_xboole_0 = sK0
    | ~ v1_funct_2(sK3,sK0,k1_xboole_0)
    | spl12_13
    | ~ spl12_42 ),
    inference(subsumption_resolution,[],[f441,f183])).

fof(f183,plain,
    ( k1_xboole_0 != sK3
    | spl12_13 ),
    inference(avatar_component_clause,[],[f182])).

fof(f441,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK3
    | ~ v1_funct_2(sK3,sK0,k1_xboole_0)
    | ~ spl12_42 ),
    inference(resolution,[],[f438,f81])).

fof(f81,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0) ) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X1
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f439,plain,
    ( spl12_42
    | ~ spl12_3
    | ~ spl12_22 ),
    inference(avatar_split_clause,[],[f421,f262,f99,f436])).

fof(f99,plain,
    ( spl12_3
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_3])])).

fof(f262,plain,
    ( spl12_22
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_22])])).

fof(f421,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl12_3
    | ~ spl12_22 ),
    inference(superposition,[],[f101,f264])).

fof(f264,plain,
    ( k1_xboole_0 = sK1
    | ~ spl12_22 ),
    inference(avatar_component_clause,[],[f262])).

fof(f101,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl12_3 ),
    inference(avatar_component_clause,[],[f99])).

fof(f415,plain,
    ( ~ spl12_37
    | ~ spl12_39 ),
    inference(avatar_contradiction_clause,[],[f414])).

fof(f414,plain,
    ( $false
    | ~ spl12_37
    | ~ spl12_39 ),
    inference(subsumption_resolution,[],[f413,f380])).

fof(f380,plain,
    ( r2_hidden(sK6(sK3,sK2),sK0)
    | ~ spl12_37 ),
    inference(avatar_component_clause,[],[f378])).

fof(f378,plain,
    ( spl12_37
  <=> r2_hidden(sK6(sK3,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_37])])).

fof(f413,plain,
    ( ~ r2_hidden(sK6(sK3,sK2),sK0)
    | ~ spl12_39 ),
    inference(trivial_inequality_removal,[],[f412])).

fof(f412,plain,
    ( sK2 != sK2
    | ~ r2_hidden(sK6(sK3,sK2),sK0)
    | ~ spl12_39 ),
    inference(superposition,[],[f32,f405])).

fof(f405,plain,
    ( sK2 = k1_funct_1(sK3,sK6(sK3,sK2))
    | ~ spl12_39 ),
    inference(avatar_component_clause,[],[f403])).

fof(f403,plain,
    ( spl12_39
  <=> sK2 = k1_funct_1(sK3,sK6(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_39])])).

fof(f32,plain,(
    ! [X4] :
      ( sK2 != k1_funct_1(sK3,X4)
      | ~ r2_hidden(X4,sK0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(X3,X4) != X2
          | ~ r2_hidden(X4,X0) )
      & r2_hidden(X2,k2_relset_1(X0,X1,X3))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(X3,X4) != X2
          | ~ r2_hidden(X4,X0) )
      & r2_hidden(X2,k2_relset_1(X0,X1,X3))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ~ ( ! [X4] :
                ~ ( k1_funct_1(X3,X4) = X2
                  & r2_hidden(X4,X0) )
            & r2_hidden(X2,k2_relset_1(X0,X1,X3)) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ~ ( ! [X4] :
              ~ ( k1_funct_1(X3,X4) = X2
                & r2_hidden(X4,X0) )
          & r2_hidden(X2,k2_relset_1(X0,X1,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_funct_2)).

fof(f406,plain,
    ( spl12_39
    | ~ spl12_10 ),
    inference(avatar_split_clause,[],[f164,f158,f403])).

fof(f164,plain,
    ( sK2 = k1_funct_1(sK3,sK6(sK3,sK2))
    | ~ spl12_10 ),
    inference(resolution,[],[f160,f47])).

fof(f47,plain,(
    ! [X2,X0] :
      ( ~ sP5(X2,X0)
      | k1_funct_1(X0,sK6(X0,X2)) = X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f381,plain,
    ( spl12_37
    | ~ spl12_10
    | ~ spl12_23 ),
    inference(avatar_split_clause,[],[f363,f267,f158,f378])).

fof(f267,plain,
    ( spl12_23
  <=> sK0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_23])])).

fof(f363,plain,
    ( r2_hidden(sK6(sK3,sK2),sK0)
    | ~ spl12_10
    | ~ spl12_23 ),
    inference(forward_demodulation,[],[f163,f269])).

fof(f269,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl12_23 ),
    inference(avatar_component_clause,[],[f267])).

fof(f368,plain,
    ( ~ spl12_9
    | ~ spl12_11
    | ~ spl12_18 ),
    inference(avatar_contradiction_clause,[],[f367])).

fof(f367,plain,
    ( $false
    | ~ spl12_9
    | ~ spl12_11
    | ~ spl12_18 ),
    inference(subsumption_resolution,[],[f366,f229])).

fof(f229,plain,
    ( r2_hidden(sK2,k1_xboole_0)
    | ~ spl12_18 ),
    inference(avatar_component_clause,[],[f227])).

fof(f227,plain,
    ( spl12_18
  <=> r2_hidden(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_18])])).

fof(f366,plain,
    ( ~ r2_hidden(sK2,k1_xboole_0)
    | ~ spl12_9
    | ~ spl12_11 ),
    inference(superposition,[],[f173,f170])).

fof(f170,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_tarski(sK2),k2_relat_1(sK3))
    | ~ spl12_11 ),
    inference(avatar_component_clause,[],[f168])).

fof(f168,plain,
    ( spl12_11
  <=> k1_xboole_0 = k4_xboole_0(k1_tarski(sK2),k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_11])])).

fof(f173,plain,
    ( ! [X1] : ~ r2_hidden(sK2,k4_xboole_0(X1,k2_relat_1(sK3)))
    | ~ spl12_9 ),
    inference(resolution,[],[f154,f84])).

fof(f84,plain,(
    ! [X0,X3,X1] :
      ( sP9(X3,X1,X0)
      | ~ r2_hidden(X3,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f70])).

% (26701)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( sP9(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f154,plain,
    ( ! [X0] : ~ sP9(sK2,k2_relat_1(sK3),X0)
    | ~ spl12_9 ),
    inference(resolution,[],[f150,f68])).

fof(f68,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ sP9(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f150,plain,
    ( r2_hidden(sK2,k2_relat_1(sK3))
    | ~ spl12_9 ),
    inference(avatar_component_clause,[],[f148])).

fof(f148,plain,
    ( spl12_9
  <=> r2_hidden(sK2,k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_9])])).

fof(f302,plain,
    ( spl12_28
    | ~ spl12_2
    | ~ spl12_22 ),
    inference(avatar_split_clause,[],[f289,f262,f94,f299])).

fof(f94,plain,
    ( spl12_2
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).

fof(f289,plain,
    ( v1_funct_2(sK3,sK0,k1_xboole_0)
    | ~ spl12_2
    | ~ spl12_22 ),
    inference(superposition,[],[f96,f264])).

fof(f96,plain,
    ( v1_funct_2(sK3,sK0,sK1)
    | ~ spl12_2 ),
    inference(avatar_component_clause,[],[f94])).

fof(f272,plain,
    ( spl12_23
    | ~ spl12_6
    | ~ spl12_21 ),
    inference(avatar_split_clause,[],[f270,f258,f128,f267])).

fof(f128,plain,
    ( spl12_6
  <=> k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_6])])).

fof(f258,plain,
    ( spl12_21
  <=> sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_21])])).

fof(f270,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl12_6
    | ~ spl12_21 ),
    inference(superposition,[],[f260,f130])).

fof(f130,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)
    | ~ spl12_6 ),
    inference(avatar_component_clause,[],[f128])).

fof(f260,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl12_21 ),
    inference(avatar_component_clause,[],[f258])).

fof(f265,plain,
    ( spl12_21
    | spl12_22
    | ~ spl12_2
    | ~ spl12_3 ),
    inference(avatar_split_clause,[],[f118,f99,f94,f262,f258])).

fof(f118,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl12_2
    | ~ spl12_3 ),
    inference(subsumption_resolution,[],[f112,f96])).

fof(f112,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ v1_funct_2(sK3,sK0,sK1)
    | ~ spl12_3 ),
    inference(resolution,[],[f101,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f230,plain,
    ( spl12_18
    | ~ spl12_9
    | ~ spl12_13 ),
    inference(avatar_split_clause,[],[f222,f182,f148,f227])).

fof(f222,plain,
    ( r2_hidden(sK2,k1_xboole_0)
    | ~ spl12_9
    | ~ spl12_13 ),
    inference(forward_demodulation,[],[f215,f38])).

fof(f38,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f215,plain,
    ( r2_hidden(sK2,k2_relat_1(k1_xboole_0))
    | ~ spl12_9
    | ~ spl12_13 ),
    inference(superposition,[],[f150,f184])).

fof(f184,plain,
    ( k1_xboole_0 = sK3
    | ~ spl12_13 ),
    inference(avatar_component_clause,[],[f182])).

fof(f171,plain,
    ( spl12_11
    | ~ spl12_4
    | ~ spl12_8 ),
    inference(avatar_split_clause,[],[f166,f138,f104,f168])).

fof(f104,plain,
    ( spl12_4
  <=> r2_hidden(sK2,k2_relset_1(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_4])])).

fof(f138,plain,
    ( spl12_8
  <=> k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_8])])).

fof(f166,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_tarski(sK2),k2_relat_1(sK3))
    | ~ spl12_4
    | ~ spl12_8 ),
    inference(forward_demodulation,[],[f125,f140])).

fof(f140,plain,
    ( k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3)
    | ~ spl12_8 ),
    inference(avatar_component_clause,[],[f138])).

fof(f125,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_tarski(sK2),k2_relset_1(sK0,sK1,sK3))
    | ~ spl12_4 ),
    inference(resolution,[],[f106,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l35_zfmisc_1)).

fof(f106,plain,
    ( r2_hidden(sK2,k2_relset_1(sK0,sK1,sK3))
    | ~ spl12_4 ),
    inference(avatar_component_clause,[],[f104])).

fof(f161,plain,
    ( spl12_10
    | ~ spl12_1
    | ~ spl12_5
    | ~ spl12_9 ),
    inference(avatar_split_clause,[],[f153,f148,f120,f87,f158])).

fof(f87,plain,
    ( spl12_1
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).

fof(f120,plain,
    ( spl12_5
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_5])])).

fof(f153,plain,
    ( sP5(sK2,sK3)
    | ~ spl12_1
    | ~ spl12_5
    | ~ spl12_9 ),
    inference(resolution,[],[f150,f146])).

fof(f146,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,k2_relat_1(sK3))
        | sP5(X2,sK3) )
    | ~ spl12_1
    | ~ spl12_5 ),
    inference(subsumption_resolution,[],[f92,f122])).

fof(f122,plain,
    ( v1_relat_1(sK3)
    | ~ spl12_5 ),
    inference(avatar_component_clause,[],[f120])).

fof(f92,plain,
    ( ! [X2] :
        ( ~ v1_relat_1(sK3)
        | sP5(X2,sK3)
        | ~ r2_hidden(X2,k2_relat_1(sK3)) )
    | ~ spl12_1 ),
    inference(resolution,[],[f89,f76])).

fof(f76,plain,(
    ! [X2,X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | sP5(X2,X0)
      | ~ r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | sP5(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f89,plain,
    ( v1_funct_1(sK3)
    | ~ spl12_1 ),
    inference(avatar_component_clause,[],[f87])).

fof(f151,plain,
    ( spl12_9
    | ~ spl12_4
    | ~ spl12_8 ),
    inference(avatar_split_clause,[],[f145,f138,f104,f148])).

fof(f145,plain,
    ( r2_hidden(sK2,k2_relat_1(sK3))
    | ~ spl12_4
    | ~ spl12_8 ),
    inference(superposition,[],[f106,f140])).

fof(f141,plain,
    ( spl12_8
    | ~ spl12_3 ),
    inference(avatar_split_clause,[],[f110,f99,f138])).

fof(f110,plain,
    ( k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3)
    | ~ spl12_3 ),
    inference(resolution,[],[f101,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f131,plain,
    ( spl12_6
    | ~ spl12_3 ),
    inference(avatar_split_clause,[],[f109,f99,f128])).

fof(f109,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)
    | ~ spl12_3 ),
    inference(resolution,[],[f101,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f123,plain,
    ( spl12_5
    | ~ spl12_3 ),
    inference(avatar_split_clause,[],[f108,f99,f120])).

fof(f108,plain,
    ( v1_relat_1(sK3)
    | ~ spl12_3 ),
    inference(resolution,[],[f101,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f107,plain,(
    spl12_4 ),
    inference(avatar_split_clause,[],[f36,f104])).

fof(f36,plain,(
    r2_hidden(sK2,k2_relset_1(sK0,sK1,sK3)) ),
    inference(cnf_transformation,[],[f17])).

fof(f102,plain,(
    spl12_3 ),
    inference(avatar_split_clause,[],[f35,f99])).

fof(f35,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f17])).

fof(f97,plain,(
    spl12_2 ),
    inference(avatar_split_clause,[],[f34,f94])).

fof(f34,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f90,plain,(
    spl12_1 ),
    inference(avatar_split_clause,[],[f33,f87])).

fof(f33,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:17:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (26686)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.47  % (26684)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.49  % (26685)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.49  % (26692)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.49  % (26697)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.49  % (26688)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.49  % (26696)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.50  % (26687)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.50  % (26693)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (26695)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.50  % (26684)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f629,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f90,f97,f102,f107,f123,f131,f141,f151,f161,f171,f230,f265,f272,f302,f368,f381,f406,f415,f439,f460,f520,f534,f594,f605,f625,f628])).
% 0.21/0.50  fof(f628,plain,(
% 0.21/0.50    k1_xboole_0 != sK1 | k1_relset_1(sK0,sK1,sK3) != k1_relat_1(sK3) | sK0 != k1_relset_1(sK0,k1_xboole_0,sK3) | r2_hidden(sK6(sK3,sK2),sK0) | ~r2_hidden(sK6(sK3,sK2),k1_relat_1(sK3))),
% 0.21/0.50    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.50  fof(f625,plain,(
% 0.21/0.50    ~spl12_48 | spl12_56 | ~spl12_58),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f624])).
% 0.21/0.50  fof(f624,plain,(
% 0.21/0.50    $false | (~spl12_48 | spl12_56 | ~spl12_58)),
% 0.21/0.50    inference(subsumption_resolution,[],[f623,f519])).
% 0.21/0.50  fof(f519,plain,(
% 0.21/0.50    v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | ~spl12_48),
% 0.21/0.50    inference(avatar_component_clause,[],[f517])).
% 0.21/0.50  fof(f517,plain,(
% 0.21/0.50    spl12_48 <=> v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl12_48])])).
% 0.21/0.50  fof(f623,plain,(
% 0.21/0.50    ~v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | (spl12_56 | ~spl12_58)),
% 0.21/0.50    inference(subsumption_resolution,[],[f611,f593])).
% 0.21/0.50  fof(f593,plain,(
% 0.21/0.50    k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) | spl12_56),
% 0.21/0.50    inference(avatar_component_clause,[],[f591])).
% 0.21/0.50  fof(f591,plain,(
% 0.21/0.50    spl12_56 <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl12_56])])).
% 0.21/0.50  fof(f611,plain,(
% 0.21/0.50    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) | ~v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | ~spl12_58),
% 0.21/0.50    inference(resolution,[],[f604,f79])).
% 0.21/0.50  fof(f79,plain,(
% 0.21/0.50    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1)) )),
% 0.21/0.50    inference(equality_resolution,[],[f63])).
% 0.21/0.50  fof(f63,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f29])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(flattening,[],[f28])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f13])).
% 0.21/0.50  fof(f13,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.50  fof(f604,plain,(
% 0.21/0.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~spl12_58),
% 0.21/0.50    inference(avatar_component_clause,[],[f602])).
% 0.21/0.50  fof(f602,plain,(
% 0.21/0.50    spl12_58 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl12_58])])).
% 0.21/0.50  fof(f605,plain,(
% 0.21/0.50    spl12_58 | ~spl12_42 | ~spl12_43),
% 0.21/0.50    inference(avatar_split_clause,[],[f500,f457,f436,f602])).
% 0.21/0.50  fof(f436,plain,(
% 0.21/0.50    spl12_42 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl12_42])])).
% 0.21/0.50  fof(f457,plain,(
% 0.21/0.50    spl12_43 <=> k1_xboole_0 = sK0),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl12_43])])).
% 0.21/0.50  fof(f500,plain,(
% 0.21/0.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl12_42 | ~spl12_43)),
% 0.21/0.50    inference(superposition,[],[f438,f459])).
% 0.21/0.50  fof(f459,plain,(
% 0.21/0.50    k1_xboole_0 = sK0 | ~spl12_43),
% 0.21/0.50    inference(avatar_component_clause,[],[f457])).
% 0.21/0.50  fof(f438,plain,(
% 0.21/0.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | ~spl12_42),
% 0.21/0.50    inference(avatar_component_clause,[],[f436])).
% 0.21/0.50  fof(f594,plain,(
% 0.21/0.50    ~spl12_56 | spl12_36 | ~spl12_43),
% 0.21/0.50    inference(avatar_split_clause,[],[f497,f457,f370,f591])).
% 0.21/0.50  fof(f370,plain,(
% 0.21/0.50    spl12_36 <=> sK0 = k1_relset_1(sK0,k1_xboole_0,sK3)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl12_36])])).
% 0.21/0.50  fof(f497,plain,(
% 0.21/0.50    k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) | (spl12_36 | ~spl12_43)),
% 0.21/0.50    inference(superposition,[],[f372,f459])).
% 0.21/0.50  fof(f372,plain,(
% 0.21/0.50    sK0 != k1_relset_1(sK0,k1_xboole_0,sK3) | spl12_36),
% 0.21/0.50    inference(avatar_component_clause,[],[f370])).
% 0.21/0.50  fof(f534,plain,(
% 0.21/0.50    spl12_50 | ~spl12_10),
% 0.21/0.50    inference(avatar_split_clause,[],[f163,f158,f531])).
% 0.21/0.50  fof(f531,plain,(
% 0.21/0.50    spl12_50 <=> r2_hidden(sK6(sK3,sK2),k1_relat_1(sK3))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl12_50])])).
% 0.21/0.50  fof(f158,plain,(
% 0.21/0.50    spl12_10 <=> sP5(sK2,sK3)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl12_10])])).
% 0.21/0.50  fof(f163,plain,(
% 0.21/0.50    r2_hidden(sK6(sK3,sK2),k1_relat_1(sK3)) | ~spl12_10),
% 0.21/0.50    inference(resolution,[],[f160,f46])).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    ( ! [X2,X0] : (~sP5(X2,X0) | r2_hidden(sK6(X0,X2),k1_relat_1(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(flattening,[],[f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).
% 0.21/0.50  fof(f160,plain,(
% 0.21/0.50    sP5(sK2,sK3) | ~spl12_10),
% 0.21/0.50    inference(avatar_component_clause,[],[f158])).
% 0.21/0.50  fof(f520,plain,(
% 0.21/0.50    spl12_48 | ~spl12_28 | ~spl12_43),
% 0.21/0.50    inference(avatar_split_clause,[],[f491,f457,f299,f517])).
% 0.21/0.50  fof(f299,plain,(
% 0.21/0.50    spl12_28 <=> v1_funct_2(sK3,sK0,k1_xboole_0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl12_28])])).
% 0.21/0.50  fof(f491,plain,(
% 0.21/0.50    v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | (~spl12_28 | ~spl12_43)),
% 0.21/0.50    inference(superposition,[],[f301,f459])).
% 0.21/0.50  fof(f301,plain,(
% 0.21/0.50    v1_funct_2(sK3,sK0,k1_xboole_0) | ~spl12_28),
% 0.21/0.50    inference(avatar_component_clause,[],[f299])).
% 0.21/0.50  fof(f460,plain,(
% 0.21/0.50    spl12_43 | spl12_13 | ~spl12_28 | ~spl12_42),
% 0.21/0.50    inference(avatar_split_clause,[],[f453,f436,f299,f182,f457])).
% 0.21/0.50  fof(f182,plain,(
% 0.21/0.50    spl12_13 <=> k1_xboole_0 = sK3),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl12_13])])).
% 0.21/0.50  fof(f453,plain,(
% 0.21/0.50    k1_xboole_0 = sK0 | (spl12_13 | ~spl12_28 | ~spl12_42)),
% 0.21/0.50    inference(subsumption_resolution,[],[f452,f301])).
% 0.21/0.50  fof(f452,plain,(
% 0.21/0.50    k1_xboole_0 = sK0 | ~v1_funct_2(sK3,sK0,k1_xboole_0) | (spl12_13 | ~spl12_42)),
% 0.21/0.50    inference(subsumption_resolution,[],[f441,f183])).
% 0.21/0.50  fof(f183,plain,(
% 0.21/0.50    k1_xboole_0 != sK3 | spl12_13),
% 0.21/0.50    inference(avatar_component_clause,[],[f182])).
% 0.21/0.50  fof(f441,plain,(
% 0.21/0.50    k1_xboole_0 = sK0 | k1_xboole_0 = sK3 | ~v1_funct_2(sK3,sK0,k1_xboole_0) | ~spl12_42),
% 0.21/0.50    inference(resolution,[],[f438,f81])).
% 0.21/0.50  fof(f81,plain,(
% 0.21/0.50    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | k1_xboole_0 = X0 | k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0)) )),
% 0.21/0.50    inference(equality_resolution,[],[f61])).
% 0.21/0.50  fof(f61,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X1 | k1_xboole_0 = X0 | k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f29])).
% 0.21/0.50  fof(f439,plain,(
% 0.21/0.50    spl12_42 | ~spl12_3 | ~spl12_22),
% 0.21/0.50    inference(avatar_split_clause,[],[f421,f262,f99,f436])).
% 0.21/0.50  fof(f99,plain,(
% 0.21/0.50    spl12_3 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl12_3])])).
% 0.21/0.50  fof(f262,plain,(
% 0.21/0.50    spl12_22 <=> k1_xboole_0 = sK1),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl12_22])])).
% 0.21/0.50  fof(f421,plain,(
% 0.21/0.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | (~spl12_3 | ~spl12_22)),
% 0.21/0.50    inference(superposition,[],[f101,f264])).
% 0.21/0.50  fof(f264,plain,(
% 0.21/0.50    k1_xboole_0 = sK1 | ~spl12_22),
% 0.21/0.50    inference(avatar_component_clause,[],[f262])).
% 0.21/0.50  fof(f101,plain,(
% 0.21/0.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl12_3),
% 0.21/0.50    inference(avatar_component_clause,[],[f99])).
% 0.21/0.50  fof(f415,plain,(
% 0.21/0.50    ~spl12_37 | ~spl12_39),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f414])).
% 0.21/0.50  fof(f414,plain,(
% 0.21/0.50    $false | (~spl12_37 | ~spl12_39)),
% 0.21/0.50    inference(subsumption_resolution,[],[f413,f380])).
% 0.21/0.50  fof(f380,plain,(
% 0.21/0.50    r2_hidden(sK6(sK3,sK2),sK0) | ~spl12_37),
% 0.21/0.50    inference(avatar_component_clause,[],[f378])).
% 0.21/0.50  fof(f378,plain,(
% 0.21/0.50    spl12_37 <=> r2_hidden(sK6(sK3,sK2),sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl12_37])])).
% 0.21/0.50  fof(f413,plain,(
% 0.21/0.50    ~r2_hidden(sK6(sK3,sK2),sK0) | ~spl12_39),
% 0.21/0.50    inference(trivial_inequality_removal,[],[f412])).
% 0.21/0.50  fof(f412,plain,(
% 0.21/0.50    sK2 != sK2 | ~r2_hidden(sK6(sK3,sK2),sK0) | ~spl12_39),
% 0.21/0.50    inference(superposition,[],[f32,f405])).
% 0.21/0.50  fof(f405,plain,(
% 0.21/0.50    sK2 = k1_funct_1(sK3,sK6(sK3,sK2)) | ~spl12_39),
% 0.21/0.50    inference(avatar_component_clause,[],[f403])).
% 0.21/0.50  fof(f403,plain,(
% 0.21/0.50    spl12_39 <=> sK2 = k1_funct_1(sK3,sK6(sK3,sK2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl12_39])])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ( ! [X4] : (sK2 != k1_funct_1(sK3,X4) | ~r2_hidden(X4,sK0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ? [X0,X1,X2,X3] : (! [X4] : (k1_funct_1(X3,X4) != X2 | ~r2_hidden(X4,X0)) & r2_hidden(X2,k2_relset_1(X0,X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.21/0.50    inference(flattening,[],[f16])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ? [X0,X1,X2,X3] : ((! [X4] : (k1_funct_1(X3,X4) != X2 | ~r2_hidden(X4,X0)) & r2_hidden(X2,k2_relset_1(X0,X1,X3))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.21/0.50    inference(ennf_transformation,[],[f15])).
% 0.21/0.50  fof(f15,negated_conjecture,(
% 0.21/0.50    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ~(! [X4] : ~(k1_funct_1(X3,X4) = X2 & r2_hidden(X4,X0)) & r2_hidden(X2,k2_relset_1(X0,X1,X3))))),
% 0.21/0.50    inference(negated_conjecture,[],[f14])).
% 0.21/0.50  fof(f14,conjecture,(
% 0.21/0.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ~(! [X4] : ~(k1_funct_1(X3,X4) = X2 & r2_hidden(X4,X0)) & r2_hidden(X2,k2_relset_1(X0,X1,X3))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_funct_2)).
% 0.21/0.50  fof(f406,plain,(
% 0.21/0.50    spl12_39 | ~spl12_10),
% 0.21/0.50    inference(avatar_split_clause,[],[f164,f158,f403])).
% 0.21/0.50  fof(f164,plain,(
% 0.21/0.50    sK2 = k1_funct_1(sK3,sK6(sK3,sK2)) | ~spl12_10),
% 0.21/0.50    inference(resolution,[],[f160,f47])).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    ( ! [X2,X0] : (~sP5(X2,X0) | k1_funct_1(X0,sK6(X0,X2)) = X2) )),
% 0.21/0.50    inference(cnf_transformation,[],[f20])).
% 0.21/0.50  fof(f381,plain,(
% 0.21/0.50    spl12_37 | ~spl12_10 | ~spl12_23),
% 0.21/0.50    inference(avatar_split_clause,[],[f363,f267,f158,f378])).
% 0.21/0.50  fof(f267,plain,(
% 0.21/0.50    spl12_23 <=> sK0 = k1_relat_1(sK3)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl12_23])])).
% 0.21/0.50  fof(f363,plain,(
% 0.21/0.50    r2_hidden(sK6(sK3,sK2),sK0) | (~spl12_10 | ~spl12_23)),
% 0.21/0.50    inference(forward_demodulation,[],[f163,f269])).
% 0.21/0.50  fof(f269,plain,(
% 0.21/0.50    sK0 = k1_relat_1(sK3) | ~spl12_23),
% 0.21/0.50    inference(avatar_component_clause,[],[f267])).
% 0.21/0.50  fof(f368,plain,(
% 0.21/0.50    ~spl12_9 | ~spl12_11 | ~spl12_18),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f367])).
% 0.21/0.50  fof(f367,plain,(
% 0.21/0.50    $false | (~spl12_9 | ~spl12_11 | ~spl12_18)),
% 0.21/0.50    inference(subsumption_resolution,[],[f366,f229])).
% 0.21/0.50  fof(f229,plain,(
% 0.21/0.50    r2_hidden(sK2,k1_xboole_0) | ~spl12_18),
% 0.21/0.50    inference(avatar_component_clause,[],[f227])).
% 0.21/0.50  fof(f227,plain,(
% 0.21/0.50    spl12_18 <=> r2_hidden(sK2,k1_xboole_0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl12_18])])).
% 0.21/0.50  fof(f366,plain,(
% 0.21/0.50    ~r2_hidden(sK2,k1_xboole_0) | (~spl12_9 | ~spl12_11)),
% 0.21/0.50    inference(superposition,[],[f173,f170])).
% 0.21/0.50  fof(f170,plain,(
% 0.21/0.50    k1_xboole_0 = k4_xboole_0(k1_tarski(sK2),k2_relat_1(sK3)) | ~spl12_11),
% 0.21/0.50    inference(avatar_component_clause,[],[f168])).
% 0.21/0.50  fof(f168,plain,(
% 0.21/0.50    spl12_11 <=> k1_xboole_0 = k4_xboole_0(k1_tarski(sK2),k2_relat_1(sK3))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl12_11])])).
% 0.21/0.50  fof(f173,plain,(
% 0.21/0.50    ( ! [X1] : (~r2_hidden(sK2,k4_xboole_0(X1,k2_relat_1(sK3)))) ) | ~spl12_9),
% 0.21/0.50    inference(resolution,[],[f154,f84])).
% 0.21/0.50  fof(f84,plain,(
% 0.21/0.50    ( ! [X0,X3,X1] : (sP9(X3,X1,X0) | ~r2_hidden(X3,k4_xboole_0(X0,X1))) )),
% 0.21/0.50    inference(equality_resolution,[],[f70])).
% 0.21/0.50  % (26701)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.50  fof(f70,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (sP9(X3,X1,X0) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.21/0.50    inference(cnf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.21/0.50  fof(f154,plain,(
% 0.21/0.50    ( ! [X0] : (~sP9(sK2,k2_relat_1(sK3),X0)) ) | ~spl12_9),
% 0.21/0.50    inference(resolution,[],[f150,f68])).
% 0.21/0.50  fof(f68,plain,(
% 0.21/0.50    ( ! [X0,X3,X1] : (~r2_hidden(X3,X1) | ~sP9(X3,X1,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f1])).
% 0.21/0.50  fof(f150,plain,(
% 0.21/0.50    r2_hidden(sK2,k2_relat_1(sK3)) | ~spl12_9),
% 0.21/0.50    inference(avatar_component_clause,[],[f148])).
% 0.21/0.50  fof(f148,plain,(
% 0.21/0.50    spl12_9 <=> r2_hidden(sK2,k2_relat_1(sK3))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl12_9])])).
% 0.21/0.50  fof(f302,plain,(
% 0.21/0.50    spl12_28 | ~spl12_2 | ~spl12_22),
% 0.21/0.50    inference(avatar_split_clause,[],[f289,f262,f94,f299])).
% 0.21/0.50  fof(f94,plain,(
% 0.21/0.50    spl12_2 <=> v1_funct_2(sK3,sK0,sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).
% 0.21/0.50  fof(f289,plain,(
% 0.21/0.50    v1_funct_2(sK3,sK0,k1_xboole_0) | (~spl12_2 | ~spl12_22)),
% 0.21/0.50    inference(superposition,[],[f96,f264])).
% 0.21/0.50  fof(f96,plain,(
% 0.21/0.50    v1_funct_2(sK3,sK0,sK1) | ~spl12_2),
% 0.21/0.50    inference(avatar_component_clause,[],[f94])).
% 0.21/0.50  fof(f272,plain,(
% 0.21/0.50    spl12_23 | ~spl12_6 | ~spl12_21),
% 0.21/0.50    inference(avatar_split_clause,[],[f270,f258,f128,f267])).
% 0.21/0.50  fof(f128,plain,(
% 0.21/0.50    spl12_6 <=> k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl12_6])])).
% 0.21/0.50  fof(f258,plain,(
% 0.21/0.50    spl12_21 <=> sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl12_21])])).
% 0.21/0.50  fof(f270,plain,(
% 0.21/0.50    sK0 = k1_relat_1(sK3) | (~spl12_6 | ~spl12_21)),
% 0.21/0.50    inference(superposition,[],[f260,f130])).
% 0.21/0.50  fof(f130,plain,(
% 0.21/0.50    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) | ~spl12_6),
% 0.21/0.50    inference(avatar_component_clause,[],[f128])).
% 0.21/0.50  fof(f260,plain,(
% 0.21/0.50    sK0 = k1_relset_1(sK0,sK1,sK3) | ~spl12_21),
% 0.21/0.50    inference(avatar_component_clause,[],[f258])).
% 0.21/0.50  fof(f265,plain,(
% 0.21/0.50    spl12_21 | spl12_22 | ~spl12_2 | ~spl12_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f118,f99,f94,f262,f258])).
% 0.21/0.50  fof(f118,plain,(
% 0.21/0.50    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3) | (~spl12_2 | ~spl12_3)),
% 0.21/0.50    inference(subsumption_resolution,[],[f112,f96])).
% 0.21/0.50  fof(f112,plain,(
% 0.21/0.50    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3) | ~v1_funct_2(sK3,sK0,sK1) | ~spl12_3),
% 0.21/0.50    inference(resolution,[],[f101,f65])).
% 0.21/0.50  fof(f65,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f29])).
% 0.21/0.50  fof(f230,plain,(
% 0.21/0.50    spl12_18 | ~spl12_9 | ~spl12_13),
% 0.21/0.50    inference(avatar_split_clause,[],[f222,f182,f148,f227])).
% 0.21/0.50  fof(f222,plain,(
% 0.21/0.50    r2_hidden(sK2,k1_xboole_0) | (~spl12_9 | ~spl12_13)),
% 0.21/0.50    inference(forward_demodulation,[],[f215,f38])).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.21/0.50    inference(cnf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.21/0.50  fof(f215,plain,(
% 0.21/0.50    r2_hidden(sK2,k2_relat_1(k1_xboole_0)) | (~spl12_9 | ~spl12_13)),
% 0.21/0.50    inference(superposition,[],[f150,f184])).
% 0.21/0.50  fof(f184,plain,(
% 0.21/0.50    k1_xboole_0 = sK3 | ~spl12_13),
% 0.21/0.50    inference(avatar_component_clause,[],[f182])).
% 0.21/0.50  fof(f171,plain,(
% 0.21/0.50    spl12_11 | ~spl12_4 | ~spl12_8),
% 0.21/0.50    inference(avatar_split_clause,[],[f166,f138,f104,f168])).
% 0.21/0.50  fof(f104,plain,(
% 0.21/0.50    spl12_4 <=> r2_hidden(sK2,k2_relset_1(sK0,sK1,sK3))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl12_4])])).
% 0.21/0.50  fof(f138,plain,(
% 0.21/0.50    spl12_8 <=> k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl12_8])])).
% 0.21/0.50  fof(f166,plain,(
% 0.21/0.50    k1_xboole_0 = k4_xboole_0(k1_tarski(sK2),k2_relat_1(sK3)) | (~spl12_4 | ~spl12_8)),
% 0.21/0.50    inference(forward_demodulation,[],[f125,f140])).
% 0.21/0.50  fof(f140,plain,(
% 0.21/0.50    k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) | ~spl12_8),
% 0.21/0.50    inference(avatar_component_clause,[],[f138])).
% 0.21/0.50  fof(f125,plain,(
% 0.21/0.50    k1_xboole_0 = k4_xboole_0(k1_tarski(sK2),k2_relset_1(sK0,sK1,sK3)) | ~spl12_4),
% 0.21/0.50    inference(resolution,[],[f106,f55])).
% 0.21/0.50  fof(f55,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 <=> r2_hidden(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l35_zfmisc_1)).
% 0.21/0.50  fof(f106,plain,(
% 0.21/0.50    r2_hidden(sK2,k2_relset_1(sK0,sK1,sK3)) | ~spl12_4),
% 0.21/0.50    inference(avatar_component_clause,[],[f104])).
% 0.21/0.50  fof(f161,plain,(
% 0.21/0.50    spl12_10 | ~spl12_1 | ~spl12_5 | ~spl12_9),
% 0.21/0.50    inference(avatar_split_clause,[],[f153,f148,f120,f87,f158])).
% 0.21/0.50  fof(f87,plain,(
% 0.21/0.50    spl12_1 <=> v1_funct_1(sK3)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).
% 0.21/0.50  fof(f120,plain,(
% 0.21/0.50    spl12_5 <=> v1_relat_1(sK3)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl12_5])])).
% 0.21/0.50  fof(f153,plain,(
% 0.21/0.50    sP5(sK2,sK3) | (~spl12_1 | ~spl12_5 | ~spl12_9)),
% 0.21/0.50    inference(resolution,[],[f150,f146])).
% 0.21/0.50  fof(f146,plain,(
% 0.21/0.50    ( ! [X2] : (~r2_hidden(X2,k2_relat_1(sK3)) | sP5(X2,sK3)) ) | (~spl12_1 | ~spl12_5)),
% 0.21/0.50    inference(subsumption_resolution,[],[f92,f122])).
% 0.21/0.50  fof(f122,plain,(
% 0.21/0.50    v1_relat_1(sK3) | ~spl12_5),
% 0.21/0.50    inference(avatar_component_clause,[],[f120])).
% 0.21/0.50  fof(f92,plain,(
% 0.21/0.50    ( ! [X2] : (~v1_relat_1(sK3) | sP5(X2,sK3) | ~r2_hidden(X2,k2_relat_1(sK3))) ) | ~spl12_1),
% 0.21/0.50    inference(resolution,[],[f89,f76])).
% 0.21/0.50  fof(f76,plain,(
% 0.21/0.50    ( ! [X2,X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | sP5(X2,X0) | ~r2_hidden(X2,k2_relat_1(X0))) )),
% 0.21/0.50    inference(equality_resolution,[],[f49])).
% 0.21/0.50  fof(f49,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | sP5(X2,X0) | ~r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 0.21/0.50    inference(cnf_transformation,[],[f20])).
% 0.21/0.50  fof(f89,plain,(
% 0.21/0.50    v1_funct_1(sK3) | ~spl12_1),
% 0.21/0.50    inference(avatar_component_clause,[],[f87])).
% 0.21/0.50  fof(f151,plain,(
% 0.21/0.50    spl12_9 | ~spl12_4 | ~spl12_8),
% 0.21/0.50    inference(avatar_split_clause,[],[f145,f138,f104,f148])).
% 0.21/0.50  fof(f145,plain,(
% 0.21/0.50    r2_hidden(sK2,k2_relat_1(sK3)) | (~spl12_4 | ~spl12_8)),
% 0.21/0.50    inference(superposition,[],[f106,f140])).
% 0.21/0.50  fof(f141,plain,(
% 0.21/0.50    spl12_8 | ~spl12_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f110,f99,f138])).
% 0.21/0.50  fof(f110,plain,(
% 0.21/0.50    k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) | ~spl12_3),
% 0.21/0.50    inference(resolution,[],[f101,f59])).
% 0.21/0.50  fof(f59,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f27])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f11])).
% 0.21/0.50  fof(f11,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.50  fof(f131,plain,(
% 0.21/0.50    spl12_6 | ~spl12_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f109,f99,f128])).
% 0.21/0.50  fof(f109,plain,(
% 0.21/0.50    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) | ~spl12_3),
% 0.21/0.50    inference(resolution,[],[f101,f58])).
% 0.21/0.50  fof(f58,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f26])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.50  fof(f123,plain,(
% 0.21/0.50    spl12_5 | ~spl12_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f108,f99,f120])).
% 0.21/0.50  fof(f108,plain,(
% 0.21/0.50    v1_relat_1(sK3) | ~spl12_3),
% 0.21/0.50    inference(resolution,[],[f101,f57])).
% 0.21/0.50  fof(f57,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f25])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.50  fof(f107,plain,(
% 0.21/0.50    spl12_4),
% 0.21/0.50    inference(avatar_split_clause,[],[f36,f104])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    r2_hidden(sK2,k2_relset_1(sK0,sK1,sK3))),
% 0.21/0.50    inference(cnf_transformation,[],[f17])).
% 0.21/0.50  fof(f102,plain,(
% 0.21/0.50    spl12_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f35,f99])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.50    inference(cnf_transformation,[],[f17])).
% 0.21/0.50  fof(f97,plain,(
% 0.21/0.50    spl12_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f34,f94])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    v1_funct_2(sK3,sK0,sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f17])).
% 0.21/0.50  fof(f90,plain,(
% 0.21/0.50    spl12_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f33,f87])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    v1_funct_1(sK3)),
% 0.21/0.50    inference(cnf_transformation,[],[f17])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (26684)------------------------------
% 0.21/0.50  % (26684)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (26684)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (26684)Memory used [KB]: 11001
% 0.21/0.50  % (26684)Time elapsed: 0.074 s
% 0.21/0.50  % (26684)------------------------------
% 0.21/0.50  % (26684)------------------------------
% 0.21/0.50  % (26689)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.51  % (26690)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.51  % (26678)Success in time 0.144 s
%------------------------------------------------------------------------------
