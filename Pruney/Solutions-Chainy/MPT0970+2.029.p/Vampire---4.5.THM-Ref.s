%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:52 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 252 expanded)
%              Number of leaves         :   31 ( 107 expanded)
%              Depth                    :   12
%              Number of atoms          :  422 ( 796 expanded)
%              Number of equality atoms :  109 ( 227 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f365,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f55,f61,f65,f69,f85,f89,f95,f99,f103,f115,f139,f153,f167,f199,f203,f208,f224,f272,f275,f282,f293,f363,f364])).

fof(f364,plain,
    ( k1_xboole_0 != sK1
    | k1_relat_1(sK2) != k1_relset_1(sK0,sK1,sK2)
    | k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)
    | k1_xboole_0 != sK0
    | sK0 = k1_relat_1(sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f363,plain,
    ( spl6_43
    | ~ spl6_30
    | ~ spl6_32 ),
    inference(avatar_split_clause,[],[f357,f291,f280,f361])).

fof(f361,plain,
    ( spl6_43
  <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_43])])).

fof(f280,plain,
    ( spl6_30
  <=> v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f291,plain,
    ( spl6_32
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).

fof(f357,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)
    | ~ spl6_30
    | ~ spl6_32 ),
    inference(subsumption_resolution,[],[f347,f281])).

fof(f281,plain,
    ( v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ spl6_30 ),
    inference(avatar_component_clause,[],[f280])).

fof(f347,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)
    | ~ v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ spl6_32 ),
    inference(resolution,[],[f292,f47])).

fof(f47,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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

fof(f292,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl6_32 ),
    inference(avatar_component_clause,[],[f291])).

fof(f293,plain,
    ( spl6_32
    | ~ spl6_3
    | ~ spl6_12
    | ~ spl6_22 ),
    inference(avatar_split_clause,[],[f267,f197,f113,f63,f291])).

fof(f63,plain,
    ( spl6_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f113,plain,
    ( spl6_12
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f197,plain,
    ( spl6_22
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f267,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl6_3
    | ~ spl6_12
    | ~ spl6_22 ),
    inference(forward_demodulation,[],[f259,f114])).

fof(f114,plain,
    ( k1_xboole_0 = sK1
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f113])).

fof(f259,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ spl6_3
    | ~ spl6_22 ),
    inference(superposition,[],[f64,f198])).

fof(f198,plain,
    ( k1_xboole_0 = sK0
    | ~ spl6_22 ),
    inference(avatar_component_clause,[],[f197])).

fof(f64,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f63])).

fof(f282,plain,
    ( spl6_30
    | ~ spl6_2
    | ~ spl6_12
    | ~ spl6_22 ),
    inference(avatar_split_clause,[],[f266,f197,f113,f59,f280])).

fof(f59,plain,
    ( spl6_2
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f266,plain,
    ( v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ spl6_2
    | ~ spl6_12
    | ~ spl6_22 ),
    inference(forward_demodulation,[],[f258,f114])).

fof(f258,plain,
    ( v1_funct_2(sK2,k1_xboole_0,sK1)
    | ~ spl6_2
    | ~ spl6_22 ),
    inference(superposition,[],[f60,f198])).

fof(f60,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f59])).

fof(f275,plain,
    ( spl6_13
    | ~ spl6_8
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f130,f113,f97,f117])).

fof(f117,plain,
    ( spl6_13
  <=> k2_relat_1(sK2) = k2_relset_1(sK0,k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f97,plain,
    ( spl6_8
  <=> k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f130,plain,
    ( k2_relat_1(sK2) = k2_relset_1(sK0,k1_xboole_0,sK2)
    | ~ spl6_8
    | ~ spl6_12 ),
    inference(superposition,[],[f98,f114])).

fof(f98,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f97])).

fof(f272,plain,
    ( spl6_17
    | ~ spl6_3
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f125,f113,f63,f145])).

fof(f145,plain,
    ( spl6_17
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f125,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl6_3
    | ~ spl6_12 ),
    inference(superposition,[],[f64,f114])).

fof(f224,plain,
    ( ~ spl6_13
    | spl6_19
    | ~ spl6_21 ),
    inference(avatar_contradiction_clause,[],[f223])).

fof(f223,plain,
    ( $false
    | ~ spl6_13
    | spl6_19
    | ~ spl6_21 ),
    inference(subsumption_resolution,[],[f222,f41])).

fof(f41,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f222,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | ~ spl6_13
    | spl6_19
    | ~ spl6_21 ),
    inference(forward_demodulation,[],[f178,f195])).

fof(f195,plain,
    ( k1_xboole_0 = sK2
    | ~ spl6_21 ),
    inference(avatar_component_clause,[],[f194])).

fof(f194,plain,
    ( spl6_21
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f178,plain,
    ( k1_xboole_0 != k2_relat_1(sK2)
    | ~ spl6_13
    | spl6_19 ),
    inference(superposition,[],[f166,f118])).

fof(f118,plain,
    ( k2_relat_1(sK2) = k2_relset_1(sK0,k1_xboole_0,sK2)
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f117])).

fof(f166,plain,
    ( k1_xboole_0 != k2_relset_1(sK0,k1_xboole_0,sK2)
    | spl6_19 ),
    inference(avatar_component_clause,[],[f165])).

fof(f165,plain,
    ( spl6_19
  <=> k1_xboole_0 = k2_relset_1(sK0,k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f208,plain,
    ( ~ spl6_1
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_7
    | ~ spl6_18
    | ~ spl6_23 ),
    inference(avatar_contradiction_clause,[],[f207])).

fof(f207,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_7
    | ~ spl6_18
    | ~ spl6_23 ),
    inference(subsumption_resolution,[],[f206,f79])).

fof(f79,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(X0,sK4(sK1,sK2)),sK2)
    | ~ spl6_3
    | spl6_4 ),
    inference(subsumption_resolution,[],[f71,f68])).

fof(f68,plain,
    ( sK1 != k2_relset_1(sK0,sK1,sK2)
    | spl6_4 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl6_4
  <=> sK1 = k2_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f71,plain,
    ( ! [X0] :
        ( sK1 = k2_relset_1(sK0,sK1,sK2)
        | ~ r2_hidden(k4_tarski(X0,sK4(sK1,sK2)),sK2) )
    | ~ spl6_3 ),
    inference(resolution,[],[f64,f27])).

fof(f27,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = X1
      | ~ r2_hidden(k4_tarski(X4,sK4(X1,X2)),X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ? [X4] : r2_hidden(k4_tarski(X4,X3),X2)
            | ~ r2_hidden(X3,X1) )
      <=> k2_relset_1(X0,X1,X2) = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ! [X3] :
            ~ ( ! [X4] : ~ r2_hidden(k4_tarski(X4,X3),X2)
              & r2_hidden(X3,X1) )
      <=> k2_relset_1(X0,X1,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_relset_1)).

fof(f206,plain,
    ( r2_hidden(k4_tarski(sK3(sK4(sK1,sK2)),sK4(sK1,sK2)),sK2)
    | ~ spl6_1
    | ~ spl6_5
    | ~ spl6_7
    | ~ spl6_18
    | ~ spl6_23 ),
    inference(forward_demodulation,[],[f204,f202])).

fof(f202,plain,
    ( sK4(sK1,sK2) = k1_funct_1(sK2,sK3(sK4(sK1,sK2)))
    | ~ spl6_23 ),
    inference(avatar_component_clause,[],[f201])).

fof(f201,plain,
    ( spl6_23
  <=> sK4(sK1,sK2) = k1_funct_1(sK2,sK3(sK4(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f204,plain,
    ( r2_hidden(k4_tarski(sK3(sK4(sK1,sK2)),k1_funct_1(sK2,sK3(sK4(sK1,sK2)))),sK2)
    | ~ spl6_1
    | ~ spl6_5
    | ~ spl6_7
    | ~ spl6_18 ),
    inference(resolution,[],[f189,f94])).

fof(f94,plain,
    ( r2_hidden(sK3(sK4(sK1,sK2)),sK0)
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl6_7
  <=> r2_hidden(sK3(sK4(sK1,sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f189,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK0)
        | r2_hidden(k4_tarski(X1,k1_funct_1(sK2,X1)),sK2) )
    | ~ spl6_1
    | ~ spl6_5
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f188,f84])).

fof(f84,plain,
    ( v1_relat_1(sK2)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl6_5
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f188,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK0)
        | ~ v1_relat_1(sK2)
        | r2_hidden(k4_tarski(X1,k1_funct_1(sK2,X1)),sK2) )
    | ~ spl6_1
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f187,f54])).

fof(f54,plain,
    ( v1_funct_1(sK2)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl6_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f187,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK0)
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2)
        | r2_hidden(k4_tarski(X1,k1_funct_1(sK2,X1)),sK2) )
    | ~ spl6_18 ),
    inference(superposition,[],[f44,f150])).

fof(f150,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f149])).

fof(f149,plain,
    ( spl6_18
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(X1,k1_funct_1(X0,X1)),X0) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | r2_hidden(k4_tarski(X1,X2),X0)
      | k1_funct_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( ( ~ r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 ) )
          & ( r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_funct_1)).

fof(f203,plain,
    ( spl6_23
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f90,f87,f201])).

fof(f87,plain,
    ( spl6_6
  <=> r2_hidden(sK4(sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f90,plain,
    ( sK4(sK1,sK2) = k1_funct_1(sK2,sK3(sK4(sK1,sK2)))
    | ~ spl6_6 ),
    inference(resolution,[],[f88,f21])).

fof(f21,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK1)
      | k1_funct_1(sK2,sK3(X3)) = X3 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) != X1
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(X2,X4) = X3
              & r2_hidden(X4,X0) )
          | ~ r2_hidden(X3,X1) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) != X1
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(X2,X4) = X3
              & r2_hidden(X4,X0) )
          | ~ r2_hidden(X3,X1) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ! [X3] :
              ~ ( ! [X4] :
                    ~ ( k1_funct_1(X2,X4) = X3
                      & r2_hidden(X4,X0) )
                & r2_hidden(X3,X1) )
         => k2_relset_1(X0,X1,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ! [X3] :
            ~ ( ! [X4] :
                  ~ ( k1_funct_1(X2,X4) = X3
                    & r2_hidden(X4,X0) )
              & r2_hidden(X3,X1) )
       => k2_relset_1(X0,X1,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_funct_2)).

fof(f88,plain,
    ( r2_hidden(sK4(sK1,sK2),sK1)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f87])).

fof(f199,plain,
    ( spl6_21
    | spl6_22
    | ~ spl6_15
    | ~ spl6_17 ),
    inference(avatar_split_clause,[],[f177,f145,f137,f197,f194])).

fof(f137,plain,
    ( spl6_15
  <=> v1_funct_2(sK2,sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f177,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK2
    | ~ spl6_15
    | ~ spl6_17 ),
    inference(subsumption_resolution,[],[f168,f138])).

fof(f138,plain,
    ( v1_funct_2(sK2,sK0,k1_xboole_0)
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f137])).

fof(f168,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK2
    | ~ v1_funct_2(sK2,sK0,k1_xboole_0)
    | ~ spl6_17 ),
    inference(resolution,[],[f146,f49])).

fof(f49,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X1
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f146,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f145])).

fof(f167,plain,
    ( ~ spl6_19
    | spl6_4
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f126,f113,f67,f165])).

fof(f126,plain,
    ( k1_xboole_0 != k2_relset_1(sK0,k1_xboole_0,sK2)
    | spl6_4
    | ~ spl6_12 ),
    inference(superposition,[],[f68,f114])).

fof(f153,plain,
    ( spl6_18
    | ~ spl6_9
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f151,f110,f101,f149])).

fof(f101,plain,
    ( spl6_9
  <=> k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f110,plain,
    ( spl6_11
  <=> sK0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f151,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl6_9
    | ~ spl6_11 ),
    inference(superposition,[],[f111,f102])).

fof(f102,plain,
    ( k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f101])).

fof(f111,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f110])).

fof(f139,plain,
    ( spl6_15
    | ~ spl6_2
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f124,f113,f59,f137])).

fof(f124,plain,
    ( v1_funct_2(sK2,sK0,k1_xboole_0)
    | ~ spl6_2
    | ~ spl6_12 ),
    inference(superposition,[],[f60,f114])).

fof(f115,plain,
    ( spl6_11
    | spl6_12
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f80,f63,f59,f113,f110])).

fof(f80,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f75,f60])).

fof(f75,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ spl6_3 ),
    inference(resolution,[],[f64,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f103,plain,
    ( spl6_9
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f76,f63,f101])).

fof(f76,plain,
    ( k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)
    | ~ spl6_3 ),
    inference(resolution,[],[f64,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f99,plain,
    ( spl6_8
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f73,f63,f97])).

fof(f73,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)
    | ~ spl6_3 ),
    inference(resolution,[],[f64,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f95,plain,
    ( spl6_7
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f91,f87,f93])).

fof(f91,plain,
    ( r2_hidden(sK3(sK4(sK1,sK2)),sK0)
    | ~ spl6_6 ),
    inference(resolution,[],[f88,f20])).

fof(f20,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK1)
      | r2_hidden(sK3(X3),sK0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f89,plain,
    ( spl6_6
    | ~ spl6_3
    | spl6_4 ),
    inference(avatar_split_clause,[],[f78,f67,f63,f87])).

fof(f78,plain,
    ( r2_hidden(sK4(sK1,sK2),sK1)
    | ~ spl6_3
    | spl6_4 ),
    inference(subsumption_resolution,[],[f70,f68])).

fof(f70,plain,
    ( sK1 = k2_relset_1(sK0,sK1,sK2)
    | r2_hidden(sK4(sK1,sK2),sK1)
    | ~ spl6_3 ),
    inference(resolution,[],[f64,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = X1
      | r2_hidden(sK4(X1,X2),X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f85,plain,
    ( spl6_5
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f77,f63,f83])).

fof(f77,plain,
    ( v1_relat_1(sK2)
    | ~ spl6_3 ),
    inference(resolution,[],[f64,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f69,plain,(
    ~ spl6_4 ),
    inference(avatar_split_clause,[],[f25,f67])).

fof(f25,plain,(
    sK1 != k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f11])).

fof(f65,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f24,f63])).

fof(f24,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f11])).

fof(f61,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f23,f59])).

fof(f23,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f55,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f22,f53])).

fof(f22,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:47:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (27140)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.47  % (27145)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.48  % (27140)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % (27142)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.48  % (27159)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.49  % (27158)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f365,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f55,f61,f65,f69,f85,f89,f95,f99,f103,f115,f139,f153,f167,f199,f203,f208,f224,f272,f275,f282,f293,f363,f364])).
% 0.21/0.49  fof(f364,plain,(
% 0.21/0.49    k1_xboole_0 != sK1 | k1_relat_1(sK2) != k1_relset_1(sK0,sK1,sK2) | k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) | k1_xboole_0 != sK0 | sK0 = k1_relat_1(sK2)),
% 0.21/0.49    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.49  fof(f363,plain,(
% 0.21/0.49    spl6_43 | ~spl6_30 | ~spl6_32),
% 0.21/0.49    inference(avatar_split_clause,[],[f357,f291,f280,f361])).
% 0.21/0.49  fof(f361,plain,(
% 0.21/0.49    spl6_43 <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_43])])).
% 0.21/0.49  fof(f280,plain,(
% 0.21/0.49    spl6_30 <=> v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).
% 0.21/0.49  fof(f291,plain,(
% 0.21/0.49    spl6_32 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).
% 0.21/0.49  fof(f357,plain,(
% 0.21/0.49    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) | (~spl6_30 | ~spl6_32)),
% 0.21/0.49    inference(subsumption_resolution,[],[f347,f281])).
% 0.21/0.49  fof(f281,plain,(
% 0.21/0.49    v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | ~spl6_30),
% 0.21/0.49    inference(avatar_component_clause,[],[f280])).
% 0.21/0.49  fof(f347,plain,(
% 0.21/0.49    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) | ~v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | ~spl6_32),
% 0.21/0.49    inference(resolution,[],[f292,f47])).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1)) )),
% 0.21/0.49    inference(equality_resolution,[],[f37])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(flattening,[],[f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.49  fof(f292,plain,(
% 0.21/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~spl6_32),
% 0.21/0.49    inference(avatar_component_clause,[],[f291])).
% 0.21/0.49  fof(f293,plain,(
% 0.21/0.49    spl6_32 | ~spl6_3 | ~spl6_12 | ~spl6_22),
% 0.21/0.49    inference(avatar_split_clause,[],[f267,f197,f113,f63,f291])).
% 0.21/0.49  fof(f63,plain,(
% 0.21/0.49    spl6_3 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.21/0.49  fof(f113,plain,(
% 0.21/0.49    spl6_12 <=> k1_xboole_0 = sK1),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.21/0.49  fof(f197,plain,(
% 0.21/0.49    spl6_22 <=> k1_xboole_0 = sK0),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).
% 0.21/0.49  fof(f267,plain,(
% 0.21/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl6_3 | ~spl6_12 | ~spl6_22)),
% 0.21/0.49    inference(forward_demodulation,[],[f259,f114])).
% 0.21/0.49  fof(f114,plain,(
% 0.21/0.49    k1_xboole_0 = sK1 | ~spl6_12),
% 0.21/0.49    inference(avatar_component_clause,[],[f113])).
% 0.21/0.49  fof(f259,plain,(
% 0.21/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) | (~spl6_3 | ~spl6_22)),
% 0.21/0.49    inference(superposition,[],[f64,f198])).
% 0.21/0.49  fof(f198,plain,(
% 0.21/0.49    k1_xboole_0 = sK0 | ~spl6_22),
% 0.21/0.49    inference(avatar_component_clause,[],[f197])).
% 0.21/0.49  fof(f64,plain,(
% 0.21/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl6_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f63])).
% 0.21/0.49  fof(f282,plain,(
% 0.21/0.49    spl6_30 | ~spl6_2 | ~spl6_12 | ~spl6_22),
% 0.21/0.49    inference(avatar_split_clause,[],[f266,f197,f113,f59,f280])).
% 0.21/0.49  fof(f59,plain,(
% 0.21/0.49    spl6_2 <=> v1_funct_2(sK2,sK0,sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.21/0.49  fof(f266,plain,(
% 0.21/0.49    v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | (~spl6_2 | ~spl6_12 | ~spl6_22)),
% 0.21/0.49    inference(forward_demodulation,[],[f258,f114])).
% 0.21/0.49  fof(f258,plain,(
% 0.21/0.49    v1_funct_2(sK2,k1_xboole_0,sK1) | (~spl6_2 | ~spl6_22)),
% 0.21/0.49    inference(superposition,[],[f60,f198])).
% 0.21/0.49  fof(f60,plain,(
% 0.21/0.49    v1_funct_2(sK2,sK0,sK1) | ~spl6_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f59])).
% 0.21/0.49  fof(f275,plain,(
% 0.21/0.49    spl6_13 | ~spl6_8 | ~spl6_12),
% 0.21/0.49    inference(avatar_split_clause,[],[f130,f113,f97,f117])).
% 0.21/0.49  fof(f117,plain,(
% 0.21/0.49    spl6_13 <=> k2_relat_1(sK2) = k2_relset_1(sK0,k1_xboole_0,sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 0.21/0.49  fof(f97,plain,(
% 0.21/0.49    spl6_8 <=> k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.21/0.49  fof(f130,plain,(
% 0.21/0.49    k2_relat_1(sK2) = k2_relset_1(sK0,k1_xboole_0,sK2) | (~spl6_8 | ~spl6_12)),
% 0.21/0.49    inference(superposition,[],[f98,f114])).
% 0.21/0.49  fof(f98,plain,(
% 0.21/0.49    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) | ~spl6_8),
% 0.21/0.49    inference(avatar_component_clause,[],[f97])).
% 0.21/0.49  fof(f272,plain,(
% 0.21/0.49    spl6_17 | ~spl6_3 | ~spl6_12),
% 0.21/0.49    inference(avatar_split_clause,[],[f125,f113,f63,f145])).
% 0.21/0.49  fof(f145,plain,(
% 0.21/0.49    spl6_17 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 0.21/0.49  fof(f125,plain,(
% 0.21/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | (~spl6_3 | ~spl6_12)),
% 0.21/0.49    inference(superposition,[],[f64,f114])).
% 0.21/0.49  fof(f224,plain,(
% 0.21/0.49    ~spl6_13 | spl6_19 | ~spl6_21),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f223])).
% 0.21/0.49  fof(f223,plain,(
% 0.21/0.49    $false | (~spl6_13 | spl6_19 | ~spl6_21)),
% 0.21/0.49    inference(subsumption_resolution,[],[f222,f41])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.21/0.49    inference(cnf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.21/0.49  fof(f222,plain,(
% 0.21/0.49    k1_xboole_0 != k2_relat_1(k1_xboole_0) | (~spl6_13 | spl6_19 | ~spl6_21)),
% 0.21/0.49    inference(forward_demodulation,[],[f178,f195])).
% 0.21/0.49  fof(f195,plain,(
% 0.21/0.49    k1_xboole_0 = sK2 | ~spl6_21),
% 0.21/0.49    inference(avatar_component_clause,[],[f194])).
% 0.21/0.49  fof(f194,plain,(
% 0.21/0.49    spl6_21 <=> k1_xboole_0 = sK2),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).
% 0.21/0.49  fof(f178,plain,(
% 0.21/0.49    k1_xboole_0 != k2_relat_1(sK2) | (~spl6_13 | spl6_19)),
% 0.21/0.49    inference(superposition,[],[f166,f118])).
% 0.21/0.49  fof(f118,plain,(
% 0.21/0.49    k2_relat_1(sK2) = k2_relset_1(sK0,k1_xboole_0,sK2) | ~spl6_13),
% 0.21/0.49    inference(avatar_component_clause,[],[f117])).
% 0.21/0.49  fof(f166,plain,(
% 0.21/0.49    k1_xboole_0 != k2_relset_1(sK0,k1_xboole_0,sK2) | spl6_19),
% 0.21/0.49    inference(avatar_component_clause,[],[f165])).
% 0.21/0.49  fof(f165,plain,(
% 0.21/0.49    spl6_19 <=> k1_xboole_0 = k2_relset_1(sK0,k1_xboole_0,sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).
% 0.21/0.49  fof(f208,plain,(
% 0.21/0.49    ~spl6_1 | ~spl6_3 | spl6_4 | ~spl6_5 | ~spl6_7 | ~spl6_18 | ~spl6_23),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f207])).
% 0.21/0.49  fof(f207,plain,(
% 0.21/0.49    $false | (~spl6_1 | ~spl6_3 | spl6_4 | ~spl6_5 | ~spl6_7 | ~spl6_18 | ~spl6_23)),
% 0.21/0.49    inference(subsumption_resolution,[],[f206,f79])).
% 0.21/0.49  fof(f79,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_hidden(k4_tarski(X0,sK4(sK1,sK2)),sK2)) ) | (~spl6_3 | spl6_4)),
% 0.21/0.49    inference(subsumption_resolution,[],[f71,f68])).
% 0.21/0.49  fof(f68,plain,(
% 0.21/0.49    sK1 != k2_relset_1(sK0,sK1,sK2) | spl6_4),
% 0.21/0.49    inference(avatar_component_clause,[],[f67])).
% 0.21/0.49  fof(f67,plain,(
% 0.21/0.49    spl6_4 <=> sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.21/0.49  fof(f71,plain,(
% 0.21/0.49    ( ! [X0] : (sK1 = k2_relset_1(sK0,sK1,sK2) | ~r2_hidden(k4_tarski(X0,sK4(sK1,sK2)),sK2)) ) | ~spl6_3),
% 0.21/0.49    inference(resolution,[],[f64,f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = X1 | ~r2_hidden(k4_tarski(X4,sK4(X1,X2)),X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((! [X3] : (? [X4] : r2_hidden(k4_tarski(X4,X3),X2) | ~r2_hidden(X3,X1)) <=> k2_relset_1(X0,X1,X2) = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (! [X3] : ~(! [X4] : ~r2_hidden(k4_tarski(X4,X3),X2) & r2_hidden(X3,X1)) <=> k2_relset_1(X0,X1,X2) = X1))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_relset_1)).
% 0.21/0.49  fof(f206,plain,(
% 0.21/0.49    r2_hidden(k4_tarski(sK3(sK4(sK1,sK2)),sK4(sK1,sK2)),sK2) | (~spl6_1 | ~spl6_5 | ~spl6_7 | ~spl6_18 | ~spl6_23)),
% 0.21/0.49    inference(forward_demodulation,[],[f204,f202])).
% 0.21/0.49  fof(f202,plain,(
% 0.21/0.49    sK4(sK1,sK2) = k1_funct_1(sK2,sK3(sK4(sK1,sK2))) | ~spl6_23),
% 0.21/0.49    inference(avatar_component_clause,[],[f201])).
% 0.21/0.49  fof(f201,plain,(
% 0.21/0.49    spl6_23 <=> sK4(sK1,sK2) = k1_funct_1(sK2,sK3(sK4(sK1,sK2)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).
% 0.21/0.49  fof(f204,plain,(
% 0.21/0.49    r2_hidden(k4_tarski(sK3(sK4(sK1,sK2)),k1_funct_1(sK2,sK3(sK4(sK1,sK2)))),sK2) | (~spl6_1 | ~spl6_5 | ~spl6_7 | ~spl6_18)),
% 0.21/0.49    inference(resolution,[],[f189,f94])).
% 0.21/0.49  fof(f94,plain,(
% 0.21/0.49    r2_hidden(sK3(sK4(sK1,sK2)),sK0) | ~spl6_7),
% 0.21/0.49    inference(avatar_component_clause,[],[f93])).
% 0.21/0.49  fof(f93,plain,(
% 0.21/0.49    spl6_7 <=> r2_hidden(sK3(sK4(sK1,sK2)),sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.21/0.49  fof(f189,plain,(
% 0.21/0.49    ( ! [X1] : (~r2_hidden(X1,sK0) | r2_hidden(k4_tarski(X1,k1_funct_1(sK2,X1)),sK2)) ) | (~spl6_1 | ~spl6_5 | ~spl6_18)),
% 0.21/0.49    inference(subsumption_resolution,[],[f188,f84])).
% 0.21/0.49  fof(f84,plain,(
% 0.21/0.49    v1_relat_1(sK2) | ~spl6_5),
% 0.21/0.49    inference(avatar_component_clause,[],[f83])).
% 0.21/0.49  fof(f83,plain,(
% 0.21/0.49    spl6_5 <=> v1_relat_1(sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.21/0.49  fof(f188,plain,(
% 0.21/0.49    ( ! [X1] : (~r2_hidden(X1,sK0) | ~v1_relat_1(sK2) | r2_hidden(k4_tarski(X1,k1_funct_1(sK2,X1)),sK2)) ) | (~spl6_1 | ~spl6_18)),
% 0.21/0.49    inference(subsumption_resolution,[],[f187,f54])).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    v1_funct_1(sK2) | ~spl6_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f53])).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    spl6_1 <=> v1_funct_1(sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.21/0.49  fof(f187,plain,(
% 0.21/0.49    ( ! [X1] : (~r2_hidden(X1,sK0) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | r2_hidden(k4_tarski(X1,k1_funct_1(sK2,X1)),sK2)) ) | ~spl6_18),
% 0.21/0.49    inference(superposition,[],[f44,f150])).
% 0.21/0.49  fof(f150,plain,(
% 0.21/0.49    sK0 = k1_relat_1(sK2) | ~spl6_18),
% 0.21/0.49    inference(avatar_component_clause,[],[f149])).
% 0.21/0.49  fof(f149,plain,(
% 0.21/0.49    spl6_18 <=> sK0 = k1_relat_1(sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | r2_hidden(k4_tarski(X1,k1_funct_1(X0,X1)),X0)) )),
% 0.21/0.49    inference(equality_resolution,[],[f33])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~r2_hidden(X1,k1_relat_1(X0)) | r2_hidden(k4_tarski(X1,X2),X0) | k1_funct_1(X0,X1) != X2) )),
% 0.21/0.49    inference(cnf_transformation,[],[f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(flattening,[],[f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : ((~r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2)) & (r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_funct_1)).
% 0.21/0.49  fof(f203,plain,(
% 0.21/0.49    spl6_23 | ~spl6_6),
% 0.21/0.49    inference(avatar_split_clause,[],[f90,f87,f201])).
% 0.21/0.49  fof(f87,plain,(
% 0.21/0.49    spl6_6 <=> r2_hidden(sK4(sK1,sK2),sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.21/0.49  fof(f90,plain,(
% 0.21/0.49    sK4(sK1,sK2) = k1_funct_1(sK2,sK3(sK4(sK1,sK2))) | ~spl6_6),
% 0.21/0.49    inference(resolution,[],[f88,f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ( ! [X3] : (~r2_hidden(X3,sK1) | k1_funct_1(sK2,sK3(X3)) = X3) )),
% 0.21/0.49    inference(cnf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.21/0.49    inference(flattening,[],[f10])).
% 0.21/0.49  fof(f10,plain,(
% 0.21/0.49    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.21/0.49    inference(ennf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,negated_conjecture,(
% 0.21/0.49    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 0.21/0.49    inference(negated_conjecture,[],[f8])).
% 0.21/0.49  fof(f8,conjecture,(
% 0.21/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_funct_2)).
% 0.21/0.49  fof(f88,plain,(
% 0.21/0.49    r2_hidden(sK4(sK1,sK2),sK1) | ~spl6_6),
% 0.21/0.49    inference(avatar_component_clause,[],[f87])).
% 0.21/0.49  fof(f199,plain,(
% 0.21/0.49    spl6_21 | spl6_22 | ~spl6_15 | ~spl6_17),
% 0.21/0.49    inference(avatar_split_clause,[],[f177,f145,f137,f197,f194])).
% 0.21/0.49  fof(f137,plain,(
% 0.21/0.49    spl6_15 <=> v1_funct_2(sK2,sK0,k1_xboole_0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 0.21/0.49  fof(f177,plain,(
% 0.21/0.49    k1_xboole_0 = sK0 | k1_xboole_0 = sK2 | (~spl6_15 | ~spl6_17)),
% 0.21/0.49    inference(subsumption_resolution,[],[f168,f138])).
% 0.21/0.49  fof(f138,plain,(
% 0.21/0.49    v1_funct_2(sK2,sK0,k1_xboole_0) | ~spl6_15),
% 0.21/0.49    inference(avatar_component_clause,[],[f137])).
% 0.21/0.49  fof(f168,plain,(
% 0.21/0.49    k1_xboole_0 = sK0 | k1_xboole_0 = sK2 | ~v1_funct_2(sK2,sK0,k1_xboole_0) | ~spl6_17),
% 0.21/0.49    inference(resolution,[],[f146,f49])).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | k1_xboole_0 = X0 | k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0)) )),
% 0.21/0.49    inference(equality_resolution,[],[f35])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X1 | k1_xboole_0 = X0 | k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f146,plain,(
% 0.21/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | ~spl6_17),
% 0.21/0.49    inference(avatar_component_clause,[],[f145])).
% 0.21/0.49  fof(f167,plain,(
% 0.21/0.49    ~spl6_19 | spl6_4 | ~spl6_12),
% 0.21/0.49    inference(avatar_split_clause,[],[f126,f113,f67,f165])).
% 0.21/0.49  fof(f126,plain,(
% 0.21/0.49    k1_xboole_0 != k2_relset_1(sK0,k1_xboole_0,sK2) | (spl6_4 | ~spl6_12)),
% 0.21/0.49    inference(superposition,[],[f68,f114])).
% 0.21/0.49  fof(f153,plain,(
% 0.21/0.49    spl6_18 | ~spl6_9 | ~spl6_11),
% 0.21/0.49    inference(avatar_split_clause,[],[f151,f110,f101,f149])).
% 0.21/0.49  fof(f101,plain,(
% 0.21/0.49    spl6_9 <=> k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.21/0.49  fof(f110,plain,(
% 0.21/0.49    spl6_11 <=> sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.21/0.49  fof(f151,plain,(
% 0.21/0.49    sK0 = k1_relat_1(sK2) | (~spl6_9 | ~spl6_11)),
% 0.21/0.49    inference(superposition,[],[f111,f102])).
% 0.21/0.49  fof(f102,plain,(
% 0.21/0.49    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) | ~spl6_9),
% 0.21/0.49    inference(avatar_component_clause,[],[f101])).
% 0.21/0.49  fof(f111,plain,(
% 0.21/0.49    sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl6_11),
% 0.21/0.49    inference(avatar_component_clause,[],[f110])).
% 0.21/0.49  fof(f139,plain,(
% 0.21/0.49    spl6_15 | ~spl6_2 | ~spl6_12),
% 0.21/0.49    inference(avatar_split_clause,[],[f124,f113,f59,f137])).
% 0.21/0.49  fof(f124,plain,(
% 0.21/0.49    v1_funct_2(sK2,sK0,k1_xboole_0) | (~spl6_2 | ~spl6_12)),
% 0.21/0.49    inference(superposition,[],[f60,f114])).
% 0.21/0.49  fof(f115,plain,(
% 0.21/0.49    spl6_11 | spl6_12 | ~spl6_2 | ~spl6_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f80,f63,f59,f113,f110])).
% 0.21/0.49  fof(f80,plain,(
% 0.21/0.49    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | (~spl6_2 | ~spl6_3)),
% 0.21/0.49    inference(subsumption_resolution,[],[f75,f60])).
% 0.21/0.49  fof(f75,plain,(
% 0.21/0.49    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | ~v1_funct_2(sK2,sK0,sK1) | ~spl6_3),
% 0.21/0.49    inference(resolution,[],[f64,f39])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f103,plain,(
% 0.21/0.49    spl6_9 | ~spl6_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f76,f63,f101])).
% 0.21/0.49  fof(f76,plain,(
% 0.21/0.49    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) | ~spl6_3),
% 0.21/0.49    inference(resolution,[],[f64,f42])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.49  fof(f99,plain,(
% 0.21/0.49    spl6_8 | ~spl6_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f73,f63,f97])).
% 0.21/0.49  fof(f73,plain,(
% 0.21/0.49    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) | ~spl6_3),
% 0.21/0.49    inference(resolution,[],[f64,f29])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.49  fof(f95,plain,(
% 0.21/0.49    spl6_7 | ~spl6_6),
% 0.21/0.49    inference(avatar_split_clause,[],[f91,f87,f93])).
% 0.21/0.49  fof(f91,plain,(
% 0.21/0.49    r2_hidden(sK3(sK4(sK1,sK2)),sK0) | ~spl6_6),
% 0.21/0.49    inference(resolution,[],[f88,f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ( ! [X3] : (~r2_hidden(X3,sK1) | r2_hidden(sK3(X3),sK0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f11])).
% 0.21/0.49  fof(f89,plain,(
% 0.21/0.49    spl6_6 | ~spl6_3 | spl6_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f78,f67,f63,f87])).
% 0.21/0.49  fof(f78,plain,(
% 0.21/0.49    r2_hidden(sK4(sK1,sK2),sK1) | (~spl6_3 | spl6_4)),
% 0.21/0.49    inference(subsumption_resolution,[],[f70,f68])).
% 0.21/0.49  fof(f70,plain,(
% 0.21/0.49    sK1 = k2_relset_1(sK0,sK1,sK2) | r2_hidden(sK4(sK1,sK2),sK1) | ~spl6_3),
% 0.21/0.49    inference(resolution,[],[f64,f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = X1 | r2_hidden(sK4(X1,X2),X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f12])).
% 0.21/0.49  fof(f85,plain,(
% 0.21/0.49    spl6_5 | ~spl6_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f77,f63,f83])).
% 0.21/0.49  fof(f77,plain,(
% 0.21/0.49    v1_relat_1(sK2) | ~spl6_3),
% 0.21/0.49    inference(resolution,[],[f64,f43])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.49  fof(f69,plain,(
% 0.21/0.49    ~spl6_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f25,f67])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    sK1 != k2_relset_1(sK0,sK1,sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f11])).
% 0.21/0.49  fof(f65,plain,(
% 0.21/0.49    spl6_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f24,f63])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.49    inference(cnf_transformation,[],[f11])).
% 0.21/0.49  fof(f61,plain,(
% 0.21/0.49    spl6_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f23,f59])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    v1_funct_2(sK2,sK0,sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f11])).
% 0.21/0.49  fof(f55,plain,(
% 0.21/0.49    spl6_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f22,f53])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    v1_funct_1(sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f11])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (27140)------------------------------
% 0.21/0.49  % (27140)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (27140)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (27140)Memory used [KB]: 6396
% 0.21/0.49  % (27140)Time elapsed: 0.063 s
% 0.21/0.49  % (27140)------------------------------
% 0.21/0.49  % (27140)------------------------------
% 0.21/0.49  % (27131)Success in time 0.129 s
%------------------------------------------------------------------------------
