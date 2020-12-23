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
% DateTime   : Thu Dec  3 13:00:58 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 163 expanded)
%              Number of leaves         :   22 (  62 expanded)
%              Depth                    :   11
%              Number of atoms          :  293 ( 523 expanded)
%              Number of equality atoms :   61 ( 114 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f244,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f68,f78,f84,f89,f144,f153,f159,f164,f173,f187,f197,f217,f226,f243])).

fof(f243,plain,
    ( ~ spl6_3
    | spl6_4
    | ~ spl6_21 ),
    inference(avatar_contradiction_clause,[],[f242])).

fof(f242,plain,
    ( $false
    | ~ spl6_3
    | spl6_4
    | ~ spl6_21 ),
    inference(subsumption_resolution,[],[f240,f88])).

fof(f88,plain,
    ( sK1 != k2_relset_1(sK0,sK1,sK2)
    | spl6_4 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl6_4
  <=> sK1 = k2_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f240,plain,
    ( sK1 = k2_relset_1(sK0,sK1,sK2)
    | ~ spl6_3
    | ~ spl6_21 ),
    inference(resolution,[],[f229,f83])).

fof(f83,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl6_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f229,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
        | sK1 = k2_relset_1(X0,sK1,sK2) )
    | ~ spl6_21 ),
    inference(resolution,[],[f225,f53])).

fof(f53,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X4,sK4(X1,X2)),X2)
      | k2_relset_1(X0,X1,X2) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ? [X4] : r2_hidden(k4_tarski(X4,X3),X2)
            | ~ r2_hidden(X3,X1) )
      <=> k2_relset_1(X0,X1,X2) = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ! [X3] :
            ~ ( ! [X4] : ~ r2_hidden(k4_tarski(X4,X3),X2)
              & r2_hidden(X3,X1) )
      <=> k2_relset_1(X0,X1,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_relset_1)).

fof(f225,plain,
    ( r2_hidden(k4_tarski(sK3(sK4(sK1,sK2)),sK4(sK1,sK2)),sK2)
    | ~ spl6_21 ),
    inference(avatar_component_clause,[],[f223])).

fof(f223,plain,
    ( spl6_21
  <=> r2_hidden(k4_tarski(sK3(sK4(sK1,sK2)),sK4(sK1,sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f226,plain,
    ( spl6_21
    | ~ spl6_1
    | ~ spl6_10
    | ~ spl6_15
    | ~ spl6_18
    | ~ spl6_20 ),
    inference(avatar_split_clause,[],[f219,f214,f194,f161,f123,f65,f223])).

fof(f65,plain,
    ( spl6_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f123,plain,
    ( spl6_10
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f161,plain,
    ( spl6_15
  <=> r2_hidden(sK3(sK4(sK1,sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f194,plain,
    ( spl6_18
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f214,plain,
    ( spl6_20
  <=> sK4(sK1,sK2) = k1_funct_1(sK2,sK3(sK4(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f219,plain,
    ( r2_hidden(k4_tarski(sK3(sK4(sK1,sK2)),sK4(sK1,sK2)),sK2)
    | ~ spl6_1
    | ~ spl6_10
    | ~ spl6_15
    | ~ spl6_18
    | ~ spl6_20 ),
    inference(forward_demodulation,[],[f204,f216])).

fof(f216,plain,
    ( sK4(sK1,sK2) = k1_funct_1(sK2,sK3(sK4(sK1,sK2)))
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f214])).

fof(f204,plain,
    ( r2_hidden(k4_tarski(sK3(sK4(sK1,sK2)),k1_funct_1(sK2,sK3(sK4(sK1,sK2)))),sK2)
    | ~ spl6_1
    | ~ spl6_10
    | ~ spl6_15
    | ~ spl6_18 ),
    inference(resolution,[],[f201,f163])).

fof(f163,plain,
    ( r2_hidden(sK3(sK4(sK1,sK2)),sK0)
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f161])).

fof(f201,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,sK0)
        | r2_hidden(k4_tarski(X4,k1_funct_1(sK2,X4)),sK2) )
    | ~ spl6_1
    | ~ spl6_10
    | ~ spl6_18 ),
    inference(forward_demodulation,[],[f200,f196])).

fof(f196,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f194])).

fof(f200,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,k1_relat_1(sK2))
        | r2_hidden(k4_tarski(X4,k1_funct_1(sK2,X4)),sK2) )
    | ~ spl6_1
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f71,f124])).

fof(f124,plain,
    ( v1_relat_1(sK2)
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f123])).

fof(f71,plain,
    ( ! [X4] :
        ( ~ v1_relat_1(sK2)
        | ~ r2_hidden(X4,k1_relat_1(sK2))
        | r2_hidden(k4_tarski(X4,k1_funct_1(sK2,X4)),sK2) )
    | ~ spl6_1 ),
    inference(resolution,[],[f67,f63])).

fof(f63,plain,(
    ! [X2,X0] :
      ( ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2) ) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | k1_funct_1(X2,X0) != X1
      | r2_hidden(k4_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

fof(f67,plain,
    ( v1_funct_1(sK2)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f65])).

fof(f217,plain,
    ( spl6_20
    | ~ spl6_13 ),
    inference(avatar_split_clause,[],[f145,f141,f214])).

fof(f141,plain,
    ( spl6_13
  <=> r2_hidden(sK4(sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f145,plain,
    ( sK4(sK1,sK2) = k1_funct_1(sK2,sK3(sK4(sK1,sK2)))
    | ~ spl6_13 ),
    inference(resolution,[],[f143,f30])).

fof(f30,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK1)
      | k1_funct_1(sK2,sK3(X3)) = X3 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
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
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
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

fof(f143,plain,
    ( r2_hidden(sK4(sK1,sK2),sK1)
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f141])).

fof(f197,plain,
    ( spl6_18
    | ~ spl6_3
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f190,f166,f81,f194])).

fof(f166,plain,
    ( spl6_16
  <=> sK0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f190,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl6_3
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f188,f83])).

fof(f188,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_16 ),
    inference(superposition,[],[f168,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f168,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f166])).

fof(f187,plain,
    ( spl6_14
    | ~ spl6_17 ),
    inference(avatar_contradiction_clause,[],[f186])).

fof(f186,plain,
    ( $false
    | spl6_14
    | ~ spl6_17 ),
    inference(subsumption_resolution,[],[f185,f35])).

fof(f35,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f185,plain,
    ( ~ r1_tarski(k1_xboole_0,sK4(k1_xboole_0,sK2))
    | spl6_14
    | ~ spl6_17 ),
    inference(superposition,[],[f152,f172])).

fof(f172,plain,
    ( k1_xboole_0 = sK1
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f170])).

fof(f170,plain,
    ( spl6_17
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f152,plain,
    ( ~ r1_tarski(sK1,sK4(sK1,sK2))
    | spl6_14 ),
    inference(avatar_component_clause,[],[f150])).

fof(f150,plain,
    ( spl6_14
  <=> r1_tarski(sK1,sK4(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f173,plain,
    ( spl6_16
    | spl6_17
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f155,f81,f75,f170,f166])).

fof(f75,plain,
    ( spl6_2
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f155,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f79,f83])).

fof(f79,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_2 ),
    inference(resolution,[],[f77,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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

fof(f77,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f75])).

fof(f164,plain,
    ( spl6_15
    | ~ spl6_13 ),
    inference(avatar_split_clause,[],[f146,f141,f161])).

fof(f146,plain,
    ( r2_hidden(sK3(sK4(sK1,sK2)),sK0)
    | ~ spl6_13 ),
    inference(resolution,[],[f143,f29])).

fof(f29,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK1)
      | r2_hidden(sK3(X3),sK0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f159,plain,
    ( ~ spl6_3
    | spl6_10 ),
    inference(avatar_contradiction_clause,[],[f158])).

fof(f158,plain,
    ( $false
    | ~ spl6_3
    | spl6_10 ),
    inference(subsumption_resolution,[],[f156,f37])).

fof(f37,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f156,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | ~ spl6_3
    | spl6_10 ),
    inference(resolution,[],[f127,f83])).

fof(f127,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl6_10 ),
    inference(resolution,[],[f125,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f125,plain,
    ( ~ v1_relat_1(sK2)
    | spl6_10 ),
    inference(avatar_component_clause,[],[f123])).

fof(f153,plain,
    ( ~ spl6_14
    | ~ spl6_13 ),
    inference(avatar_split_clause,[],[f148,f141,f150])).

fof(f148,plain,
    ( ~ r1_tarski(sK1,sK4(sK1,sK2))
    | ~ spl6_13 ),
    inference(resolution,[],[f143,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f144,plain,
    ( spl6_13
    | ~ spl6_3
    | spl6_4 ),
    inference(avatar_split_clause,[],[f134,f86,f81,f141])).

fof(f134,plain,
    ( r2_hidden(sK4(sK1,sK2),sK1)
    | ~ spl6_3
    | spl6_4 ),
    inference(subsumption_resolution,[],[f90,f88])).

fof(f90,plain,
    ( sK1 = k2_relset_1(sK0,sK1,sK2)
    | r2_hidden(sK4(sK1,sK2),sK1)
    | ~ spl6_3 ),
    inference(resolution,[],[f83,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = X1
      | r2_hidden(sK4(X1,X2),X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f89,plain,(
    ~ spl6_4 ),
    inference(avatar_split_clause,[],[f34,f86])).

fof(f34,plain,(
    sK1 != k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f84,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f33,f81])).

fof(f33,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f16])).

fof(f78,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f32,f75])).

fof(f32,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f68,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f31,f65])).

fof(f31,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n018.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.21/0.35  % CPULimit   : 60
% 0.21/0.35  % WCLimit    : 600
% 0.21/0.35  % DateTime   : Tue Dec  1 16:58:42 EST 2020
% 0.21/0.35  % CPUTime    : 
% 0.22/0.49  % (11243)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.50  % (11243)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.51  % (11257)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f244,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(avatar_sat_refutation,[],[f68,f78,f84,f89,f144,f153,f159,f164,f173,f187,f197,f217,f226,f243])).
% 0.22/0.51  fof(f243,plain,(
% 0.22/0.51    ~spl6_3 | spl6_4 | ~spl6_21),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f242])).
% 0.22/0.51  fof(f242,plain,(
% 0.22/0.51    $false | (~spl6_3 | spl6_4 | ~spl6_21)),
% 0.22/0.51    inference(subsumption_resolution,[],[f240,f88])).
% 0.22/0.51  fof(f88,plain,(
% 0.22/0.51    sK1 != k2_relset_1(sK0,sK1,sK2) | spl6_4),
% 0.22/0.51    inference(avatar_component_clause,[],[f86])).
% 0.22/0.51  fof(f86,plain,(
% 0.22/0.51    spl6_4 <=> sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.22/0.51  fof(f240,plain,(
% 0.22/0.51    sK1 = k2_relset_1(sK0,sK1,sK2) | (~spl6_3 | ~spl6_21)),
% 0.22/0.51    inference(resolution,[],[f229,f83])).
% 0.22/0.51  fof(f83,plain,(
% 0.22/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl6_3),
% 0.22/0.51    inference(avatar_component_clause,[],[f81])).
% 0.22/0.51  fof(f81,plain,(
% 0.22/0.51    spl6_3 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.22/0.51  fof(f229,plain,(
% 0.22/0.51    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | sK1 = k2_relset_1(X0,sK1,sK2)) ) | ~spl6_21),
% 0.22/0.51    inference(resolution,[],[f225,f53])).
% 0.22/0.51  fof(f53,plain,(
% 0.22/0.51    ( ! [X4,X2,X0,X1] : (~r2_hidden(k4_tarski(X4,sK4(X1,X2)),X2) | k2_relset_1(X0,X1,X2) = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f26])).
% 0.22/0.51  fof(f26,plain,(
% 0.22/0.51    ! [X0,X1,X2] : ((! [X3] : (? [X4] : r2_hidden(k4_tarski(X4,X3),X2) | ~r2_hidden(X3,X1)) <=> k2_relset_1(X0,X1,X2) = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.51    inference(ennf_transformation,[],[f10])).
% 0.22/0.51  fof(f10,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (! [X3] : ~(! [X4] : ~r2_hidden(k4_tarski(X4,X3),X2) & r2_hidden(X3,X1)) <=> k2_relset_1(X0,X1,X2) = X1))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_relset_1)).
% 0.22/0.51  fof(f225,plain,(
% 0.22/0.51    r2_hidden(k4_tarski(sK3(sK4(sK1,sK2)),sK4(sK1,sK2)),sK2) | ~spl6_21),
% 0.22/0.51    inference(avatar_component_clause,[],[f223])).
% 0.22/0.51  fof(f223,plain,(
% 0.22/0.51    spl6_21 <=> r2_hidden(k4_tarski(sK3(sK4(sK1,sK2)),sK4(sK1,sK2)),sK2)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).
% 0.22/0.51  fof(f226,plain,(
% 0.22/0.51    spl6_21 | ~spl6_1 | ~spl6_10 | ~spl6_15 | ~spl6_18 | ~spl6_20),
% 0.22/0.51    inference(avatar_split_clause,[],[f219,f214,f194,f161,f123,f65,f223])).
% 0.22/0.51  fof(f65,plain,(
% 0.22/0.51    spl6_1 <=> v1_funct_1(sK2)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.22/0.51  fof(f123,plain,(
% 0.22/0.51    spl6_10 <=> v1_relat_1(sK2)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.22/0.51  fof(f161,plain,(
% 0.22/0.51    spl6_15 <=> r2_hidden(sK3(sK4(sK1,sK2)),sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 0.22/0.51  fof(f194,plain,(
% 0.22/0.51    spl6_18 <=> sK0 = k1_relat_1(sK2)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 0.22/0.51  fof(f214,plain,(
% 0.22/0.51    spl6_20 <=> sK4(sK1,sK2) = k1_funct_1(sK2,sK3(sK4(sK1,sK2)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).
% 0.22/0.51  fof(f219,plain,(
% 0.22/0.51    r2_hidden(k4_tarski(sK3(sK4(sK1,sK2)),sK4(sK1,sK2)),sK2) | (~spl6_1 | ~spl6_10 | ~spl6_15 | ~spl6_18 | ~spl6_20)),
% 0.22/0.51    inference(forward_demodulation,[],[f204,f216])).
% 0.22/0.51  fof(f216,plain,(
% 0.22/0.51    sK4(sK1,sK2) = k1_funct_1(sK2,sK3(sK4(sK1,sK2))) | ~spl6_20),
% 0.22/0.51    inference(avatar_component_clause,[],[f214])).
% 0.22/0.51  fof(f204,plain,(
% 0.22/0.51    r2_hidden(k4_tarski(sK3(sK4(sK1,sK2)),k1_funct_1(sK2,sK3(sK4(sK1,sK2)))),sK2) | (~spl6_1 | ~spl6_10 | ~spl6_15 | ~spl6_18)),
% 0.22/0.51    inference(resolution,[],[f201,f163])).
% 0.22/0.51  fof(f163,plain,(
% 0.22/0.51    r2_hidden(sK3(sK4(sK1,sK2)),sK0) | ~spl6_15),
% 0.22/0.51    inference(avatar_component_clause,[],[f161])).
% 0.22/0.51  fof(f201,plain,(
% 0.22/0.51    ( ! [X4] : (~r2_hidden(X4,sK0) | r2_hidden(k4_tarski(X4,k1_funct_1(sK2,X4)),sK2)) ) | (~spl6_1 | ~spl6_10 | ~spl6_18)),
% 0.22/0.51    inference(forward_demodulation,[],[f200,f196])).
% 0.22/0.51  fof(f196,plain,(
% 0.22/0.51    sK0 = k1_relat_1(sK2) | ~spl6_18),
% 0.22/0.51    inference(avatar_component_clause,[],[f194])).
% 0.22/0.51  fof(f200,plain,(
% 0.22/0.51    ( ! [X4] : (~r2_hidden(X4,k1_relat_1(sK2)) | r2_hidden(k4_tarski(X4,k1_funct_1(sK2,X4)),sK2)) ) | (~spl6_1 | ~spl6_10)),
% 0.22/0.51    inference(subsumption_resolution,[],[f71,f124])).
% 0.22/0.51  fof(f124,plain,(
% 0.22/0.51    v1_relat_1(sK2) | ~spl6_10),
% 0.22/0.51    inference(avatar_component_clause,[],[f123])).
% 0.22/0.51  fof(f71,plain,(
% 0.22/0.51    ( ! [X4] : (~v1_relat_1(sK2) | ~r2_hidden(X4,k1_relat_1(sK2)) | r2_hidden(k4_tarski(X4,k1_funct_1(sK2,X4)),sK2)) ) | ~spl6_1),
% 0.22/0.51    inference(resolution,[],[f67,f63])).
% 0.22/0.51  fof(f63,plain,(
% 0.22/0.51    ( ! [X2,X0] : (~v1_funct_1(X2) | ~v1_relat_1(X2) | ~r2_hidden(X0,k1_relat_1(X2)) | r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2)) )),
% 0.22/0.51    inference(equality_resolution,[],[f57])).
% 0.22/0.51  fof(f57,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~v1_funct_1(X2) | ~r2_hidden(X0,k1_relat_1(X2)) | k1_funct_1(X2,X0) != X1 | r2_hidden(k4_tarski(X0,X1),X2)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f28])).
% 0.22/0.51  fof(f28,plain,(
% 0.22/0.51    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.22/0.51    inference(flattening,[],[f27])).
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.22/0.51    inference(ennf_transformation,[],[f5])).
% 0.22/0.51  fof(f5,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).
% 0.22/0.51  fof(f67,plain,(
% 0.22/0.51    v1_funct_1(sK2) | ~spl6_1),
% 0.22/0.51    inference(avatar_component_clause,[],[f65])).
% 0.22/0.51  fof(f217,plain,(
% 0.22/0.51    spl6_20 | ~spl6_13),
% 0.22/0.51    inference(avatar_split_clause,[],[f145,f141,f214])).
% 0.22/0.51  fof(f141,plain,(
% 0.22/0.51    spl6_13 <=> r2_hidden(sK4(sK1,sK2),sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 0.22/0.51  fof(f145,plain,(
% 0.22/0.51    sK4(sK1,sK2) = k1_funct_1(sK2,sK3(sK4(sK1,sK2))) | ~spl6_13),
% 0.22/0.51    inference(resolution,[],[f143,f30])).
% 0.22/0.51  fof(f30,plain,(
% 0.22/0.51    ( ! [X3] : (~r2_hidden(X3,sK1) | k1_funct_1(sK2,sK3(X3)) = X3) )),
% 0.22/0.51    inference(cnf_transformation,[],[f16])).
% 0.22/0.51  fof(f16,plain,(
% 0.22/0.51    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.22/0.51    inference(flattening,[],[f15])).
% 0.22/0.51  fof(f15,plain,(
% 0.22/0.51    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.22/0.51    inference(ennf_transformation,[],[f14])).
% 0.22/0.51  fof(f14,negated_conjecture,(
% 0.22/0.51    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 0.22/0.51    inference(negated_conjecture,[],[f13])).
% 0.22/0.51  fof(f13,conjecture,(
% 0.22/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_funct_2)).
% 0.22/0.51  fof(f143,plain,(
% 0.22/0.51    r2_hidden(sK4(sK1,sK2),sK1) | ~spl6_13),
% 0.22/0.51    inference(avatar_component_clause,[],[f141])).
% 0.22/0.51  fof(f197,plain,(
% 0.22/0.51    spl6_18 | ~spl6_3 | ~spl6_16),
% 0.22/0.51    inference(avatar_split_clause,[],[f190,f166,f81,f194])).
% 0.22/0.51  fof(f166,plain,(
% 0.22/0.51    spl6_16 <=> sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 0.22/0.51  fof(f190,plain,(
% 0.22/0.51    sK0 = k1_relat_1(sK2) | (~spl6_3 | ~spl6_16)),
% 0.22/0.51    inference(subsumption_resolution,[],[f188,f83])).
% 0.22/0.51  fof(f188,plain,(
% 0.22/0.51    sK0 = k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl6_16),
% 0.22/0.51    inference(superposition,[],[f168,f43])).
% 0.22/0.51  fof(f43,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f21])).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.51    inference(ennf_transformation,[],[f8])).
% 0.22/0.51  fof(f8,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.51  fof(f168,plain,(
% 0.22/0.51    sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl6_16),
% 0.22/0.51    inference(avatar_component_clause,[],[f166])).
% 0.22/0.51  fof(f187,plain,(
% 0.22/0.51    spl6_14 | ~spl6_17),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f186])).
% 0.22/0.51  fof(f186,plain,(
% 0.22/0.51    $false | (spl6_14 | ~spl6_17)),
% 0.22/0.51    inference(subsumption_resolution,[],[f185,f35])).
% 0.22/0.51  fof(f35,plain,(
% 0.22/0.51    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.51  fof(f185,plain,(
% 0.22/0.51    ~r1_tarski(k1_xboole_0,sK4(k1_xboole_0,sK2)) | (spl6_14 | ~spl6_17)),
% 0.22/0.51    inference(superposition,[],[f152,f172])).
% 0.22/0.51  fof(f172,plain,(
% 0.22/0.51    k1_xboole_0 = sK1 | ~spl6_17),
% 0.22/0.51    inference(avatar_component_clause,[],[f170])).
% 0.22/0.51  fof(f170,plain,(
% 0.22/0.51    spl6_17 <=> k1_xboole_0 = sK1),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 0.22/0.51  fof(f152,plain,(
% 0.22/0.51    ~r1_tarski(sK1,sK4(sK1,sK2)) | spl6_14),
% 0.22/0.51    inference(avatar_component_clause,[],[f150])).
% 0.22/0.51  fof(f150,plain,(
% 0.22/0.51    spl6_14 <=> r1_tarski(sK1,sK4(sK1,sK2))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 0.22/0.51  fof(f173,plain,(
% 0.22/0.51    spl6_16 | spl6_17 | ~spl6_2 | ~spl6_3),
% 0.22/0.51    inference(avatar_split_clause,[],[f155,f81,f75,f170,f166])).
% 0.22/0.51  fof(f75,plain,(
% 0.22/0.51    spl6_2 <=> v1_funct_2(sK2,sK0,sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.22/0.51  fof(f155,plain,(
% 0.22/0.51    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | (~spl6_2 | ~spl6_3)),
% 0.22/0.51    inference(subsumption_resolution,[],[f79,f83])).
% 0.22/0.51  fof(f79,plain,(
% 0.22/0.51    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl6_2),
% 0.22/0.51    inference(resolution,[],[f77,f51])).
% 0.22/0.51  fof(f51,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f25])).
% 0.22/0.51  fof(f25,plain,(
% 0.22/0.51    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.51    inference(flattening,[],[f24])).
% 0.22/0.51  fof(f24,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.51    inference(ennf_transformation,[],[f11])).
% 0.22/0.51  fof(f11,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.22/0.51  fof(f77,plain,(
% 0.22/0.51    v1_funct_2(sK2,sK0,sK1) | ~spl6_2),
% 0.22/0.51    inference(avatar_component_clause,[],[f75])).
% 0.22/0.51  fof(f164,plain,(
% 0.22/0.51    spl6_15 | ~spl6_13),
% 0.22/0.51    inference(avatar_split_clause,[],[f146,f141,f161])).
% 0.22/0.51  fof(f146,plain,(
% 0.22/0.51    r2_hidden(sK3(sK4(sK1,sK2)),sK0) | ~spl6_13),
% 0.22/0.51    inference(resolution,[],[f143,f29])).
% 0.22/0.51  fof(f29,plain,(
% 0.22/0.51    ( ! [X3] : (~r2_hidden(X3,sK1) | r2_hidden(sK3(X3),sK0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f16])).
% 0.22/0.51  fof(f159,plain,(
% 0.22/0.51    ~spl6_3 | spl6_10),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f158])).
% 0.22/0.51  fof(f158,plain,(
% 0.22/0.51    $false | (~spl6_3 | spl6_10)),
% 0.22/0.51    inference(subsumption_resolution,[],[f156,f37])).
% 0.22/0.51  fof(f37,plain,(
% 0.22/0.51    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f4])).
% 0.22/0.51  fof(f4,axiom,(
% 0.22/0.51    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.22/0.51  fof(f156,plain,(
% 0.22/0.51    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | (~spl6_3 | spl6_10)),
% 0.22/0.51    inference(resolution,[],[f127,f83])).
% 0.22/0.51  fof(f127,plain,(
% 0.22/0.51    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl6_10),
% 0.22/0.51    inference(resolution,[],[f125,f36])).
% 0.22/0.51  fof(f36,plain,(
% 0.22/0.51    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f17])).
% 0.22/0.51  fof(f17,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f3])).
% 0.22/0.51  fof(f3,axiom,(
% 0.22/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.22/0.51  fof(f125,plain,(
% 0.22/0.51    ~v1_relat_1(sK2) | spl6_10),
% 0.22/0.51    inference(avatar_component_clause,[],[f123])).
% 0.22/0.51  fof(f153,plain,(
% 0.22/0.51    ~spl6_14 | ~spl6_13),
% 0.22/0.51    inference(avatar_split_clause,[],[f148,f141,f150])).
% 0.22/0.51  fof(f148,plain,(
% 0.22/0.51    ~r1_tarski(sK1,sK4(sK1,sK2)) | ~spl6_13),
% 0.22/0.51    inference(resolution,[],[f143,f42])).
% 0.22/0.51  fof(f42,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f20])).
% 0.22/0.51  fof(f20,plain,(
% 0.22/0.51    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.22/0.51    inference(ennf_transformation,[],[f6])).
% 0.22/0.51  fof(f6,axiom,(
% 0.22/0.51    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.22/0.51  fof(f144,plain,(
% 0.22/0.51    spl6_13 | ~spl6_3 | spl6_4),
% 0.22/0.51    inference(avatar_split_clause,[],[f134,f86,f81,f141])).
% 0.22/0.51  fof(f134,plain,(
% 0.22/0.51    r2_hidden(sK4(sK1,sK2),sK1) | (~spl6_3 | spl6_4)),
% 0.22/0.51    inference(subsumption_resolution,[],[f90,f88])).
% 0.22/0.51  fof(f90,plain,(
% 0.22/0.51    sK1 = k2_relset_1(sK0,sK1,sK2) | r2_hidden(sK4(sK1,sK2),sK1) | ~spl6_3),
% 0.22/0.51    inference(resolution,[],[f83,f52])).
% 0.22/0.51  fof(f52,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = X1 | r2_hidden(sK4(X1,X2),X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f26])).
% 0.22/0.51  fof(f89,plain,(
% 0.22/0.51    ~spl6_4),
% 0.22/0.51    inference(avatar_split_clause,[],[f34,f86])).
% 0.22/0.51  fof(f34,plain,(
% 0.22/0.51    sK1 != k2_relset_1(sK0,sK1,sK2)),
% 0.22/0.51    inference(cnf_transformation,[],[f16])).
% 0.22/0.51  fof(f84,plain,(
% 0.22/0.51    spl6_3),
% 0.22/0.51    inference(avatar_split_clause,[],[f33,f81])).
% 0.22/0.51  fof(f33,plain,(
% 0.22/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.51    inference(cnf_transformation,[],[f16])).
% 0.22/0.51  fof(f78,plain,(
% 0.22/0.51    spl6_2),
% 0.22/0.51    inference(avatar_split_clause,[],[f32,f75])).
% 0.22/0.51  fof(f32,plain,(
% 0.22/0.51    v1_funct_2(sK2,sK0,sK1)),
% 0.22/0.51    inference(cnf_transformation,[],[f16])).
% 0.22/0.51  fof(f68,plain,(
% 0.22/0.51    spl6_1),
% 0.22/0.51    inference(avatar_split_clause,[],[f31,f65])).
% 0.22/0.51  fof(f31,plain,(
% 0.22/0.51    v1_funct_1(sK2)),
% 0.22/0.51    inference(cnf_transformation,[],[f16])).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (11243)------------------------------
% 0.22/0.51  % (11243)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (11243)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (11243)Memory used [KB]: 10746
% 0.22/0.51  % (11243)Time elapsed: 0.081 s
% 0.22/0.51  % (11243)------------------------------
% 0.22/0.51  % (11243)------------------------------
% 0.22/0.51  % (11239)Success in time 0.15 s
%------------------------------------------------------------------------------
