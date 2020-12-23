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
% DateTime   : Thu Dec  3 13:00:51 EST 2020

% Result     : Theorem 1.42s
% Output     : Refutation 1.42s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 181 expanded)
%              Number of leaves         :   24 (  63 expanded)
%              Depth                    :   14
%              Number of atoms          :  320 ( 602 expanded)
%              Number of equality atoms :   63 ( 131 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f244,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f70,f79,f86,f91,f106,f113,f121,f129,f132,f145,f158,f175,f186,f243])).

fof(f243,plain,
    ( ~ spl8_3
    | ~ spl8_9
    | ~ spl8_12
    | spl8_14 ),
    inference(avatar_contradiction_clause,[],[f242])).

fof(f242,plain,
    ( $false
    | ~ spl8_3
    | ~ spl8_9
    | ~ spl8_12
    | spl8_14 ),
    inference(subsumption_resolution,[],[f241,f185])).

fof(f185,plain,
    ( ~ r1_tarski(sK1,k2_relat_1(sK2))
    | spl8_14 ),
    inference(avatar_component_clause,[],[f183])).

fof(f183,plain,
    ( spl8_14
  <=> r1_tarski(sK1,k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f241,plain,
    ( r1_tarski(sK1,k2_relat_1(sK2))
    | ~ spl8_3
    | ~ spl8_9
    | ~ spl8_12 ),
    inference(duplicate_literal_removal,[],[f239])).

fof(f239,plain,
    ( r1_tarski(sK1,k2_relat_1(sK2))
    | r1_tarski(sK1,k2_relat_1(sK2))
    | ~ spl8_3
    | ~ spl8_9
    | ~ spl8_12 ),
    inference(resolution,[],[f222,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f222,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK7(X0,k2_relat_1(sK2)),sK1)
        | r1_tarski(X0,k2_relat_1(sK2)) )
    | ~ spl8_3
    | ~ spl8_9
    | ~ spl8_12 ),
    inference(resolution,[],[f200,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK7(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f200,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k2_relat_1(sK2))
        | ~ r2_hidden(X0,sK1) )
    | ~ spl8_3
    | ~ spl8_9
    | ~ spl8_12 ),
    inference(resolution,[],[f194,f124])).

fof(f124,plain,
    ( ! [X0] :
        ( ~ sP5(X0,sK2)
        | r2_hidden(X0,k2_relat_1(sK2)) )
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl8_9
  <=> ! [X0] :
        ( ~ sP5(X0,sK2)
        | r2_hidden(X0,k2_relat_1(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f194,plain,
    ( ! [X0] :
        ( sP5(X0,sK2)
        | ~ r2_hidden(X0,sK1) )
    | ~ spl8_3
    | ~ spl8_12 ),
    inference(subsumption_resolution,[],[f192,f24])).

fof(f24,plain,(
    ! [X3] :
      ( r2_hidden(sK3(X3),sK0)
      | ~ r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f13,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
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
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
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

fof(f192,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3(X0),sK0)
        | sP5(X0,sK2)
        | ~ r2_hidden(X0,sK1) )
    | ~ spl8_3
    | ~ spl8_12 ),
    inference(backward_demodulation,[],[f107,f191])).

fof(f191,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl8_3
    | ~ spl8_12 ),
    inference(subsumption_resolution,[],[f189,f85])).

fof(f85,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl8_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f189,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl8_12 ),
    inference(superposition,[],[f153,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f153,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f151])).

fof(f151,plain,
    ( spl8_12
  <=> sK0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f107,plain,(
    ! [X0] :
      ( sP5(X0,sK2)
      | ~ r2_hidden(sK3(X0),k1_relat_1(sK2))
      | ~ r2_hidden(X0,sK1) ) ),
    inference(superposition,[],[f58,f25])).

fof(f25,plain,(
    ! [X3] :
      ( k1_funct_1(sK2,sK3(X3)) = X3
      | ~ r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f58,plain,(
    ! [X0,X3] :
      ( sP5(k1_funct_1(X0,X3),X0)
      | ~ r2_hidden(X3,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(X3,k1_relat_1(X0))
      | k1_funct_1(X0,X3) != X2
      | sP5(X2,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

fof(f186,plain,
    ( ~ spl8_14
    | spl8_6
    | ~ spl8_11 ),
    inference(avatar_split_clause,[],[f149,f142,f103,f183])).

fof(f103,plain,
    ( spl8_6
  <=> sK1 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f142,plain,
    ( spl8_11
  <=> r1_tarski(k2_relat_1(sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f149,plain,
    ( ~ r1_tarski(sK1,k2_relat_1(sK2))
    | spl8_6
    | ~ spl8_11 ),
    inference(subsumption_resolution,[],[f148,f105])).

fof(f105,plain,
    ( sK1 != k2_relat_1(sK2)
    | spl8_6 ),
    inference(avatar_component_clause,[],[f103])).

fof(f148,plain,
    ( ~ r1_tarski(sK1,k2_relat_1(sK2))
    | sK1 = k2_relat_1(sK2)
    | ~ spl8_11 ),
    inference(resolution,[],[f144,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f144,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1)
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f142])).

fof(f175,plain,
    ( spl8_6
    | ~ spl8_11
    | ~ spl8_13 ),
    inference(avatar_contradiction_clause,[],[f174])).

fof(f174,plain,
    ( $false
    | spl8_6
    | ~ spl8_11
    | ~ spl8_13 ),
    inference(subsumption_resolution,[],[f172,f30])).

fof(f30,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f172,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_relat_1(sK2))
    | spl8_6
    | ~ spl8_11
    | ~ spl8_13 ),
    inference(backward_demodulation,[],[f149,f157])).

fof(f157,plain,
    ( k1_xboole_0 = sK1
    | ~ spl8_13 ),
    inference(avatar_component_clause,[],[f155])).

fof(f155,plain,
    ( spl8_13
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f158,plain,
    ( spl8_12
    | spl8_13
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f81,f76,f155,f151])).

fof(f76,plain,
    ( spl8_2
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f81,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f80,f28])).

fof(f28,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f14])).

fof(f80,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl8_2 ),
    inference(resolution,[],[f78,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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

fof(f78,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f76])).

fof(f145,plain,
    ( spl8_11
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f139,f118,f142])).

fof(f118,plain,
    ( spl8_8
  <=> m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f139,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1)
    | ~ spl8_8 ),
    inference(resolution,[],[f120,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f120,plain,
    ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1))
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f118])).

fof(f132,plain,
    ( ~ spl8_3
    | spl8_10 ),
    inference(avatar_contradiction_clause,[],[f131])).

fof(f131,plain,
    ( $false
    | ~ spl8_3
    | spl8_10 ),
    inference(subsumption_resolution,[],[f85,f130])).

fof(f130,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl8_10 ),
    inference(resolution,[],[f128,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f128,plain,
    ( ~ v1_relat_1(sK2)
    | spl8_10 ),
    inference(avatar_component_clause,[],[f126])).

fof(f126,plain,
    ( spl8_10
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f129,plain,
    ( spl8_9
    | ~ spl8_10
    | ~ spl8_1 ),
    inference(avatar_split_clause,[],[f71,f67,f126,f123])).

fof(f67,plain,
    ( spl8_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f71,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(sK2)
        | ~ sP5(X0,sK2)
        | r2_hidden(X0,k2_relat_1(sK2)) )
    | ~ spl8_1 ),
    inference(resolution,[],[f69,f57])).

fof(f57,plain,(
    ! [X2,X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ sP5(X2,X0)
      | r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ sP5(X2,X0)
      | r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f69,plain,
    ( v1_funct_1(sK2)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f67])).

fof(f121,plain,
    ( spl8_8
    | ~ spl8_3
    | ~ spl8_7 ),
    inference(avatar_split_clause,[],[f116,f110,f83,f118])).

fof(f110,plain,
    ( spl8_7
  <=> m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f116,plain,
    ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1))
    | ~ spl8_3
    | ~ spl8_7 ),
    inference(subsumption_resolution,[],[f115,f85])).

fof(f115,plain,
    ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl8_7 ),
    inference(superposition,[],[f112,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f112,plain,
    ( m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK1))
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f110])).

fof(f113,plain,
    ( spl8_7
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f93,f83,f110])).

fof(f93,plain,
    ( m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK1))
    | ~ spl8_3 ),
    inference(resolution,[],[f85,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(f106,plain,
    ( ~ spl8_6
    | ~ spl8_3
    | spl8_4 ),
    inference(avatar_split_clause,[],[f101,f88,f83,f103])).

fof(f88,plain,
    ( spl8_4
  <=> sK1 = k2_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f101,plain,
    ( sK1 != k2_relat_1(sK2)
    | ~ spl8_3
    | spl8_4 ),
    inference(subsumption_resolution,[],[f100,f85])).

fof(f100,plain,
    ( sK1 != k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl8_4 ),
    inference(superposition,[],[f90,f48])).

fof(f90,plain,
    ( sK1 != k2_relset_1(sK0,sK1,sK2)
    | spl8_4 ),
    inference(avatar_component_clause,[],[f88])).

fof(f91,plain,(
    ~ spl8_4 ),
    inference(avatar_split_clause,[],[f29,f88])).

fof(f29,plain,(
    sK1 != k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f86,plain,(
    spl8_3 ),
    inference(avatar_split_clause,[],[f28,f83])).

fof(f79,plain,(
    spl8_2 ),
    inference(avatar_split_clause,[],[f27,f76])).

fof(f27,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f70,plain,(
    spl8_1 ),
    inference(avatar_split_clause,[],[f26,f67])).

fof(f26,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:02:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.52  % (24823)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.53  % (24805)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (24807)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (24810)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.42/0.55  % (24808)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.42/0.55  % (24825)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.42/0.55  % (24813)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.42/0.55  % (24833)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.42/0.55  % (24825)Refutation found. Thanks to Tanya!
% 1.42/0.55  % SZS status Theorem for theBenchmark
% 1.42/0.55  % SZS output start Proof for theBenchmark
% 1.42/0.55  fof(f244,plain,(
% 1.42/0.55    $false),
% 1.42/0.55    inference(avatar_sat_refutation,[],[f70,f79,f86,f91,f106,f113,f121,f129,f132,f145,f158,f175,f186,f243])).
% 1.42/0.55  fof(f243,plain,(
% 1.42/0.55    ~spl8_3 | ~spl8_9 | ~spl8_12 | spl8_14),
% 1.42/0.55    inference(avatar_contradiction_clause,[],[f242])).
% 1.42/0.55  fof(f242,plain,(
% 1.42/0.55    $false | (~spl8_3 | ~spl8_9 | ~spl8_12 | spl8_14)),
% 1.42/0.55    inference(subsumption_resolution,[],[f241,f185])).
% 1.42/0.55  fof(f185,plain,(
% 1.42/0.55    ~r1_tarski(sK1,k2_relat_1(sK2)) | spl8_14),
% 1.42/0.55    inference(avatar_component_clause,[],[f183])).
% 1.42/0.55  fof(f183,plain,(
% 1.42/0.55    spl8_14 <=> r1_tarski(sK1,k2_relat_1(sK2))),
% 1.42/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).
% 1.42/0.55  fof(f241,plain,(
% 1.42/0.55    r1_tarski(sK1,k2_relat_1(sK2)) | (~spl8_3 | ~spl8_9 | ~spl8_12)),
% 1.42/0.55    inference(duplicate_literal_removal,[],[f239])).
% 1.42/0.55  fof(f239,plain,(
% 1.42/0.55    r1_tarski(sK1,k2_relat_1(sK2)) | r1_tarski(sK1,k2_relat_1(sK2)) | (~spl8_3 | ~spl8_9 | ~spl8_12)),
% 1.42/0.55    inference(resolution,[],[f222,f42])).
% 1.42/0.55  fof(f42,plain,(
% 1.42/0.55    ( ! [X0,X1] : (r2_hidden(sK7(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.42/0.55    inference(cnf_transformation,[],[f17])).
% 1.42/0.55  fof(f17,plain,(
% 1.42/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.42/0.55    inference(ennf_transformation,[],[f1])).
% 1.42/0.55  fof(f1,axiom,(
% 1.42/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.42/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.42/0.55  fof(f222,plain,(
% 1.42/0.55    ( ! [X0] : (~r2_hidden(sK7(X0,k2_relat_1(sK2)),sK1) | r1_tarski(X0,k2_relat_1(sK2))) ) | (~spl8_3 | ~spl8_9 | ~spl8_12)),
% 1.42/0.55    inference(resolution,[],[f200,f43])).
% 1.42/0.55  fof(f43,plain,(
% 1.42/0.55    ( ! [X0,X1] : (~r2_hidden(sK7(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.42/0.55    inference(cnf_transformation,[],[f17])).
% 1.42/0.55  fof(f200,plain,(
% 1.42/0.55    ( ! [X0] : (r2_hidden(X0,k2_relat_1(sK2)) | ~r2_hidden(X0,sK1)) ) | (~spl8_3 | ~spl8_9 | ~spl8_12)),
% 1.42/0.55    inference(resolution,[],[f194,f124])).
% 1.42/0.55  fof(f124,plain,(
% 1.42/0.55    ( ! [X0] : (~sP5(X0,sK2) | r2_hidden(X0,k2_relat_1(sK2))) ) | ~spl8_9),
% 1.42/0.55    inference(avatar_component_clause,[],[f123])).
% 1.42/0.55  fof(f123,plain,(
% 1.42/0.55    spl8_9 <=> ! [X0] : (~sP5(X0,sK2) | r2_hidden(X0,k2_relat_1(sK2)))),
% 1.42/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 1.42/0.55  fof(f194,plain,(
% 1.42/0.55    ( ! [X0] : (sP5(X0,sK2) | ~r2_hidden(X0,sK1)) ) | (~spl8_3 | ~spl8_12)),
% 1.42/0.55    inference(subsumption_resolution,[],[f192,f24])).
% 1.42/0.55  fof(f24,plain,(
% 1.42/0.55    ( ! [X3] : (r2_hidden(sK3(X3),sK0) | ~r2_hidden(X3,sK1)) )),
% 1.42/0.55    inference(cnf_transformation,[],[f14])).
% 1.42/0.55  fof(f14,plain,(
% 1.42/0.55    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.42/0.55    inference(flattening,[],[f13])).
% 1.42/0.55  fof(f13,plain,(
% 1.42/0.55    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.42/0.55    inference(ennf_transformation,[],[f12])).
% 1.42/0.55  fof(f12,negated_conjecture,(
% 1.42/0.55    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 1.42/0.55    inference(negated_conjecture,[],[f11])).
% 1.42/0.55  fof(f11,conjecture,(
% 1.42/0.55    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 1.42/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_funct_2)).
% 1.42/0.55  fof(f192,plain,(
% 1.42/0.55    ( ! [X0] : (~r2_hidden(sK3(X0),sK0) | sP5(X0,sK2) | ~r2_hidden(X0,sK1)) ) | (~spl8_3 | ~spl8_12)),
% 1.42/0.55    inference(backward_demodulation,[],[f107,f191])).
% 1.42/0.55  fof(f191,plain,(
% 1.42/0.55    sK0 = k1_relat_1(sK2) | (~spl8_3 | ~spl8_12)),
% 1.42/0.55    inference(subsumption_resolution,[],[f189,f85])).
% 1.42/0.55  fof(f85,plain,(
% 1.42/0.55    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl8_3),
% 1.42/0.55    inference(avatar_component_clause,[],[f83])).
% 1.42/0.55  fof(f83,plain,(
% 1.42/0.55    spl8_3 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.42/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 1.42/0.55  fof(f189,plain,(
% 1.42/0.55    sK0 = k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl8_12),
% 1.42/0.55    inference(superposition,[],[f153,f47])).
% 1.42/0.55  fof(f47,plain,(
% 1.42/0.55    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.42/0.55    inference(cnf_transformation,[],[f19])).
% 1.42/0.55  fof(f19,plain,(
% 1.42/0.55    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.42/0.55    inference(ennf_transformation,[],[f8])).
% 1.42/0.55  fof(f8,axiom,(
% 1.42/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.42/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.42/0.55  fof(f153,plain,(
% 1.42/0.55    sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl8_12),
% 1.42/0.55    inference(avatar_component_clause,[],[f151])).
% 1.42/0.55  fof(f151,plain,(
% 1.42/0.55    spl8_12 <=> sK0 = k1_relset_1(sK0,sK1,sK2)),
% 1.42/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).
% 1.42/0.55  fof(f107,plain,(
% 1.42/0.55    ( ! [X0] : (sP5(X0,sK2) | ~r2_hidden(sK3(X0),k1_relat_1(sK2)) | ~r2_hidden(X0,sK1)) )),
% 1.42/0.55    inference(superposition,[],[f58,f25])).
% 1.42/0.55  fof(f25,plain,(
% 1.42/0.55    ( ! [X3] : (k1_funct_1(sK2,sK3(X3)) = X3 | ~r2_hidden(X3,sK1)) )),
% 1.42/0.55    inference(cnf_transformation,[],[f14])).
% 1.42/0.55  fof(f58,plain,(
% 1.42/0.55    ( ! [X0,X3] : (sP5(k1_funct_1(X0,X3),X0) | ~r2_hidden(X3,k1_relat_1(X0))) )),
% 1.42/0.55    inference(equality_resolution,[],[f31])).
% 1.42/0.55  fof(f31,plain,(
% 1.42/0.55    ( ! [X2,X0,X3] : (~r2_hidden(X3,k1_relat_1(X0)) | k1_funct_1(X0,X3) != X2 | sP5(X2,X0)) )),
% 1.42/0.55    inference(cnf_transformation,[],[f16])).
% 1.42/0.55  fof(f16,plain,(
% 1.42/0.55    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.42/0.55    inference(flattening,[],[f15])).
% 1.42/0.55  fof(f15,plain,(
% 1.42/0.55    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.42/0.55    inference(ennf_transformation,[],[f5])).
% 1.42/0.55  fof(f5,axiom,(
% 1.42/0.55    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 1.42/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).
% 1.42/0.55  fof(f186,plain,(
% 1.42/0.55    ~spl8_14 | spl8_6 | ~spl8_11),
% 1.42/0.55    inference(avatar_split_clause,[],[f149,f142,f103,f183])).
% 1.42/0.55  fof(f103,plain,(
% 1.42/0.55    spl8_6 <=> sK1 = k2_relat_1(sK2)),
% 1.42/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 1.42/0.55  fof(f142,plain,(
% 1.42/0.55    spl8_11 <=> r1_tarski(k2_relat_1(sK2),sK1)),
% 1.42/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 1.42/0.55  fof(f149,plain,(
% 1.42/0.55    ~r1_tarski(sK1,k2_relat_1(sK2)) | (spl8_6 | ~spl8_11)),
% 1.42/0.55    inference(subsumption_resolution,[],[f148,f105])).
% 1.42/0.55  fof(f105,plain,(
% 1.42/0.55    sK1 != k2_relat_1(sK2) | spl8_6),
% 1.42/0.55    inference(avatar_component_clause,[],[f103])).
% 1.42/0.55  fof(f148,plain,(
% 1.42/0.55    ~r1_tarski(sK1,k2_relat_1(sK2)) | sK1 = k2_relat_1(sK2) | ~spl8_11),
% 1.42/0.55    inference(resolution,[],[f144,f40])).
% 1.42/0.55  fof(f40,plain,(
% 1.42/0.55    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.42/0.55    inference(cnf_transformation,[],[f2])).
% 1.42/0.55  fof(f2,axiom,(
% 1.42/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.42/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.42/0.55  fof(f144,plain,(
% 1.42/0.55    r1_tarski(k2_relat_1(sK2),sK1) | ~spl8_11),
% 1.42/0.55    inference(avatar_component_clause,[],[f142])).
% 1.42/0.55  fof(f175,plain,(
% 1.42/0.55    spl8_6 | ~spl8_11 | ~spl8_13),
% 1.42/0.55    inference(avatar_contradiction_clause,[],[f174])).
% 1.42/0.55  fof(f174,plain,(
% 1.42/0.55    $false | (spl8_6 | ~spl8_11 | ~spl8_13)),
% 1.42/0.55    inference(subsumption_resolution,[],[f172,f30])).
% 1.42/0.55  fof(f30,plain,(
% 1.42/0.55    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.42/0.55    inference(cnf_transformation,[],[f3])).
% 1.42/0.55  fof(f3,axiom,(
% 1.42/0.55    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.42/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.42/0.55  fof(f172,plain,(
% 1.42/0.55    ~r1_tarski(k1_xboole_0,k2_relat_1(sK2)) | (spl8_6 | ~spl8_11 | ~spl8_13)),
% 1.42/0.55    inference(backward_demodulation,[],[f149,f157])).
% 1.42/0.55  fof(f157,plain,(
% 1.42/0.55    k1_xboole_0 = sK1 | ~spl8_13),
% 1.42/0.55    inference(avatar_component_clause,[],[f155])).
% 1.42/0.55  fof(f155,plain,(
% 1.42/0.55    spl8_13 <=> k1_xboole_0 = sK1),
% 1.42/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).
% 1.42/0.55  fof(f158,plain,(
% 1.42/0.55    spl8_12 | spl8_13 | ~spl8_2),
% 1.42/0.55    inference(avatar_split_clause,[],[f81,f76,f155,f151])).
% 1.42/0.55  fof(f76,plain,(
% 1.42/0.55    spl8_2 <=> v1_funct_2(sK2,sK0,sK1)),
% 1.42/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 1.42/0.55  fof(f81,plain,(
% 1.42/0.55    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl8_2),
% 1.42/0.55    inference(subsumption_resolution,[],[f80,f28])).
% 1.42/0.55  fof(f28,plain,(
% 1.42/0.55    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.42/0.55    inference(cnf_transformation,[],[f14])).
% 1.42/0.55  fof(f80,plain,(
% 1.42/0.55    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl8_2),
% 1.42/0.55    inference(resolution,[],[f78,f55])).
% 1.42/0.55  fof(f55,plain,(
% 1.42/0.55    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.42/0.55    inference(cnf_transformation,[],[f23])).
% 1.42/0.55  fof(f23,plain,(
% 1.42/0.55    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.42/0.55    inference(flattening,[],[f22])).
% 1.42/0.55  fof(f22,plain,(
% 1.42/0.55    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.42/0.55    inference(ennf_transformation,[],[f10])).
% 1.42/0.55  fof(f10,axiom,(
% 1.42/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.42/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.42/0.55  fof(f78,plain,(
% 1.42/0.55    v1_funct_2(sK2,sK0,sK1) | ~spl8_2),
% 1.42/0.55    inference(avatar_component_clause,[],[f76])).
% 1.42/0.55  fof(f145,plain,(
% 1.42/0.55    spl8_11 | ~spl8_8),
% 1.42/0.55    inference(avatar_split_clause,[],[f139,f118,f142])).
% 1.42/0.55  fof(f118,plain,(
% 1.42/0.55    spl8_8 <=> m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1))),
% 1.42/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 1.42/0.55  fof(f139,plain,(
% 1.42/0.55    r1_tarski(k2_relat_1(sK2),sK1) | ~spl8_8),
% 1.42/0.55    inference(resolution,[],[f120,f45])).
% 1.42/0.55  fof(f45,plain,(
% 1.42/0.55    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.42/0.55    inference(cnf_transformation,[],[f4])).
% 1.42/0.55  fof(f4,axiom,(
% 1.42/0.55    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.42/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.42/0.55  fof(f120,plain,(
% 1.42/0.55    m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) | ~spl8_8),
% 1.42/0.55    inference(avatar_component_clause,[],[f118])).
% 1.42/0.55  fof(f132,plain,(
% 1.42/0.55    ~spl8_3 | spl8_10),
% 1.42/0.55    inference(avatar_contradiction_clause,[],[f131])).
% 1.42/0.55  fof(f131,plain,(
% 1.42/0.55    $false | (~spl8_3 | spl8_10)),
% 1.42/0.55    inference(subsumption_resolution,[],[f85,f130])).
% 1.42/0.55  fof(f130,plain,(
% 1.42/0.55    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl8_10),
% 1.42/0.55    inference(resolution,[],[f128,f46])).
% 1.42/0.55  fof(f46,plain,(
% 1.42/0.55    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.42/0.55    inference(cnf_transformation,[],[f18])).
% 1.42/0.55  fof(f18,plain,(
% 1.42/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.42/0.55    inference(ennf_transformation,[],[f6])).
% 1.42/0.55  fof(f6,axiom,(
% 1.42/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.42/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.42/0.55  fof(f128,plain,(
% 1.42/0.55    ~v1_relat_1(sK2) | spl8_10),
% 1.42/0.55    inference(avatar_component_clause,[],[f126])).
% 1.42/0.55  fof(f126,plain,(
% 1.42/0.55    spl8_10 <=> v1_relat_1(sK2)),
% 1.42/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 1.42/0.55  fof(f129,plain,(
% 1.42/0.55    spl8_9 | ~spl8_10 | ~spl8_1),
% 1.42/0.55    inference(avatar_split_clause,[],[f71,f67,f126,f123])).
% 1.42/0.55  fof(f67,plain,(
% 1.42/0.55    spl8_1 <=> v1_funct_1(sK2)),
% 1.42/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 1.42/0.55  fof(f71,plain,(
% 1.42/0.55    ( ! [X0] : (~v1_relat_1(sK2) | ~sP5(X0,sK2) | r2_hidden(X0,k2_relat_1(sK2))) ) | ~spl8_1),
% 1.42/0.55    inference(resolution,[],[f69,f57])).
% 1.42/0.55  fof(f57,plain,(
% 1.42/0.55    ( ! [X2,X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | ~sP5(X2,X0) | r2_hidden(X2,k2_relat_1(X0))) )),
% 1.42/0.55    inference(equality_resolution,[],[f34])).
% 1.42/0.55  fof(f34,plain,(
% 1.42/0.55    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~sP5(X2,X0) | r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 1.42/0.55    inference(cnf_transformation,[],[f16])).
% 1.42/0.55  fof(f69,plain,(
% 1.42/0.55    v1_funct_1(sK2) | ~spl8_1),
% 1.42/0.55    inference(avatar_component_clause,[],[f67])).
% 1.42/0.55  fof(f121,plain,(
% 1.42/0.55    spl8_8 | ~spl8_3 | ~spl8_7),
% 1.42/0.55    inference(avatar_split_clause,[],[f116,f110,f83,f118])).
% 1.42/0.55  fof(f110,plain,(
% 1.42/0.55    spl8_7 <=> m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK1))),
% 1.42/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 1.42/0.55  fof(f116,plain,(
% 1.42/0.55    m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) | (~spl8_3 | ~spl8_7)),
% 1.42/0.55    inference(subsumption_resolution,[],[f115,f85])).
% 1.42/0.55  fof(f115,plain,(
% 1.42/0.55    m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl8_7),
% 1.42/0.55    inference(superposition,[],[f112,f48])).
% 1.42/0.55  fof(f48,plain,(
% 1.42/0.55    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.42/0.55    inference(cnf_transformation,[],[f20])).
% 1.42/0.55  fof(f20,plain,(
% 1.42/0.55    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.42/0.55    inference(ennf_transformation,[],[f9])).
% 1.42/0.55  fof(f9,axiom,(
% 1.42/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.42/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.42/0.55  fof(f112,plain,(
% 1.42/0.55    m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK1)) | ~spl8_7),
% 1.42/0.55    inference(avatar_component_clause,[],[f110])).
% 1.42/0.55  fof(f113,plain,(
% 1.42/0.55    spl8_7 | ~spl8_3),
% 1.42/0.55    inference(avatar_split_clause,[],[f93,f83,f110])).
% 1.42/0.55  fof(f93,plain,(
% 1.42/0.55    m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK1)) | ~spl8_3),
% 1.42/0.55    inference(resolution,[],[f85,f49])).
% 1.42/0.55  fof(f49,plain,(
% 1.42/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))) )),
% 1.42/0.55    inference(cnf_transformation,[],[f21])).
% 1.42/0.55  fof(f21,plain,(
% 1.42/0.55    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.42/0.55    inference(ennf_transformation,[],[f7])).
% 1.42/0.55  fof(f7,axiom,(
% 1.42/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 1.42/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).
% 1.42/0.55  fof(f106,plain,(
% 1.42/0.55    ~spl8_6 | ~spl8_3 | spl8_4),
% 1.42/0.55    inference(avatar_split_clause,[],[f101,f88,f83,f103])).
% 1.42/0.55  fof(f88,plain,(
% 1.42/0.55    spl8_4 <=> sK1 = k2_relset_1(sK0,sK1,sK2)),
% 1.42/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 1.42/0.55  fof(f101,plain,(
% 1.42/0.55    sK1 != k2_relat_1(sK2) | (~spl8_3 | spl8_4)),
% 1.42/0.55    inference(subsumption_resolution,[],[f100,f85])).
% 1.42/0.55  fof(f100,plain,(
% 1.42/0.55    sK1 != k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl8_4),
% 1.42/0.55    inference(superposition,[],[f90,f48])).
% 1.42/0.55  fof(f90,plain,(
% 1.42/0.55    sK1 != k2_relset_1(sK0,sK1,sK2) | spl8_4),
% 1.42/0.55    inference(avatar_component_clause,[],[f88])).
% 1.42/0.55  fof(f91,plain,(
% 1.42/0.55    ~spl8_4),
% 1.42/0.55    inference(avatar_split_clause,[],[f29,f88])).
% 1.42/0.55  fof(f29,plain,(
% 1.42/0.55    sK1 != k2_relset_1(sK0,sK1,sK2)),
% 1.42/0.55    inference(cnf_transformation,[],[f14])).
% 1.42/0.55  fof(f86,plain,(
% 1.42/0.55    spl8_3),
% 1.42/0.55    inference(avatar_split_clause,[],[f28,f83])).
% 1.42/0.55  fof(f79,plain,(
% 1.42/0.55    spl8_2),
% 1.42/0.55    inference(avatar_split_clause,[],[f27,f76])).
% 1.42/0.55  fof(f27,plain,(
% 1.42/0.55    v1_funct_2(sK2,sK0,sK1)),
% 1.42/0.55    inference(cnf_transformation,[],[f14])).
% 1.42/0.55  fof(f70,plain,(
% 1.42/0.55    spl8_1),
% 1.42/0.55    inference(avatar_split_clause,[],[f26,f67])).
% 1.42/0.55  fof(f26,plain,(
% 1.42/0.55    v1_funct_1(sK2)),
% 1.42/0.55    inference(cnf_transformation,[],[f14])).
% 1.42/0.55  % SZS output end Proof for theBenchmark
% 1.42/0.55  % (24825)------------------------------
% 1.42/0.55  % (24825)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.55  % (24825)Termination reason: Refutation
% 1.42/0.55  
% 1.42/0.55  % (24825)Memory used [KB]: 10874
% 1.42/0.55  % (24825)Time elapsed: 0.132 s
% 1.42/0.55  % (24825)------------------------------
% 1.42/0.55  % (24825)------------------------------
% 1.42/0.55  % (24834)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.42/0.55  % (24819)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.42/0.56  % (24811)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.42/0.56  % (24814)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.42/0.56  % (24822)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.42/0.56  % (24809)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.42/0.56  % (24817)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.42/0.56  % (24830)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.56/0.57  % (24828)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.56/0.57  % (24816)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.56/0.57  % (24815)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.56/0.57  % (24820)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.56/0.57  % (24832)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.56/0.57  % (24824)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.56/0.58  % (24806)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.56/0.58  % (24826)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.56/0.58  % (24827)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.56/0.58  % (24831)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.56/0.58  % (24804)Success in time 0.215 s
%------------------------------------------------------------------------------
