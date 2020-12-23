%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:49 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 165 expanded)
%              Number of leaves         :   25 (  65 expanded)
%              Depth                    :   10
%              Number of atoms          :  314 ( 538 expanded)
%              Number of equality atoms :   68 ( 123 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f360,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f78,f83,f88,f98,f109,f118,f127,f149,f171,f228,f302,f308,f311,f354,f359])).

fof(f359,plain,
    ( spl8_13
    | ~ spl8_30 ),
    inference(avatar_contradiction_clause,[],[f355])).

fof(f355,plain,
    ( $false
    | spl8_13
    | ~ spl8_30 ),
    inference(unit_resulting_resolution,[],[f148,f353,f32])).

fof(f32,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f353,plain,
    ( r1_tarski(k2_relat_1(sK2),k1_xboole_0)
    | ~ spl8_30 ),
    inference(avatar_component_clause,[],[f351])).

fof(f351,plain,
    ( spl8_30
  <=> r1_tarski(k2_relat_1(sK2),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).

fof(f148,plain,
    ( k1_xboole_0 != k2_relat_1(sK2)
    | spl8_13 ),
    inference(avatar_component_clause,[],[f146])).

fof(f146,plain,
    ( spl8_13
  <=> k1_xboole_0 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f354,plain,
    ( spl8_30
    | ~ spl8_10
    | ~ spl8_25 ),
    inference(avatar_split_clause,[],[f334,f305,f124,f351])).

fof(f124,plain,
    ( spl8_10
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f305,plain,
    ( spl8_25
  <=> r1_tarski(k2_relat_1(sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).

fof(f334,plain,
    ( r1_tarski(k2_relat_1(sK2),k1_xboole_0)
    | ~ spl8_10
    | ~ spl8_25 ),
    inference(forward_demodulation,[],[f306,f126])).

fof(f126,plain,
    ( k1_xboole_0 = sK1
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f124])).

fof(f306,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1)
    | ~ spl8_25 ),
    inference(avatar_component_clause,[],[f305])).

fof(f311,plain,
    ( ~ spl8_5
    | ~ spl8_7
    | spl8_25 ),
    inference(avatar_contradiction_clause,[],[f309])).

fof(f309,plain,
    ( $false
    | ~ spl8_5
    | ~ spl8_7
    | spl8_25 ),
    inference(unit_resulting_resolution,[],[f97,f108,f307,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | ~ v5_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f307,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),sK1)
    | spl8_25 ),
    inference(avatar_component_clause,[],[f305])).

fof(f108,plain,
    ( v5_relat_1(sK2,sK1)
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl8_7
  <=> v5_relat_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f97,plain,
    ( v1_relat_1(sK2)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl8_5
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f308,plain,
    ( spl8_8
    | ~ spl8_25
    | ~ spl8_24 ),
    inference(avatar_split_clause,[],[f303,f299,f305,f115])).

fof(f115,plain,
    ( spl8_8
  <=> sK1 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f299,plain,
    ( spl8_24
  <=> r1_tarski(sK1,k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).

fof(f303,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),sK1)
    | sK1 = k2_relat_1(sK2)
    | ~ spl8_24 ),
    inference(resolution,[],[f301,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f301,plain,
    ( r1_tarski(sK1,k2_relat_1(sK2))
    | ~ spl8_24 ),
    inference(avatar_component_clause,[],[f299])).

fof(f302,plain,
    ( spl8_24
    | ~ spl8_20 ),
    inference(avatar_split_clause,[],[f296,f226,f299])).

fof(f226,plain,
    ( spl8_20
  <=> ! [X2] :
        ( ~ r2_hidden(sK3(X2),sK0)
        | ~ r2_hidden(X2,sK1)
        | r2_hidden(X2,k2_relat_1(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

% (553)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
fof(f296,plain,
    ( r1_tarski(sK1,k2_relat_1(sK2))
    | ~ spl8_20 ),
    inference(duplicate_literal_removal,[],[f294])).

fof(f294,plain,
    ( r1_tarski(sK1,k2_relat_1(sK2))
    | r1_tarski(sK1,k2_relat_1(sK2))
    | ~ spl8_20 ),
    inference(resolution,[],[f293,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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

fof(f293,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK7(X0,k2_relat_1(sK2)),sK1)
        | r1_tarski(X0,k2_relat_1(sK2)) )
    | ~ spl8_20 ),
    inference(duplicate_literal_removal,[],[f291])).

fof(f291,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK7(X0,k2_relat_1(sK2)),sK1)
        | r1_tarski(X0,k2_relat_1(sK2))
        | ~ r2_hidden(sK7(X0,k2_relat_1(sK2)),sK1) )
    | ~ spl8_20 ),
    inference(resolution,[],[f283,f26])).

fof(f26,plain,(
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

fof(f283,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3(sK7(X0,k2_relat_1(sK2))),sK0)
        | ~ r2_hidden(sK7(X0,k2_relat_1(sK2)),sK1)
        | r1_tarski(X0,k2_relat_1(sK2)) )
    | ~ spl8_20 ),
    inference(resolution,[],[f227,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK7(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f227,plain,
    ( ! [X2] :
        ( r2_hidden(X2,k2_relat_1(sK2))
        | ~ r2_hidden(X2,sK1)
        | ~ r2_hidden(sK3(X2),sK0) )
    | ~ spl8_20 ),
    inference(avatar_component_clause,[],[f226])).

fof(f228,plain,
    ( ~ spl8_5
    | spl8_20
    | ~ spl8_15 ),
    inference(avatar_split_clause,[],[f223,f168,f226,f95])).

fof(f168,plain,
    ( spl8_15
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f223,plain,
    ( ! [X2] :
        ( ~ r2_hidden(sK3(X2),sK0)
        | r2_hidden(X2,k2_relat_1(sK2))
        | ~ v1_relat_1(sK2)
        | ~ r2_hidden(X2,sK1) )
    | ~ spl8_15 ),
    inference(forward_demodulation,[],[f113,f170])).

fof(f170,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl8_15 ),
    inference(avatar_component_clause,[],[f168])).

fof(f113,plain,(
    ! [X2] :
      ( r2_hidden(X2,k2_relat_1(sK2))
      | ~ r2_hidden(sK3(X2),k1_relat_1(sK2))
      | ~ v1_relat_1(sK2)
      | ~ r2_hidden(X2,sK1) ) ),
    inference(global_subsumption,[],[f28,f111])).

fof(f111,plain,(
    ! [X2] :
      ( r2_hidden(X2,k2_relat_1(sK2))
      | ~ v1_funct_1(sK2)
      | ~ r2_hidden(sK3(X2),k1_relat_1(sK2))
      | ~ v1_relat_1(sK2)
      | ~ r2_hidden(X2,sK1) ) ),
    inference(superposition,[],[f59,f27])).

fof(f27,plain,(
    ! [X3] :
      ( k1_funct_1(sK2,sK3(X3)) = X3
      | ~ r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f59,plain,(
    ! [X0,X3] :
      ( r2_hidden(k1_funct_1(X0,X3),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | r2_hidden(k1_funct_1(X0,X3),X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | k1_funct_1(X0,X3) != X2
      | r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

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

fof(f28,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f171,plain,
    ( ~ spl8_3
    | spl8_15
    | ~ spl8_9 ),
    inference(avatar_split_clause,[],[f161,f120,f168,f80])).

fof(f80,plain,
    ( spl8_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f120,plain,
    ( spl8_9
  <=> sK0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f161,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl8_9 ),
    inference(superposition,[],[f122,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f122,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f120])).

fof(f149,plain,
    ( ~ spl8_13
    | spl8_8
    | ~ spl8_10 ),
    inference(avatar_split_clause,[],[f134,f124,f115,f146])).

fof(f134,plain,
    ( k1_xboole_0 != k2_relat_1(sK2)
    | spl8_8
    | ~ spl8_10 ),
    inference(backward_demodulation,[],[f117,f126])).

fof(f117,plain,
    ( sK1 != k2_relat_1(sK2)
    | spl8_8 ),
    inference(avatar_component_clause,[],[f115])).

fof(f127,plain,
    ( ~ spl8_2
    | spl8_9
    | spl8_10
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f90,f80,f124,f120,f75])).

fof(f75,plain,
    ( spl8_2
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f90,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ spl8_3 ),
    inference(resolution,[],[f82,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
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

fof(f82,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f80])).

fof(f118,plain,
    ( ~ spl8_3
    | ~ spl8_8
    | spl8_4 ),
    inference(avatar_split_clause,[],[f99,f85,f115,f80])).

fof(f85,plain,
    ( spl8_4
  <=> sK1 = k2_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f99,plain,
    ( sK1 != k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl8_4 ),
    inference(superposition,[],[f87,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f87,plain,
    ( sK1 != k2_relset_1(sK0,sK1,sK2)
    | spl8_4 ),
    inference(avatar_component_clause,[],[f85])).

fof(f109,plain,
    ( spl8_7
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f92,f80,f106])).

fof(f92,plain,
    ( v5_relat_1(sK2,sK1)
    | ~ spl8_3 ),
    inference(resolution,[],[f82,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f98,plain,
    ( spl8_5
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f93,f80,f95])).

fof(f93,plain,
    ( v1_relat_1(sK2)
    | ~ spl8_3 ),
    inference(resolution,[],[f82,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f88,plain,(
    ~ spl8_4 ),
    inference(avatar_split_clause,[],[f31,f85])).

fof(f31,plain,(
    sK1 != k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f83,plain,(
    spl8_3 ),
    inference(avatar_split_clause,[],[f30,f80])).

fof(f30,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f14])).

fof(f78,plain,(
    spl8_2 ),
    inference(avatar_split_clause,[],[f29,f75])).

fof(f29,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.15/0.36  % Computer   : n022.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % WCLimit    : 600
% 0.15/0.36  % DateTime   : Tue Dec  1 09:46:11 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.22/0.51  % (557)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.51  % (542)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.51  % (549)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.52  % (540)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.52  % (544)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.52  % (558)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.53  % (538)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.53  % (550)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.53  % (539)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.53  % (545)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.53  % (536)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.53  % (557)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f360,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(avatar_sat_refutation,[],[f78,f83,f88,f98,f109,f118,f127,f149,f171,f228,f302,f308,f311,f354,f359])).
% 0.22/0.53  fof(f359,plain,(
% 0.22/0.53    spl8_13 | ~spl8_30),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f355])).
% 0.22/0.53  fof(f355,plain,(
% 0.22/0.53    $false | (spl8_13 | ~spl8_30)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f148,f353,f32])).
% 0.22/0.53  fof(f32,plain,(
% 0.22/0.53    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.22/0.53    inference(cnf_transformation,[],[f15])).
% 0.22/0.53  fof(f15,plain,(
% 0.22/0.53    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.22/0.53    inference(ennf_transformation,[],[f3])).
% 0.22/0.53  fof(f3,axiom,(
% 0.22/0.53    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.22/0.53  fof(f353,plain,(
% 0.22/0.53    r1_tarski(k2_relat_1(sK2),k1_xboole_0) | ~spl8_30),
% 0.22/0.53    inference(avatar_component_clause,[],[f351])).
% 0.22/0.53  fof(f351,plain,(
% 0.22/0.53    spl8_30 <=> r1_tarski(k2_relat_1(sK2),k1_xboole_0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).
% 0.22/0.53  fof(f148,plain,(
% 0.22/0.53    k1_xboole_0 != k2_relat_1(sK2) | spl8_13),
% 0.22/0.53    inference(avatar_component_clause,[],[f146])).
% 0.22/0.53  fof(f146,plain,(
% 0.22/0.53    spl8_13 <=> k1_xboole_0 = k2_relat_1(sK2)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).
% 0.22/0.53  fof(f354,plain,(
% 0.22/0.53    spl8_30 | ~spl8_10 | ~spl8_25),
% 0.22/0.53    inference(avatar_split_clause,[],[f334,f305,f124,f351])).
% 0.22/0.53  fof(f124,plain,(
% 0.22/0.53    spl8_10 <=> k1_xboole_0 = sK1),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 0.22/0.53  fof(f305,plain,(
% 0.22/0.53    spl8_25 <=> r1_tarski(k2_relat_1(sK2),sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).
% 0.22/0.53  fof(f334,plain,(
% 0.22/0.53    r1_tarski(k2_relat_1(sK2),k1_xboole_0) | (~spl8_10 | ~spl8_25)),
% 0.22/0.53    inference(forward_demodulation,[],[f306,f126])).
% 0.22/0.53  fof(f126,plain,(
% 0.22/0.53    k1_xboole_0 = sK1 | ~spl8_10),
% 0.22/0.53    inference(avatar_component_clause,[],[f124])).
% 0.22/0.53  fof(f306,plain,(
% 0.22/0.53    r1_tarski(k2_relat_1(sK2),sK1) | ~spl8_25),
% 0.22/0.53    inference(avatar_component_clause,[],[f305])).
% 0.22/0.53  fof(f311,plain,(
% 0.22/0.53    ~spl8_5 | ~spl8_7 | spl8_25),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f309])).
% 0.22/0.53  fof(f309,plain,(
% 0.22/0.53    $false | (~spl8_5 | ~spl8_7 | spl8_25)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f97,f108,f307,f40])).
% 0.22/0.53  fof(f40,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1) | ~v5_relat_1(X1,X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f18])).
% 0.22/0.53  fof(f18,plain,(
% 0.22/0.53    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.53    inference(ennf_transformation,[],[f4])).
% 0.22/0.53  fof(f4,axiom,(
% 0.22/0.53    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 0.22/0.53  fof(f307,plain,(
% 0.22/0.53    ~r1_tarski(k2_relat_1(sK2),sK1) | spl8_25),
% 0.22/0.53    inference(avatar_component_clause,[],[f305])).
% 0.22/0.53  fof(f108,plain,(
% 0.22/0.53    v5_relat_1(sK2,sK1) | ~spl8_7),
% 0.22/0.53    inference(avatar_component_clause,[],[f106])).
% 0.22/0.53  fof(f106,plain,(
% 0.22/0.53    spl8_7 <=> v5_relat_1(sK2,sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 0.22/0.53  fof(f97,plain,(
% 0.22/0.53    v1_relat_1(sK2) | ~spl8_5),
% 0.22/0.53    inference(avatar_component_clause,[],[f95])).
% 0.22/0.53  fof(f95,plain,(
% 0.22/0.53    spl8_5 <=> v1_relat_1(sK2)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.22/0.53  fof(f308,plain,(
% 0.22/0.53    spl8_8 | ~spl8_25 | ~spl8_24),
% 0.22/0.53    inference(avatar_split_clause,[],[f303,f299,f305,f115])).
% 0.22/0.53  fof(f115,plain,(
% 0.22/0.53    spl8_8 <=> sK1 = k2_relat_1(sK2)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 0.22/0.53  fof(f299,plain,(
% 0.22/0.53    spl8_24 <=> r1_tarski(sK1,k2_relat_1(sK2))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).
% 0.22/0.53  fof(f303,plain,(
% 0.22/0.53    ~r1_tarski(k2_relat_1(sK2),sK1) | sK1 = k2_relat_1(sK2) | ~spl8_24),
% 0.22/0.53    inference(resolution,[],[f301,f43])).
% 0.22/0.53  fof(f43,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.22/0.53    inference(cnf_transformation,[],[f2])).
% 0.22/0.53  fof(f2,axiom,(
% 0.22/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.53  fof(f301,plain,(
% 0.22/0.53    r1_tarski(sK1,k2_relat_1(sK2)) | ~spl8_24),
% 0.22/0.53    inference(avatar_component_clause,[],[f299])).
% 0.22/0.53  fof(f302,plain,(
% 0.22/0.53    spl8_24 | ~spl8_20),
% 0.22/0.53    inference(avatar_split_clause,[],[f296,f226,f299])).
% 0.22/0.53  fof(f226,plain,(
% 0.22/0.53    spl8_20 <=> ! [X2] : (~r2_hidden(sK3(X2),sK0) | ~r2_hidden(X2,sK1) | r2_hidden(X2,k2_relat_1(sK2)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).
% 0.22/0.53  % (553)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.53  fof(f296,plain,(
% 0.22/0.53    r1_tarski(sK1,k2_relat_1(sK2)) | ~spl8_20),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f294])).
% 0.22/0.53  fof(f294,plain,(
% 0.22/0.53    r1_tarski(sK1,k2_relat_1(sK2)) | r1_tarski(sK1,k2_relat_1(sK2)) | ~spl8_20),
% 0.22/0.53    inference(resolution,[],[f293,f45])).
% 0.22/0.53  fof(f45,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r2_hidden(sK7(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f19])).
% 0.22/0.53  fof(f19,plain,(
% 0.22/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.53  fof(f293,plain,(
% 0.22/0.53    ( ! [X0] : (~r2_hidden(sK7(X0,k2_relat_1(sK2)),sK1) | r1_tarski(X0,k2_relat_1(sK2))) ) | ~spl8_20),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f291])).
% 0.22/0.53  fof(f291,plain,(
% 0.22/0.53    ( ! [X0] : (~r2_hidden(sK7(X0,k2_relat_1(sK2)),sK1) | r1_tarski(X0,k2_relat_1(sK2)) | ~r2_hidden(sK7(X0,k2_relat_1(sK2)),sK1)) ) | ~spl8_20),
% 0.22/0.53    inference(resolution,[],[f283,f26])).
% 0.22/0.53  fof(f26,plain,(
% 0.22/0.53    ( ! [X3] : (r2_hidden(sK3(X3),sK0) | ~r2_hidden(X3,sK1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f14])).
% 0.22/0.53  fof(f14,plain,(
% 0.22/0.53    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.22/0.53    inference(flattening,[],[f13])).
% 0.22/0.53  fof(f13,plain,(
% 0.22/0.53    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.22/0.53    inference(ennf_transformation,[],[f12])).
% 0.22/0.53  fof(f12,negated_conjecture,(
% 0.22/0.53    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 0.22/0.53    inference(negated_conjecture,[],[f11])).
% 0.22/0.53  fof(f11,conjecture,(
% 0.22/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_funct_2)).
% 0.22/0.53  fof(f283,plain,(
% 0.22/0.53    ( ! [X0] : (~r2_hidden(sK3(sK7(X0,k2_relat_1(sK2))),sK0) | ~r2_hidden(sK7(X0,k2_relat_1(sK2)),sK1) | r1_tarski(X0,k2_relat_1(sK2))) ) | ~spl8_20),
% 0.22/0.53    inference(resolution,[],[f227,f46])).
% 0.22/0.53  fof(f46,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r2_hidden(sK7(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f19])).
% 0.22/0.53  fof(f227,plain,(
% 0.22/0.53    ( ! [X2] : (r2_hidden(X2,k2_relat_1(sK2)) | ~r2_hidden(X2,sK1) | ~r2_hidden(sK3(X2),sK0)) ) | ~spl8_20),
% 0.22/0.53    inference(avatar_component_clause,[],[f226])).
% 0.22/0.53  fof(f228,plain,(
% 0.22/0.53    ~spl8_5 | spl8_20 | ~spl8_15),
% 0.22/0.53    inference(avatar_split_clause,[],[f223,f168,f226,f95])).
% 0.22/0.53  fof(f168,plain,(
% 0.22/0.53    spl8_15 <=> sK0 = k1_relat_1(sK2)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).
% 0.22/0.53  fof(f223,plain,(
% 0.22/0.53    ( ! [X2] : (~r2_hidden(sK3(X2),sK0) | r2_hidden(X2,k2_relat_1(sK2)) | ~v1_relat_1(sK2) | ~r2_hidden(X2,sK1)) ) | ~spl8_15),
% 0.22/0.53    inference(forward_demodulation,[],[f113,f170])).
% 0.22/0.53  fof(f170,plain,(
% 0.22/0.53    sK0 = k1_relat_1(sK2) | ~spl8_15),
% 0.22/0.53    inference(avatar_component_clause,[],[f168])).
% 0.22/0.53  fof(f113,plain,(
% 0.22/0.53    ( ! [X2] : (r2_hidden(X2,k2_relat_1(sK2)) | ~r2_hidden(sK3(X2),k1_relat_1(sK2)) | ~v1_relat_1(sK2) | ~r2_hidden(X2,sK1)) )),
% 0.22/0.53    inference(global_subsumption,[],[f28,f111])).
% 0.22/0.53  fof(f111,plain,(
% 0.22/0.53    ( ! [X2] : (r2_hidden(X2,k2_relat_1(sK2)) | ~v1_funct_1(sK2) | ~r2_hidden(sK3(X2),k1_relat_1(sK2)) | ~v1_relat_1(sK2) | ~r2_hidden(X2,sK1)) )),
% 0.22/0.53    inference(superposition,[],[f59,f27])).
% 0.22/0.53  fof(f27,plain,(
% 0.22/0.53    ( ! [X3] : (k1_funct_1(sK2,sK3(X3)) = X3 | ~r2_hidden(X3,sK1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f14])).
% 0.22/0.53  fof(f59,plain,(
% 0.22/0.53    ( ! [X0,X3] : (r2_hidden(k1_funct_1(X0,X3),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~r2_hidden(X3,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.22/0.53    inference(equality_resolution,[],[f58])).
% 0.22/0.53  fof(f58,plain,(
% 0.22/0.53    ( ! [X0,X3,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~r2_hidden(X3,k1_relat_1(X0)) | r2_hidden(k1_funct_1(X0,X3),X1) | k2_relat_1(X0) != X1) )),
% 0.22/0.53    inference(equality_resolution,[],[f38])).
% 0.22/0.53  fof(f38,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~r2_hidden(X3,k1_relat_1(X0)) | k1_funct_1(X0,X3) != X2 | r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 0.22/0.53    inference(cnf_transformation,[],[f17])).
% 0.22/0.53  fof(f17,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.53    inference(flattening,[],[f16])).
% 0.22/0.53  fof(f16,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f5])).
% 0.22/0.53  fof(f5,axiom,(
% 0.22/0.53    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).
% 0.22/0.53  fof(f28,plain,(
% 0.22/0.53    v1_funct_1(sK2)),
% 0.22/0.53    inference(cnf_transformation,[],[f14])).
% 0.22/0.53  fof(f171,plain,(
% 0.22/0.53    ~spl8_3 | spl8_15 | ~spl8_9),
% 0.22/0.53    inference(avatar_split_clause,[],[f161,f120,f168,f80])).
% 0.22/0.53  fof(f80,plain,(
% 0.22/0.53    spl8_3 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.22/0.53  fof(f120,plain,(
% 0.22/0.53    spl8_9 <=> sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 0.22/0.53  fof(f161,plain,(
% 0.22/0.53    sK0 = k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl8_9),
% 0.22/0.53    inference(superposition,[],[f122,f48])).
% 0.22/0.53  fof(f48,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f21])).
% 0.22/0.53  fof(f21,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.53    inference(ennf_transformation,[],[f8])).
% 0.22/0.53  fof(f8,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.53  fof(f122,plain,(
% 0.22/0.53    sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl8_9),
% 0.22/0.53    inference(avatar_component_clause,[],[f120])).
% 0.22/0.53  fof(f149,plain,(
% 0.22/0.53    ~spl8_13 | spl8_8 | ~spl8_10),
% 0.22/0.53    inference(avatar_split_clause,[],[f134,f124,f115,f146])).
% 0.22/0.53  fof(f134,plain,(
% 0.22/0.53    k1_xboole_0 != k2_relat_1(sK2) | (spl8_8 | ~spl8_10)),
% 0.22/0.53    inference(backward_demodulation,[],[f117,f126])).
% 0.22/0.53  fof(f117,plain,(
% 0.22/0.53    sK1 != k2_relat_1(sK2) | spl8_8),
% 0.22/0.53    inference(avatar_component_clause,[],[f115])).
% 0.22/0.54  fof(f127,plain,(
% 0.22/0.54    ~spl8_2 | spl8_9 | spl8_10 | ~spl8_3),
% 0.22/0.54    inference(avatar_split_clause,[],[f90,f80,f124,f120,f75])).
% 0.22/0.54  fof(f75,plain,(
% 0.22/0.54    spl8_2 <=> v1_funct_2(sK2,sK0,sK1)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.22/0.54  fof(f90,plain,(
% 0.22/0.54    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | ~v1_funct_2(sK2,sK0,sK1) | ~spl8_3),
% 0.22/0.54    inference(resolution,[],[f82,f57])).
% 0.22/0.54  fof(f57,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f25])).
% 0.22/0.54  fof(f25,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.54    inference(flattening,[],[f24])).
% 0.22/0.54  fof(f24,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.54    inference(ennf_transformation,[],[f10])).
% 0.22/0.54  fof(f10,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.22/0.54  fof(f82,plain,(
% 0.22/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl8_3),
% 0.22/0.54    inference(avatar_component_clause,[],[f80])).
% 0.22/0.54  fof(f118,plain,(
% 0.22/0.54    ~spl8_3 | ~spl8_8 | spl8_4),
% 0.22/0.54    inference(avatar_split_clause,[],[f99,f85,f115,f80])).
% 0.22/0.54  fof(f85,plain,(
% 0.22/0.54    spl8_4 <=> sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.22/0.54  fof(f99,plain,(
% 0.22/0.54    sK1 != k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl8_4),
% 0.22/0.54    inference(superposition,[],[f87,f49])).
% 0.22/0.54  fof(f49,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f22])).
% 0.22/0.54  fof(f22,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.54    inference(ennf_transformation,[],[f9])).
% 0.22/0.54  fof(f9,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.22/0.54  fof(f87,plain,(
% 0.22/0.54    sK1 != k2_relset_1(sK0,sK1,sK2) | spl8_4),
% 0.22/0.54    inference(avatar_component_clause,[],[f85])).
% 0.22/0.54  fof(f109,plain,(
% 0.22/0.54    spl8_7 | ~spl8_3),
% 0.22/0.54    inference(avatar_split_clause,[],[f92,f80,f106])).
% 0.22/0.54  fof(f92,plain,(
% 0.22/0.54    v5_relat_1(sK2,sK1) | ~spl8_3),
% 0.22/0.54    inference(resolution,[],[f82,f51])).
% 0.22/0.54  fof(f51,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f23])).
% 0.22/0.54  fof(f23,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.54    inference(ennf_transformation,[],[f7])).
% 0.22/0.54  fof(f7,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.22/0.54  fof(f98,plain,(
% 0.22/0.54    spl8_5 | ~spl8_3),
% 0.22/0.54    inference(avatar_split_clause,[],[f93,f80,f95])).
% 0.22/0.54  fof(f93,plain,(
% 0.22/0.54    v1_relat_1(sK2) | ~spl8_3),
% 0.22/0.54    inference(resolution,[],[f82,f47])).
% 0.22/0.54  fof(f47,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f20])).
% 0.22/0.54  fof(f20,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.54    inference(ennf_transformation,[],[f6])).
% 0.22/0.54  fof(f6,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.54  fof(f88,plain,(
% 0.22/0.54    ~spl8_4),
% 0.22/0.54    inference(avatar_split_clause,[],[f31,f85])).
% 0.22/0.54  fof(f31,plain,(
% 0.22/0.54    sK1 != k2_relset_1(sK0,sK1,sK2)),
% 0.22/0.54    inference(cnf_transformation,[],[f14])).
% 0.22/0.54  fof(f83,plain,(
% 0.22/0.54    spl8_3),
% 0.22/0.54    inference(avatar_split_clause,[],[f30,f80])).
% 0.22/0.54  fof(f30,plain,(
% 0.22/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.54    inference(cnf_transformation,[],[f14])).
% 0.22/0.54  fof(f78,plain,(
% 0.22/0.54    spl8_2),
% 0.22/0.54    inference(avatar_split_clause,[],[f29,f75])).
% 0.22/0.54  fof(f29,plain,(
% 0.22/0.54    v1_funct_2(sK2,sK0,sK1)),
% 0.22/0.54    inference(cnf_transformation,[],[f14])).
% 0.22/0.54  % SZS output end Proof for theBenchmark
% 0.22/0.54  % (557)------------------------------
% 0.22/0.54  % (557)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (557)Termination reason: Refutation
% 0.22/0.54  
% 0.22/0.54  % (557)Memory used [KB]: 10874
% 0.22/0.54  % (557)Time elapsed: 0.061 s
% 0.22/0.54  % (557)------------------------------
% 0.22/0.54  % (557)------------------------------
% 0.22/0.54  % (535)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.54  % (533)Success in time 0.168 s
%------------------------------------------------------------------------------
