%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:50 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 194 expanded)
%              Number of leaves         :   20 (  52 expanded)
%              Depth                    :   11
%              Number of atoms          :  263 ( 735 expanded)
%              Number of equality atoms :   56 ( 191 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f301,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f99,f103,f117,f125,f129,f172,f193,f239,f300])).

fof(f300,plain,
    ( ~ spl6_2
    | spl6_8 ),
    inference(avatar_contradiction_clause,[],[f297])).

fof(f297,plain,
    ( $false
    | ~ spl6_2
    | spl6_8 ),
    inference(unit_resulting_resolution,[],[f52,f288,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
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

fof(f288,plain,
    ( r2_hidden(sK4(k2_relat_1(sK2),k1_xboole_0),k1_xboole_0)
    | ~ spl6_2
    | spl6_8 ),
    inference(unit_resulting_resolution,[],[f252,f256,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X1)
      | r2_hidden(sK4(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

fof(f256,plain,
    ( ~ r2_hidden(sK4(k2_relat_1(sK2),k1_xboole_0),k2_relat_1(sK2))
    | ~ spl6_2
    | spl6_8 ),
    inference(backward_demodulation,[],[f170,f94])).

fof(f94,plain,
    ( k1_xboole_0 = sK1
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl6_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f170,plain,
    ( ~ r2_hidden(sK4(k2_relat_1(sK2),sK1),k2_relat_1(sK2))
    | spl6_8 ),
    inference(avatar_component_clause,[],[f169])).

fof(f169,plain,
    ( spl6_8
  <=> r2_hidden(sK4(k2_relat_1(sK2),sK1),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f252,plain,
    ( k1_xboole_0 != k2_relat_1(sK2)
    | ~ spl6_2 ),
    inference(backward_demodulation,[],[f81,f94])).

fof(f81,plain,(
    sK1 != k2_relat_1(sK2) ),
    inference(superposition,[],[f33,f60])).

fof(f60,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f32,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f32,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f15])).

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
    inference(flattening,[],[f14])).

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
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
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
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
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

fof(f33,plain,(
    sK1 != k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f52,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f239,plain,(
    ~ spl6_8 ),
    inference(avatar_contradiction_clause,[],[f235])).

fof(f235,plain,
    ( $false
    | ~ spl6_8 ),
    inference(unit_resulting_resolution,[],[f72,f171,f224,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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

fof(f224,plain,
    ( ~ r2_hidden(sK4(k2_relat_1(sK2),sK1),sK1)
    | ~ spl6_8 ),
    inference(unit_resulting_resolution,[],[f81,f171,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | ~ r2_hidden(sK4(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f171,plain,
    ( r2_hidden(sK4(k2_relat_1(sK2),sK1),k2_relat_1(sK2))
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f169])).

fof(f72,plain,(
    r1_tarski(k2_relat_1(sK2),sK1) ),
    inference(unit_resulting_resolution,[],[f61,f64,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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

fof(f64,plain,(
    v5_relat_1(sK2,sK1) ),
    inference(unit_resulting_resolution,[],[f32,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f61,plain,(
    v1_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f32,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f193,plain,(
    ~ spl6_7 ),
    inference(avatar_contradiction_clause,[],[f187])).

fof(f187,plain,
    ( $false
    | ~ spl6_7 ),
    inference(unit_resulting_resolution,[],[f81,f167])).

fof(f167,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f165])).

fof(f165,plain,
    ( spl6_7
  <=> sK1 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f172,plain,
    ( spl6_7
    | spl6_8
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f153,f115,f169,f165])).

fof(f115,plain,
    ( spl6_6
  <=> ! [X0] :
        ( ~ r2_hidden(sK3(X0),sK0)
        | ~ r2_hidden(X0,sK1)
        | r2_hidden(X0,k2_relat_1(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f153,plain,
    ( r2_hidden(sK4(k2_relat_1(sK2),sK1),k2_relat_1(sK2))
    | sK1 = k2_relat_1(sK2)
    | ~ spl6_6 ),
    inference(factoring,[],[f134])).

fof(f134,plain,
    ( ! [X1] :
        ( r2_hidden(sK4(X1,sK1),k2_relat_1(sK2))
        | r2_hidden(sK4(X1,sK1),X1)
        | sK1 = X1 )
    | ~ spl6_6 ),
    inference(resolution,[],[f131,f35])).

fof(f131,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | r2_hidden(X0,k2_relat_1(sK2)) )
    | ~ spl6_6 ),
    inference(duplicate_literal_removal,[],[f130])).

fof(f130,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | r2_hidden(X0,k2_relat_1(sK2))
        | ~ r2_hidden(X0,sK1) )
    | ~ spl6_6 ),
    inference(resolution,[],[f116,f28])).

fof(f28,plain,(
    ! [X3] :
      ( r2_hidden(sK3(X3),sK0)
      | ~ r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f116,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3(X0),sK0)
        | ~ r2_hidden(X0,sK1)
        | r2_hidden(X0,k2_relat_1(sK2)) )
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f115])).

fof(f129,plain,(
    spl6_5 ),
    inference(avatar_contradiction_clause,[],[f126])).

fof(f126,plain,
    ( $false
    | spl6_5 ),
    inference(unit_resulting_resolution,[],[f30,f113])).

fof(f113,plain,
    ( ~ v1_funct_1(sK2)
    | spl6_5 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl6_5
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f30,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f125,plain,(
    spl6_4 ),
    inference(avatar_contradiction_clause,[],[f120])).

fof(f120,plain,
    ( $false
    | spl6_4 ),
    inference(unit_resulting_resolution,[],[f32,f109,f42])).

fof(f109,plain,
    ( ~ v1_relat_1(sK2)
    | spl6_4 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl6_4
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f117,plain,
    ( ~ spl6_4
    | ~ spl6_5
    | spl6_6
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f104,f96,f115,f111,f107])).

fof(f96,plain,
    ( spl6_3
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f104,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3(X0),sK0)
        | r2_hidden(X0,k2_relat_1(sK2))
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2)
        | ~ r2_hidden(X0,sK1) )
    | ~ spl6_3 ),
    inference(backward_demodulation,[],[f82,f98])).

fof(f98,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f96])).

fof(f82,plain,(
    ! [X0] :
      ( r2_hidden(X0,k2_relat_1(sK2))
      | ~ v1_funct_1(sK2)
      | ~ r2_hidden(sK3(X0),k1_relat_1(sK2))
      | ~ v1_relat_1(sK2)
      | ~ r2_hidden(X0,sK1) ) ),
    inference(superposition,[],[f37,f29])).

fof(f29,plain,(
    ! [X3] :
      ( k1_funct_1(sK2,sK3(X3)) = X3
      | ~ r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).

fof(f103,plain,(
    spl6_1 ),
    inference(avatar_contradiction_clause,[],[f100])).

fof(f100,plain,
    ( $false
    | spl6_1 ),
    inference(unit_resulting_resolution,[],[f31,f90])).

fof(f90,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl6_1
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f31,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f99,plain,
    ( ~ spl6_1
    | spl6_2
    | spl6_3 ),
    inference(avatar_split_clause,[],[f71,f96,f92,f88])).

fof(f71,plain,
    ( sK0 = k1_relat_1(sK2)
    | k1_xboole_0 = sK1
    | ~ v1_funct_2(sK2,sK0,sK1) ),
    inference(forward_demodulation,[],[f69,f62])).

fof(f62,plain,(
    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) ),
    inference(unit_resulting_resolution,[],[f32,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f69,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ v1_funct_2(sK2,sK0,sK1) ),
    inference(resolution,[],[f32,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

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
    inference(flattening,[],[f23])).

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
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:33:16 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.51  % (32145)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.51  % (32146)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.51  % (32153)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.51  % (32162)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.52  % (32152)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.52  % (32152)Refutation not found, incomplete strategy% (32152)------------------------------
% 0.22/0.52  % (32152)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (32152)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (32152)Memory used [KB]: 10746
% 0.22/0.52  % (32152)Time elapsed: 0.110 s
% 0.22/0.52  % (32152)------------------------------
% 0.22/0.52  % (32152)------------------------------
% 0.22/0.52  % (32145)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f301,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(avatar_sat_refutation,[],[f99,f103,f117,f125,f129,f172,f193,f239,f300])).
% 0.22/0.52  fof(f300,plain,(
% 0.22/0.52    ~spl6_2 | spl6_8),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f297])).
% 0.22/0.52  fof(f297,plain,(
% 0.22/0.52    $false | (~spl6_2 | spl6_8)),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f52,f288,f38])).
% 0.22/0.52  fof(f38,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f20])).
% 0.22/0.52  fof(f20,plain,(
% 0.22/0.52    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.22/0.52    inference(ennf_transformation,[],[f6])).
% 0.22/0.52  fof(f6,axiom,(
% 0.22/0.52    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.22/0.52  fof(f288,plain,(
% 0.22/0.52    r2_hidden(sK4(k2_relat_1(sK2),k1_xboole_0),k1_xboole_0) | (~spl6_2 | spl6_8)),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f252,f256,f35])).
% 0.22/0.52  fof(f35,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X1) | r2_hidden(sK4(X0,X1),X0) | X0 = X1) )),
% 0.22/0.52    inference(cnf_transformation,[],[f17])).
% 0.22/0.52  fof(f17,plain,(
% 0.22/0.52    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 0.22/0.52    inference(ennf_transformation,[],[f2])).
% 0.22/0.52  fof(f2,axiom,(
% 0.22/0.52    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).
% 0.22/0.52  fof(f256,plain,(
% 0.22/0.52    ~r2_hidden(sK4(k2_relat_1(sK2),k1_xboole_0),k2_relat_1(sK2)) | (~spl6_2 | spl6_8)),
% 0.22/0.52    inference(backward_demodulation,[],[f170,f94])).
% 0.22/0.52  fof(f94,plain,(
% 0.22/0.52    k1_xboole_0 = sK1 | ~spl6_2),
% 0.22/0.52    inference(avatar_component_clause,[],[f92])).
% 0.22/0.52  fof(f92,plain,(
% 0.22/0.52    spl6_2 <=> k1_xboole_0 = sK1),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.22/0.52  fof(f170,plain,(
% 0.22/0.52    ~r2_hidden(sK4(k2_relat_1(sK2),sK1),k2_relat_1(sK2)) | spl6_8),
% 0.22/0.52    inference(avatar_component_clause,[],[f169])).
% 0.22/0.52  fof(f169,plain,(
% 0.22/0.52    spl6_8 <=> r2_hidden(sK4(k2_relat_1(sK2),sK1),k2_relat_1(sK2))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.22/0.52  fof(f252,plain,(
% 0.22/0.52    k1_xboole_0 != k2_relat_1(sK2) | ~spl6_2),
% 0.22/0.52    inference(backward_demodulation,[],[f81,f94])).
% 0.22/0.52  fof(f81,plain,(
% 0.22/0.52    sK1 != k2_relat_1(sK2)),
% 0.22/0.52    inference(superposition,[],[f33,f60])).
% 0.22/0.52  fof(f60,plain,(
% 0.22/0.52    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f32,f34])).
% 0.22/0.52  fof(f34,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f16])).
% 0.22/0.52  fof(f16,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(ennf_transformation,[],[f10])).
% 0.22/0.52  fof(f10,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.22/0.52  fof(f32,plain,(
% 0.22/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.52    inference(cnf_transformation,[],[f15])).
% 0.22/0.52  fof(f15,plain,(
% 0.22/0.52    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.22/0.52    inference(flattening,[],[f14])).
% 0.22/0.52  fof(f14,plain,(
% 0.22/0.52    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.22/0.52    inference(ennf_transformation,[],[f13])).
% 0.22/0.52  fof(f13,negated_conjecture,(
% 0.22/0.52    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 0.22/0.52    inference(negated_conjecture,[],[f12])).
% 0.22/0.52  fof(f12,conjecture,(
% 0.22/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_funct_2)).
% 0.22/0.52  fof(f33,plain,(
% 0.22/0.52    sK1 != k2_relset_1(sK0,sK1,sK2)),
% 0.22/0.52    inference(cnf_transformation,[],[f15])).
% 0.22/0.52  fof(f52,plain,(
% 0.22/0.52    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f3])).
% 0.22/0.52  fof(f3,axiom,(
% 0.22/0.52    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.52  fof(f239,plain,(
% 0.22/0.52    ~spl6_8),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f235])).
% 0.22/0.52  fof(f235,plain,(
% 0.22/0.52    $false | ~spl6_8),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f72,f171,f224,f39])).
% 0.22/0.52  fof(f39,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f21])).
% 0.22/0.52  fof(f21,plain,(
% 0.22/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f1])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.52  fof(f224,plain,(
% 0.22/0.52    ~r2_hidden(sK4(k2_relat_1(sK2),sK1),sK1) | ~spl6_8),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f81,f171,f36])).
% 0.22/0.52  fof(f36,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | ~r2_hidden(sK4(X0,X1),X0) | X0 = X1) )),
% 0.22/0.52    inference(cnf_transformation,[],[f17])).
% 0.22/0.52  fof(f171,plain,(
% 0.22/0.52    r2_hidden(sK4(k2_relat_1(sK2),sK1),k2_relat_1(sK2)) | ~spl6_8),
% 0.22/0.52    inference(avatar_component_clause,[],[f169])).
% 0.22/0.52  fof(f72,plain,(
% 0.22/0.52    r1_tarski(k2_relat_1(sK2),sK1)),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f61,f64,f50])).
% 0.22/0.52  fof(f50,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f25])).
% 0.22/0.52  fof(f25,plain,(
% 0.22/0.52    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.52    inference(ennf_transformation,[],[f4])).
% 0.22/0.52  fof(f4,axiom,(
% 0.22/0.52    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 0.22/0.52  fof(f64,plain,(
% 0.22/0.52    v5_relat_1(sK2,sK1)),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f32,f54])).
% 0.22/0.52  fof(f54,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f27])).
% 0.22/0.52  fof(f27,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(ennf_transformation,[],[f8])).
% 0.22/0.52  fof(f8,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.22/0.52  fof(f61,plain,(
% 0.22/0.52    v1_relat_1(sK2)),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f32,f42])).
% 0.22/0.52  fof(f42,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f22])).
% 0.22/0.52  fof(f22,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(ennf_transformation,[],[f7])).
% 0.22/0.52  fof(f7,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.52  fof(f193,plain,(
% 0.22/0.52    ~spl6_7),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f187])).
% 0.22/0.52  fof(f187,plain,(
% 0.22/0.52    $false | ~spl6_7),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f81,f167])).
% 0.22/0.52  fof(f167,plain,(
% 0.22/0.52    sK1 = k2_relat_1(sK2) | ~spl6_7),
% 0.22/0.52    inference(avatar_component_clause,[],[f165])).
% 0.22/0.52  fof(f165,plain,(
% 0.22/0.52    spl6_7 <=> sK1 = k2_relat_1(sK2)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.22/0.52  fof(f172,plain,(
% 0.22/0.52    spl6_7 | spl6_8 | ~spl6_6),
% 0.22/0.52    inference(avatar_split_clause,[],[f153,f115,f169,f165])).
% 0.22/0.52  fof(f115,plain,(
% 0.22/0.52    spl6_6 <=> ! [X0] : (~r2_hidden(sK3(X0),sK0) | ~r2_hidden(X0,sK1) | r2_hidden(X0,k2_relat_1(sK2)))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.22/0.52  fof(f153,plain,(
% 0.22/0.52    r2_hidden(sK4(k2_relat_1(sK2),sK1),k2_relat_1(sK2)) | sK1 = k2_relat_1(sK2) | ~spl6_6),
% 0.22/0.52    inference(factoring,[],[f134])).
% 0.22/0.52  fof(f134,plain,(
% 0.22/0.52    ( ! [X1] : (r2_hidden(sK4(X1,sK1),k2_relat_1(sK2)) | r2_hidden(sK4(X1,sK1),X1) | sK1 = X1) ) | ~spl6_6),
% 0.22/0.52    inference(resolution,[],[f131,f35])).
% 0.22/0.52  fof(f131,plain,(
% 0.22/0.52    ( ! [X0] : (~r2_hidden(X0,sK1) | r2_hidden(X0,k2_relat_1(sK2))) ) | ~spl6_6),
% 0.22/0.52    inference(duplicate_literal_removal,[],[f130])).
% 0.22/0.52  fof(f130,plain,(
% 0.22/0.52    ( ! [X0] : (~r2_hidden(X0,sK1) | r2_hidden(X0,k2_relat_1(sK2)) | ~r2_hidden(X0,sK1)) ) | ~spl6_6),
% 0.22/0.52    inference(resolution,[],[f116,f28])).
% 0.22/0.52  fof(f28,plain,(
% 0.22/0.52    ( ! [X3] : (r2_hidden(sK3(X3),sK0) | ~r2_hidden(X3,sK1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f15])).
% 0.22/0.52  fof(f116,plain,(
% 0.22/0.52    ( ! [X0] : (~r2_hidden(sK3(X0),sK0) | ~r2_hidden(X0,sK1) | r2_hidden(X0,k2_relat_1(sK2))) ) | ~spl6_6),
% 0.22/0.52    inference(avatar_component_clause,[],[f115])).
% 0.22/0.52  fof(f129,plain,(
% 0.22/0.52    spl6_5),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f126])).
% 0.22/0.52  fof(f126,plain,(
% 0.22/0.52    $false | spl6_5),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f30,f113])).
% 0.22/0.52  fof(f113,plain,(
% 0.22/0.52    ~v1_funct_1(sK2) | spl6_5),
% 0.22/0.52    inference(avatar_component_clause,[],[f111])).
% 0.22/0.52  fof(f111,plain,(
% 0.22/0.52    spl6_5 <=> v1_funct_1(sK2)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.22/0.52  fof(f30,plain,(
% 0.22/0.52    v1_funct_1(sK2)),
% 0.22/0.52    inference(cnf_transformation,[],[f15])).
% 0.22/0.52  fof(f125,plain,(
% 0.22/0.52    spl6_4),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f120])).
% 0.22/0.52  fof(f120,plain,(
% 0.22/0.52    $false | spl6_4),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f32,f109,f42])).
% 0.22/0.52  fof(f109,plain,(
% 0.22/0.52    ~v1_relat_1(sK2) | spl6_4),
% 0.22/0.52    inference(avatar_component_clause,[],[f107])).
% 0.22/0.52  fof(f107,plain,(
% 0.22/0.52    spl6_4 <=> v1_relat_1(sK2)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.22/0.52  fof(f117,plain,(
% 0.22/0.52    ~spl6_4 | ~spl6_5 | spl6_6 | ~spl6_3),
% 0.22/0.52    inference(avatar_split_clause,[],[f104,f96,f115,f111,f107])).
% 0.22/0.52  fof(f96,plain,(
% 0.22/0.52    spl6_3 <=> sK0 = k1_relat_1(sK2)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.22/0.52  fof(f104,plain,(
% 0.22/0.52    ( ! [X0] : (~r2_hidden(sK3(X0),sK0) | r2_hidden(X0,k2_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~r2_hidden(X0,sK1)) ) | ~spl6_3),
% 0.22/0.52    inference(backward_demodulation,[],[f82,f98])).
% 0.22/0.52  fof(f98,plain,(
% 0.22/0.52    sK0 = k1_relat_1(sK2) | ~spl6_3),
% 0.22/0.52    inference(avatar_component_clause,[],[f96])).
% 0.22/0.52  fof(f82,plain,(
% 0.22/0.52    ( ! [X0] : (r2_hidden(X0,k2_relat_1(sK2)) | ~v1_funct_1(sK2) | ~r2_hidden(sK3(X0),k1_relat_1(sK2)) | ~v1_relat_1(sK2) | ~r2_hidden(X0,sK1)) )),
% 0.22/0.52    inference(superposition,[],[f37,f29])).
% 0.22/0.52  fof(f29,plain,(
% 0.22/0.52    ( ! [X3] : (k1_funct_1(sK2,sK3(X3)) = X3 | ~r2_hidden(X3,sK1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f15])).
% 0.22/0.52  fof(f37,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~v1_funct_1(X1) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f19])).
% 0.22/0.52  fof(f19,plain,(
% 0.22/0.52    ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.52    inference(flattening,[],[f18])).
% 0.22/0.52  fof(f18,plain,(
% 0.22/0.52    ! [X0,X1] : ((r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.22/0.52    inference(ennf_transformation,[],[f5])).
% 0.22/0.52  fof(f5,axiom,(
% 0.22/0.52    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).
% 0.22/0.52  fof(f103,plain,(
% 0.22/0.52    spl6_1),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f100])).
% 0.22/0.52  fof(f100,plain,(
% 0.22/0.52    $false | spl6_1),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f31,f90])).
% 0.22/0.52  fof(f90,plain,(
% 0.22/0.52    ~v1_funct_2(sK2,sK0,sK1) | spl6_1),
% 0.22/0.52    inference(avatar_component_clause,[],[f88])).
% 0.22/0.52  fof(f88,plain,(
% 0.22/0.52    spl6_1 <=> v1_funct_2(sK2,sK0,sK1)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.22/0.52  fof(f31,plain,(
% 0.22/0.52    v1_funct_2(sK2,sK0,sK1)),
% 0.22/0.52    inference(cnf_transformation,[],[f15])).
% 0.22/0.52  fof(f99,plain,(
% 0.22/0.52    ~spl6_1 | spl6_2 | spl6_3),
% 0.22/0.52    inference(avatar_split_clause,[],[f71,f96,f92,f88])).
% 0.22/0.52  fof(f71,plain,(
% 0.22/0.52    sK0 = k1_relat_1(sK2) | k1_xboole_0 = sK1 | ~v1_funct_2(sK2,sK0,sK1)),
% 0.22/0.52    inference(forward_demodulation,[],[f69,f62])).
% 0.22/0.52  fof(f62,plain,(
% 0.22/0.52    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f32,f51])).
% 0.22/0.52  fof(f51,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f26])).
% 0.22/0.52  fof(f26,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(ennf_transformation,[],[f9])).
% 0.22/0.52  fof(f9,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.52  fof(f69,plain,(
% 0.22/0.52    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | ~v1_funct_2(sK2,sK0,sK1)),
% 0.22/0.52    inference(resolution,[],[f32,f48])).
% 0.22/0.52  fof(f48,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f24])).
% 0.22/0.52  fof(f24,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(flattening,[],[f23])).
% 0.22/0.52  fof(f23,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(ennf_transformation,[],[f11])).
% 0.22/0.52  fof(f11,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (32145)------------------------------
% 0.22/0.52  % (32145)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (32145)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (32145)Memory used [KB]: 6268
% 0.22/0.52  % (32145)Time elapsed: 0.097 s
% 0.22/0.52  % (32145)------------------------------
% 0.22/0.52  % (32145)------------------------------
% 0.22/0.52  % (32140)Success in time 0.159 s
%------------------------------------------------------------------------------
