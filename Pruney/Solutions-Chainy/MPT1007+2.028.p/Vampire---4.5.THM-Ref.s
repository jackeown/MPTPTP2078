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
% DateTime   : Thu Dec  3 13:03:55 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  152 ( 248 expanded)
%              Number of leaves         :   40 ( 103 expanded)
%              Depth                    :    9
%              Number of atoms          :  386 ( 610 expanded)
%              Number of equality atoms :   88 ( 137 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f662,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f98,f103,f108,f113,f118,f152,f157,f162,f182,f200,f219,f231,f260,f299,f350,f369,f419,f582,f584,f635,f661])).

fof(f661,plain,(
    spl8_54 ),
    inference(avatar_contradiction_clause,[],[f660])).

fof(f660,plain,
    ( $false
    | spl8_54 ),
    inference(resolution,[],[f634,f49])).

fof(f49,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f634,plain,
    ( ~ r1_tarski(k1_xboole_0,k4_tarski(sK3(k2_enumset1(sK0,sK0,sK0,sK0)),sK5(k1_xboole_0,sK3(k2_enumset1(sK0,sK0,sK0,sK0)))))
    | spl8_54 ),
    inference(avatar_component_clause,[],[f632])).

fof(f632,plain,
    ( spl8_54
  <=> r1_tarski(k1_xboole_0,k4_tarski(sK3(k2_enumset1(sK0,sK0,sK0,sK0)),sK5(k1_xboole_0,sK3(k2_enumset1(sK0,sK0,sK0,sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_54])])).

fof(f635,plain,
    ( ~ spl8_54
    | ~ spl8_53 ),
    inference(avatar_split_clause,[],[f630,f579,f632])).

fof(f579,plain,
    ( spl8_53
  <=> r2_hidden(k4_tarski(sK3(k2_enumset1(sK0,sK0,sK0,sK0)),sK5(k1_xboole_0,sK3(k2_enumset1(sK0,sK0,sK0,sK0)))),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_53])])).

fof(f630,plain,
    ( ~ r1_tarski(k1_xboole_0,k4_tarski(sK3(k2_enumset1(sK0,sK0,sK0,sK0)),sK5(k1_xboole_0,sK3(k2_enumset1(sK0,sK0,sK0,sK0)))))
    | ~ spl8_53 ),
    inference(resolution,[],[f581,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f581,plain,
    ( r2_hidden(k4_tarski(sK3(k2_enumset1(sK0,sK0,sK0,sK0)),sK5(k1_xboole_0,sK3(k2_enumset1(sK0,sK0,sK0,sK0)))),k1_xboole_0)
    | ~ spl8_53 ),
    inference(avatar_component_clause,[],[f579])).

fof(f584,plain,(
    ~ spl8_52 ),
    inference(avatar_contradiction_clause,[],[f583])).

fof(f583,plain,
    ( $false
    | ~ spl8_52 ),
    inference(resolution,[],[f577,f84])).

fof(f84,plain,(
    ! [X0,X1] : ~ v1_xboole_0(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f56,f79])).

fof(f79,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f57,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f57,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f56,plain,(
    ! [X0,X1] : ~ v1_xboole_0(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : ~ v1_xboole_0(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_xboole_0)).

fof(f577,plain,
    ( v1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl8_52 ),
    inference(avatar_component_clause,[],[f575])).

fof(f575,plain,
    ( spl8_52
  <=> v1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_52])])).

fof(f582,plain,
    ( spl8_52
    | spl8_53
    | ~ spl8_37 ),
    inference(avatar_split_clause,[],[f571,f416,f579,f575])).

fof(f416,plain,
    ( spl8_37
  <=> sP6(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_37])])).

fof(f571,plain,
    ( r2_hidden(k4_tarski(sK3(k2_enumset1(sK0,sK0,sK0,sK0)),sK5(k1_xboole_0,sK3(k2_enumset1(sK0,sK0,sK0,sK0)))),k1_xboole_0)
    | v1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl8_37 ),
    inference(resolution,[],[f212,f418])).

fof(f418,plain,
    ( sP6(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl8_37 ),
    inference(avatar_component_clause,[],[f416])).

fof(f212,plain,(
    ! [X0,X1] :
      ( ~ sP6(X1,X0)
      | r2_hidden(k4_tarski(sK3(X0),sK5(X1,sK3(X0))),X1)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f91,f120])).

fof(f120,plain,(
    ! [X1] :
      ( r2_hidden(sK3(X1),X1)
      | v1_xboole_0(X1) ) ),
    inference(resolution,[],[f61,f55])).

fof(f55,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f91,plain,(
    ! [X2,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | r2_hidden(k4_tarski(X3,sK5(X2,X3)),X2)
      | ~ sP6(X2,X1) ) ),
    inference(general_splitting,[],[f77,f90_D])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k1_relset_1(X1,X0,X2) != X1
      | sP6(X2,X1) ) ),
    inference(cnf_transformation,[],[f90_D])).

fof(f90_D,plain,(
    ! [X1,X2] :
      ( ! [X0] :
          ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | k1_relset_1(X1,X0,X2) != X1 )
    <=> ~ sP6(X2,X1) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP6])])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k1_relset_1(X1,X0,X2) != X1
      | ~ r2_hidden(X3,X1)
      | r2_hidden(k4_tarski(X3,sK5(X2,X3)),X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
            | ~ r2_hidden(X3,X1) )
      <=> k1_relset_1(X1,X0,X2) = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( ! [X3] :
            ~ ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),X2)
              & r2_hidden(X3,X1) )
      <=> k1_relset_1(X1,X0,X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relset_1)).

fof(f419,plain,
    ( spl8_37
    | ~ spl8_13
    | ~ spl8_18 ),
    inference(avatar_split_clause,[],[f384,f224,f175,f416])).

fof(f175,plain,
    ( spl8_13
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f224,plain,
    ( spl8_18
  <=> sP6(sK2,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f384,plain,
    ( sP6(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl8_13
    | ~ spl8_18 ),
    inference(backward_demodulation,[],[f226,f177])).

fof(f177,plain,
    ( k1_xboole_0 = sK2
    | ~ spl8_13 ),
    inference(avatar_component_clause,[],[f175])).

fof(f226,plain,
    ( sP6(sK2,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl8_18 ),
    inference(avatar_component_clause,[],[f224])).

fof(f369,plain,
    ( spl8_14
    | ~ spl8_10
    | ~ spl8_17
    | ~ spl8_33 ),
    inference(avatar_split_clause,[],[f368,f347,f216,f159,f179])).

fof(f179,plain,
    ( spl8_14
  <=> k1_xboole_0 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f159,plain,
    ( spl8_10
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f216,plain,
    ( spl8_17
  <=> k2_relat_1(sK2) = k9_relat_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

fof(f347,plain,
    ( spl8_33
  <=> k1_xboole_0 = k11_relat_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_33])])).

fof(f368,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | ~ spl8_10
    | ~ spl8_17
    | ~ spl8_33 ),
    inference(forward_demodulation,[],[f365,f349])).

fof(f349,plain,
    ( k1_xboole_0 = k11_relat_1(sK2,sK0)
    | ~ spl8_33 ),
    inference(avatar_component_clause,[],[f347])).

fof(f365,plain,
    ( k2_relat_1(sK2) = k11_relat_1(sK2,sK0)
    | ~ spl8_10
    | ~ spl8_17 ),
    inference(superposition,[],[f218,f210])).

fof(f210,plain,
    ( ! [X4] : k11_relat_1(sK2,X4) = k9_relat_1(sK2,k2_enumset1(X4,X4,X4,X4))
    | ~ spl8_10 ),
    inference(resolution,[],[f83,f161])).

fof(f161,plain,
    ( v1_relat_1(sK2)
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f159])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k11_relat_1(X0,X1) = k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f54,f80])).

fof(f80,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f51,f79])).

fof(f51,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

fof(f218,plain,
    ( k2_relat_1(sK2) = k9_relat_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl8_17 ),
    inference(avatar_component_clause,[],[f216])).

fof(f350,plain,
    ( spl8_33
    | spl8_1
    | ~ spl8_10
    | ~ spl8_23 ),
    inference(avatar_split_clause,[],[f342,f258,f159,f95,f347])).

fof(f95,plain,
    ( spl8_1
  <=> r2_hidden(k1_funct_1(sK2,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f258,plain,
    ( spl8_23
  <=> ! [X2] :
        ( ~ r2_hidden(X2,k1_relat_1(sK2))
        | r2_hidden(k1_funct_1(sK2,X2),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).

fof(f342,plain,
    ( k1_xboole_0 = k11_relat_1(sK2,sK0)
    | spl8_1
    | ~ spl8_10
    | ~ spl8_23 ),
    inference(resolution,[],[f265,f97])).

fof(f97,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK0),sK1)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f95])).

fof(f265,plain,
    ( ! [X0] :
        ( r2_hidden(k1_funct_1(sK2,X0),sK1)
        | k1_xboole_0 = k11_relat_1(sK2,X0) )
    | ~ spl8_10
    | ~ spl8_23 ),
    inference(resolution,[],[f259,f205])).

fof(f205,plain,
    ( ! [X4] :
        ( r2_hidden(X4,k1_relat_1(sK2))
        | k1_xboole_0 = k11_relat_1(sK2,X4) )
    | ~ spl8_10 ),
    inference(resolution,[],[f59,f161])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_xboole_0 = k11_relat_1(X1,X0)
      | r2_hidden(X0,k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

fof(f259,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,k1_relat_1(sK2))
        | r2_hidden(k1_funct_1(sK2,X2),sK1) )
    | ~ spl8_23 ),
    inference(avatar_component_clause,[],[f258])).

fof(f299,plain,
    ( ~ spl8_4
    | spl8_19
    | spl8_2
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f298,f105,f100,f228,f110])).

fof(f110,plain,
    ( spl8_4
  <=> v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f228,plain,
    ( spl8_19
  <=> k2_enumset1(sK0,sK0,sK0,sK0) = k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).

fof(f100,plain,
    ( spl8_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f105,plain,
    ( spl8_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f298,plain,
    ( k1_xboole_0 = sK1
    | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2)
    | ~ v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1)
    | ~ spl8_3 ),
    inference(resolution,[],[f74,f107])).

fof(f107,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f105])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f39,plain,(
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
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
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

fof(f260,plain,
    ( spl8_23
    | ~ spl8_5
    | ~ spl8_10
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f246,f149,f159,f115,f258])).

fof(f115,plain,
    ( spl8_5
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f149,plain,
    ( spl8_8
  <=> v5_relat_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f246,plain,
    ( ! [X2] :
        ( ~ v1_relat_1(sK2)
        | ~ v1_funct_1(sK2)
        | ~ r2_hidden(X2,k1_relat_1(sK2))
        | r2_hidden(k1_funct_1(sK2,X2),sK1) )
    | ~ spl8_8 ),
    inference(resolution,[],[f62,f151])).

fof(f151,plain,
    ( v5_relat_1(sK2,sK1)
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f149])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | r2_hidden(k1_funct_1(X1,X2),X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(k1_funct_1(X1,X2),X0)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(k1_funct_1(X1,X2),X0)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => r2_hidden(k1_funct_1(X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_funct_1)).

fof(f231,plain,
    ( spl8_18
    | ~ spl8_19
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f222,f105,f228,f224])).

fof(f222,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) != k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2)
    | sP6(sK2,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl8_3 ),
    inference(resolution,[],[f90,f107])).

fof(f219,plain,
    ( spl8_17
    | ~ spl8_10
    | ~ spl8_16 ),
    inference(avatar_split_clause,[],[f214,f197,f159,f216])).

fof(f197,plain,
    ( spl8_16
  <=> sK2 = k7_relat_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f214,plain,
    ( k2_relat_1(sK2) = k9_relat_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl8_10
    | ~ spl8_16 ),
    inference(superposition,[],[f190,f199])).

fof(f199,plain,
    ( sK2 = k7_relat_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl8_16 ),
    inference(avatar_component_clause,[],[f197])).

fof(f190,plain,
    ( ! [X4] : k2_relat_1(k7_relat_1(sK2,X4)) = k9_relat_1(sK2,X4)
    | ~ spl8_10 ),
    inference(resolution,[],[f58,f161])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

% (19733)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f200,plain,
    ( spl8_16
    | ~ spl8_10
    | ~ spl8_9 ),
    inference(avatar_split_clause,[],[f195,f154,f159,f197])).

fof(f154,plain,
    ( spl8_9
  <=> v4_relat_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f195,plain,
    ( ~ v1_relat_1(sK2)
    | sK2 = k7_relat_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl8_9 ),
    inference(resolution,[],[f156,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(f156,plain,
    ( v4_relat_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f154])).

fof(f182,plain,
    ( spl8_13
    | ~ spl8_14
    | ~ spl8_10 ),
    inference(avatar_split_clause,[],[f172,f159,f179,f175])).

fof(f172,plain,
    ( k1_xboole_0 != k2_relat_1(sK2)
    | k1_xboole_0 = sK2
    | ~ spl8_10 ),
    inference(resolution,[],[f161,f53])).

fof(f53,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 != k2_relat_1(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(f162,plain,
    ( spl8_10
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f146,f105,f159])).

fof(f146,plain,
    ( v1_relat_1(sK2)
    | ~ spl8_3 ),
    inference(resolution,[],[f107,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f157,plain,
    ( spl8_9
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f145,f105,f154])).

fof(f145,plain,
    ( v4_relat_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl8_3 ),
    inference(resolution,[],[f107,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f152,plain,
    ( spl8_8
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f144,f105,f149])).

fof(f144,plain,
    ( v5_relat_1(sK2,sK1)
    | ~ spl8_3 ),
    inference(resolution,[],[f107,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f118,plain,(
    spl8_5 ),
    inference(avatar_split_clause,[],[f44,f115])).

fof(f44,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_2)).

fof(f113,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f82,f110])).

fof(f82,plain,(
    v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    inference(definition_unfolding,[],[f45,f80])).

fof(f45,plain,(
    v1_funct_2(sK2,k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f108,plain,(
    spl8_3 ),
    inference(avatar_split_clause,[],[f81,f105])).

fof(f81,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f46,f80])).

fof(f46,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f24])).

fof(f103,plain,(
    ~ spl8_2 ),
    inference(avatar_split_clause,[],[f47,f100])).

fof(f47,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f24])).

fof(f98,plain,(
    ~ spl8_1 ),
    inference(avatar_split_clause,[],[f48,f95])).

fof(f48,plain,(
    ~ r2_hidden(k1_funct_1(sK2,sK0),sK1) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:27:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (19747)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.51  % (19741)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.51  % (19741)Refutation not found, incomplete strategy% (19741)------------------------------
% 0.21/0.51  % (19741)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (19743)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (19741)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (19741)Memory used [KB]: 10746
% 0.21/0.51  % (19741)Time elapsed: 0.094 s
% 0.21/0.51  % (19741)------------------------------
% 0.21/0.51  % (19741)------------------------------
% 0.21/0.52  % (19751)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.52  % (19755)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.53  % (19747)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f662,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(avatar_sat_refutation,[],[f98,f103,f108,f113,f118,f152,f157,f162,f182,f200,f219,f231,f260,f299,f350,f369,f419,f582,f584,f635,f661])).
% 0.21/0.53  fof(f661,plain,(
% 0.21/0.53    spl8_54),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f660])).
% 0.21/0.53  fof(f660,plain,(
% 0.21/0.53    $false | spl8_54),
% 0.21/0.53    inference(resolution,[],[f634,f49])).
% 0.21/0.53  fof(f49,plain,(
% 0.21/0.53    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.53  fof(f634,plain,(
% 0.21/0.53    ~r1_tarski(k1_xboole_0,k4_tarski(sK3(k2_enumset1(sK0,sK0,sK0,sK0)),sK5(k1_xboole_0,sK3(k2_enumset1(sK0,sK0,sK0,sK0))))) | spl8_54),
% 0.21/0.53    inference(avatar_component_clause,[],[f632])).
% 0.21/0.53  fof(f632,plain,(
% 0.21/0.53    spl8_54 <=> r1_tarski(k1_xboole_0,k4_tarski(sK3(k2_enumset1(sK0,sK0,sK0,sK0)),sK5(k1_xboole_0,sK3(k2_enumset1(sK0,sK0,sK0,sK0)))))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_54])])).
% 0.21/0.53  fof(f635,plain,(
% 0.21/0.53    ~spl8_54 | ~spl8_53),
% 0.21/0.53    inference(avatar_split_clause,[],[f630,f579,f632])).
% 0.21/0.53  fof(f579,plain,(
% 0.21/0.53    spl8_53 <=> r2_hidden(k4_tarski(sK3(k2_enumset1(sK0,sK0,sK0,sK0)),sK5(k1_xboole_0,sK3(k2_enumset1(sK0,sK0,sK0,sK0)))),k1_xboole_0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_53])])).
% 0.21/0.53  fof(f630,plain,(
% 0.21/0.53    ~r1_tarski(k1_xboole_0,k4_tarski(sK3(k2_enumset1(sK0,sK0,sK0,sK0)),sK5(k1_xboole_0,sK3(k2_enumset1(sK0,sK0,sK0,sK0))))) | ~spl8_53),
% 0.21/0.53    inference(resolution,[],[f581,f64])).
% 0.21/0.53  fof(f64,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f36])).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f16])).
% 0.21/0.53  fof(f16,axiom,(
% 0.21/0.53    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.21/0.53  fof(f581,plain,(
% 0.21/0.53    r2_hidden(k4_tarski(sK3(k2_enumset1(sK0,sK0,sK0,sK0)),sK5(k1_xboole_0,sK3(k2_enumset1(sK0,sK0,sK0,sK0)))),k1_xboole_0) | ~spl8_53),
% 0.21/0.53    inference(avatar_component_clause,[],[f579])).
% 0.21/0.53  fof(f584,plain,(
% 0.21/0.53    ~spl8_52),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f583])).
% 0.21/0.53  fof(f583,plain,(
% 0.21/0.53    $false | ~spl8_52),
% 0.21/0.53    inference(resolution,[],[f577,f84])).
% 0.21/0.53  fof(f84,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~v1_xboole_0(k2_enumset1(X0,X0,X0,X1))) )),
% 0.21/0.53    inference(definition_unfolding,[],[f56,f79])).
% 0.21/0.53  fof(f79,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f57,f65])).
% 0.21/0.53  fof(f65,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.53  fof(f57,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.53  fof(f56,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~v1_xboole_0(k2_tarski(X0,X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0,X1] : ~v1_xboole_0(k2_tarski(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_xboole_0)).
% 0.21/0.53  fof(f577,plain,(
% 0.21/0.53    v1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl8_52),
% 0.21/0.53    inference(avatar_component_clause,[],[f575])).
% 0.21/0.53  fof(f575,plain,(
% 0.21/0.53    spl8_52 <=> v1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_52])])).
% 0.21/0.53  fof(f582,plain,(
% 0.21/0.53    spl8_52 | spl8_53 | ~spl8_37),
% 0.21/0.53    inference(avatar_split_clause,[],[f571,f416,f579,f575])).
% 0.21/0.53  fof(f416,plain,(
% 0.21/0.53    spl8_37 <=> sP6(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_37])])).
% 0.21/0.53  fof(f571,plain,(
% 0.21/0.53    r2_hidden(k4_tarski(sK3(k2_enumset1(sK0,sK0,sK0,sK0)),sK5(k1_xboole_0,sK3(k2_enumset1(sK0,sK0,sK0,sK0)))),k1_xboole_0) | v1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl8_37),
% 0.21/0.53    inference(resolution,[],[f212,f418])).
% 0.21/0.53  fof(f418,plain,(
% 0.21/0.53    sP6(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl8_37),
% 0.21/0.53    inference(avatar_component_clause,[],[f416])).
% 0.21/0.53  fof(f212,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~sP6(X1,X0) | r2_hidden(k4_tarski(sK3(X0),sK5(X1,sK3(X0))),X1) | v1_xboole_0(X0)) )),
% 0.21/0.53    inference(resolution,[],[f91,f120])).
% 0.21/0.53  fof(f120,plain,(
% 0.21/0.53    ( ! [X1] : (r2_hidden(sK3(X1),X1) | v1_xboole_0(X1)) )),
% 0.21/0.53    inference(resolution,[],[f61,f55])).
% 0.21/0.53  fof(f55,plain,(
% 0.21/0.53    ( ! [X0] : (m1_subset_1(sK3(X0),X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0] : ? [X1] : m1_subset_1(X1,X0)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).
% 0.21/0.53  fof(f61,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f31])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.21/0.53    inference(flattening,[],[f30])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,axiom,(
% 0.21/0.53    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.21/0.53  fof(f91,plain,(
% 0.21/0.53    ( ! [X2,X3,X1] : (~r2_hidden(X3,X1) | r2_hidden(k4_tarski(X3,sK5(X2,X3)),X2) | ~sP6(X2,X1)) )),
% 0.21/0.53    inference(general_splitting,[],[f77,f90_D])).
% 0.21/0.53  fof(f90,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k1_relset_1(X1,X0,X2) != X1 | sP6(X2,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f90_D])).
% 0.21/0.53  fof(f90_D,plain,(
% 0.21/0.53    ( ! [X1,X2] : (( ! [X0] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k1_relset_1(X1,X0,X2) != X1) ) <=> ~sP6(X2,X1)) )),
% 0.21/0.53    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP6])])).
% 0.21/0.53  fof(f77,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k1_relset_1(X1,X0,X2) != X1 | ~r2_hidden(X3,X1) | r2_hidden(k4_tarski(X3,sK5(X2,X3)),X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f41])).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.21/0.53    inference(ennf_transformation,[],[f19])).
% 0.21/0.53  fof(f19,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (! [X3] : ~(! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relset_1)).
% 0.21/0.53  fof(f419,plain,(
% 0.21/0.53    spl8_37 | ~spl8_13 | ~spl8_18),
% 0.21/0.53    inference(avatar_split_clause,[],[f384,f224,f175,f416])).
% 0.21/0.53  fof(f175,plain,(
% 0.21/0.53    spl8_13 <=> k1_xboole_0 = sK2),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).
% 0.21/0.53  fof(f224,plain,(
% 0.21/0.53    spl8_18 <=> sP6(sK2,k2_enumset1(sK0,sK0,sK0,sK0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).
% 0.21/0.53  fof(f384,plain,(
% 0.21/0.53    sP6(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0)) | (~spl8_13 | ~spl8_18)),
% 0.21/0.53    inference(backward_demodulation,[],[f226,f177])).
% 0.21/0.53  fof(f177,plain,(
% 0.21/0.53    k1_xboole_0 = sK2 | ~spl8_13),
% 0.21/0.53    inference(avatar_component_clause,[],[f175])).
% 0.21/0.53  fof(f226,plain,(
% 0.21/0.53    sP6(sK2,k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl8_18),
% 0.21/0.53    inference(avatar_component_clause,[],[f224])).
% 0.21/0.53  fof(f369,plain,(
% 0.21/0.53    spl8_14 | ~spl8_10 | ~spl8_17 | ~spl8_33),
% 0.21/0.53    inference(avatar_split_clause,[],[f368,f347,f216,f159,f179])).
% 0.21/0.53  fof(f179,plain,(
% 0.21/0.53    spl8_14 <=> k1_xboole_0 = k2_relat_1(sK2)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).
% 0.21/0.53  fof(f159,plain,(
% 0.21/0.53    spl8_10 <=> v1_relat_1(sK2)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 0.21/0.53  fof(f216,plain,(
% 0.21/0.53    spl8_17 <=> k2_relat_1(sK2) = k9_relat_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).
% 0.21/0.53  fof(f347,plain,(
% 0.21/0.53    spl8_33 <=> k1_xboole_0 = k11_relat_1(sK2,sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_33])])).
% 0.21/0.53  fof(f368,plain,(
% 0.21/0.53    k1_xboole_0 = k2_relat_1(sK2) | (~spl8_10 | ~spl8_17 | ~spl8_33)),
% 0.21/0.53    inference(forward_demodulation,[],[f365,f349])).
% 0.21/0.53  fof(f349,plain,(
% 0.21/0.53    k1_xboole_0 = k11_relat_1(sK2,sK0) | ~spl8_33),
% 0.21/0.53    inference(avatar_component_clause,[],[f347])).
% 0.21/0.53  fof(f365,plain,(
% 0.21/0.53    k2_relat_1(sK2) = k11_relat_1(sK2,sK0) | (~spl8_10 | ~spl8_17)),
% 0.21/0.53    inference(superposition,[],[f218,f210])).
% 0.21/0.53  fof(f210,plain,(
% 0.21/0.53    ( ! [X4] : (k11_relat_1(sK2,X4) = k9_relat_1(sK2,k2_enumset1(X4,X4,X4,X4))) ) | ~spl8_10),
% 0.21/0.53    inference(resolution,[],[f83,f161])).
% 0.21/0.53  fof(f161,plain,(
% 0.21/0.53    v1_relat_1(sK2) | ~spl8_10),
% 0.21/0.53    inference(avatar_component_clause,[],[f159])).
% 0.21/0.53  fof(f83,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~v1_relat_1(X0) | k11_relat_1(X0,X1) = k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1))) )),
% 0.21/0.53    inference(definition_unfolding,[],[f54,f80])).
% 0.21/0.53  fof(f80,plain,(
% 0.21/0.53    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f51,f79])).
% 0.21/0.53  fof(f51,plain,(
% 0.21/0.53    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.53  fof(f54,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~v1_relat_1(X0) | k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f27])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f10])).
% 0.21/0.53  fof(f10,axiom,(
% 0.21/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).
% 0.21/0.53  fof(f218,plain,(
% 0.21/0.53    k2_relat_1(sK2) = k9_relat_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl8_17),
% 0.21/0.53    inference(avatar_component_clause,[],[f216])).
% 0.21/0.53  fof(f350,plain,(
% 0.21/0.53    spl8_33 | spl8_1 | ~spl8_10 | ~spl8_23),
% 0.21/0.53    inference(avatar_split_clause,[],[f342,f258,f159,f95,f347])).
% 0.21/0.53  fof(f95,plain,(
% 0.21/0.53    spl8_1 <=> r2_hidden(k1_funct_1(sK2,sK0),sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.21/0.53  fof(f258,plain,(
% 0.21/0.53    spl8_23 <=> ! [X2] : (~r2_hidden(X2,k1_relat_1(sK2)) | r2_hidden(k1_funct_1(sK2,X2),sK1))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).
% 0.21/0.53  fof(f342,plain,(
% 0.21/0.53    k1_xboole_0 = k11_relat_1(sK2,sK0) | (spl8_1 | ~spl8_10 | ~spl8_23)),
% 0.21/0.53    inference(resolution,[],[f265,f97])).
% 0.21/0.53  fof(f97,plain,(
% 0.21/0.53    ~r2_hidden(k1_funct_1(sK2,sK0),sK1) | spl8_1),
% 0.21/0.53    inference(avatar_component_clause,[],[f95])).
% 0.21/0.53  fof(f265,plain,(
% 0.21/0.53    ( ! [X0] : (r2_hidden(k1_funct_1(sK2,X0),sK1) | k1_xboole_0 = k11_relat_1(sK2,X0)) ) | (~spl8_10 | ~spl8_23)),
% 0.21/0.53    inference(resolution,[],[f259,f205])).
% 0.21/0.53  fof(f205,plain,(
% 0.21/0.53    ( ! [X4] : (r2_hidden(X4,k1_relat_1(sK2)) | k1_xboole_0 = k11_relat_1(sK2,X4)) ) | ~spl8_10),
% 0.21/0.53    inference(resolution,[],[f59,f161])).
% 0.21/0.53  fof(f59,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_xboole_0 = k11_relat_1(X1,X0) | r2_hidden(X0,k1_relat_1(X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f29])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ! [X0,X1] : ((r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f12])).
% 0.21/0.53  fof(f12,axiom,(
% 0.21/0.53    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).
% 0.21/0.53  fof(f259,plain,(
% 0.21/0.53    ( ! [X2] : (~r2_hidden(X2,k1_relat_1(sK2)) | r2_hidden(k1_funct_1(sK2,X2),sK1)) ) | ~spl8_23),
% 0.21/0.53    inference(avatar_component_clause,[],[f258])).
% 0.21/0.53  fof(f299,plain,(
% 0.21/0.53    ~spl8_4 | spl8_19 | spl8_2 | ~spl8_3),
% 0.21/0.53    inference(avatar_split_clause,[],[f298,f105,f100,f228,f110])).
% 0.21/0.53  fof(f110,plain,(
% 0.21/0.53    spl8_4 <=> v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.21/0.53  fof(f228,plain,(
% 0.21/0.53    spl8_19 <=> k2_enumset1(sK0,sK0,sK0,sK0) = k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).
% 0.21/0.53  fof(f100,plain,(
% 0.21/0.53    spl8_2 <=> k1_xboole_0 = sK1),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.21/0.53  fof(f105,plain,(
% 0.21/0.53    spl8_3 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.21/0.53  fof(f298,plain,(
% 0.21/0.53    k1_xboole_0 = sK1 | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) | ~v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1) | ~spl8_3),
% 0.21/0.53    inference(resolution,[],[f74,f107])).
% 0.21/0.53  fof(f107,plain,(
% 0.21/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) | ~spl8_3),
% 0.21/0.53    inference(avatar_component_clause,[],[f105])).
% 0.21/0.53  fof(f74,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f40])).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.53    inference(flattening,[],[f39])).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.53    inference(ennf_transformation,[],[f20])).
% 0.21/0.53  fof(f20,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.53  fof(f260,plain,(
% 0.21/0.53    spl8_23 | ~spl8_5 | ~spl8_10 | ~spl8_8),
% 0.21/0.53    inference(avatar_split_clause,[],[f246,f149,f159,f115,f258])).
% 0.21/0.53  fof(f115,plain,(
% 0.21/0.53    spl8_5 <=> v1_funct_1(sK2)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.21/0.53  fof(f149,plain,(
% 0.21/0.53    spl8_8 <=> v5_relat_1(sK2,sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 0.21/0.53  fof(f246,plain,(
% 0.21/0.53    ( ! [X2] : (~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~r2_hidden(X2,k1_relat_1(sK2)) | r2_hidden(k1_funct_1(sK2,X2),sK1)) ) | ~spl8_8),
% 0.21/0.53    inference(resolution,[],[f62,f151])).
% 0.21/0.53  fof(f151,plain,(
% 0.21/0.53    v5_relat_1(sK2,sK1) | ~spl8_8),
% 0.21/0.53    inference(avatar_component_clause,[],[f149])).
% 0.21/0.53  fof(f62,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~v5_relat_1(X1,X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~r2_hidden(X2,k1_relat_1(X1)) | r2_hidden(k1_funct_1(X1,X2),X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f33])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    ! [X0,X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.53    inference(flattening,[],[f32])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    ! [X0,X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.53    inference(ennf_transformation,[],[f15])).
% 0.21/0.53  fof(f15,axiom,(
% 0.21/0.53    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X2),X0)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_funct_1)).
% 0.21/0.53  fof(f231,plain,(
% 0.21/0.53    spl8_18 | ~spl8_19 | ~spl8_3),
% 0.21/0.53    inference(avatar_split_clause,[],[f222,f105,f228,f224])).
% 0.21/0.53  fof(f222,plain,(
% 0.21/0.53    k2_enumset1(sK0,sK0,sK0,sK0) != k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) | sP6(sK2,k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl8_3),
% 0.21/0.53    inference(resolution,[],[f90,f107])).
% 0.21/0.53  fof(f219,plain,(
% 0.21/0.53    spl8_17 | ~spl8_10 | ~spl8_16),
% 0.21/0.53    inference(avatar_split_clause,[],[f214,f197,f159,f216])).
% 0.21/0.53  fof(f197,plain,(
% 0.21/0.53    spl8_16 <=> sK2 = k7_relat_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).
% 0.21/0.53  fof(f214,plain,(
% 0.21/0.53    k2_relat_1(sK2) = k9_relat_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0)) | (~spl8_10 | ~spl8_16)),
% 0.21/0.53    inference(superposition,[],[f190,f199])).
% 0.21/0.53  fof(f199,plain,(
% 0.21/0.53    sK2 = k7_relat_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl8_16),
% 0.21/0.53    inference(avatar_component_clause,[],[f197])).
% 0.21/0.53  fof(f190,plain,(
% 0.21/0.53    ( ! [X4] : (k2_relat_1(k7_relat_1(sK2,X4)) = k9_relat_1(sK2,X4)) ) | ~spl8_10),
% 0.21/0.53    inference(resolution,[],[f58,f161])).
% 0.21/0.53  fof(f58,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f28])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f11])).
% 0.21/0.53  % (19733)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  fof(f11,axiom,(
% 0.21/0.53    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 0.21/0.53  fof(f200,plain,(
% 0.21/0.53    spl8_16 | ~spl8_10 | ~spl8_9),
% 0.21/0.53    inference(avatar_split_clause,[],[f195,f154,f159,f197])).
% 0.21/0.53  fof(f154,plain,(
% 0.21/0.53    spl8_9 <=> v4_relat_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 0.21/0.53  fof(f195,plain,(
% 0.21/0.53    ~v1_relat_1(sK2) | sK2 = k7_relat_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl8_9),
% 0.21/0.53    inference(resolution,[],[f156,f63])).
% 0.21/0.53  fof(f63,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | ~v1_relat_1(X1) | k7_relat_1(X1,X0) = X1) )),
% 0.21/0.53    inference(cnf_transformation,[],[f35])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.53    inference(flattening,[],[f34])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.53    inference(ennf_transformation,[],[f13])).
% 0.21/0.53  fof(f13,axiom,(
% 0.21/0.53    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).
% 0.21/0.53  fof(f156,plain,(
% 0.21/0.53    v4_relat_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl8_9),
% 0.21/0.53    inference(avatar_component_clause,[],[f154])).
% 0.21/0.53  fof(f182,plain,(
% 0.21/0.53    spl8_13 | ~spl8_14 | ~spl8_10),
% 0.21/0.53    inference(avatar_split_clause,[],[f172,f159,f179,f175])).
% 0.21/0.53  fof(f172,plain,(
% 0.21/0.53    k1_xboole_0 != k2_relat_1(sK2) | k1_xboole_0 = sK2 | ~spl8_10),
% 0.21/0.53    inference(resolution,[],[f161,f53])).
% 0.21/0.53  fof(f53,plain,(
% 0.21/0.53    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0) | k1_xboole_0 = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f26])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(flattening,[],[f25])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f14])).
% 0.21/0.53  fof(f14,axiom,(
% 0.21/0.53    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).
% 0.21/0.53  fof(f162,plain,(
% 0.21/0.53    spl8_10 | ~spl8_3),
% 0.21/0.53    inference(avatar_split_clause,[],[f146,f105,f159])).
% 0.21/0.53  fof(f146,plain,(
% 0.21/0.53    v1_relat_1(sK2) | ~spl8_3),
% 0.21/0.53    inference(resolution,[],[f107,f66])).
% 0.21/0.53  fof(f66,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f37])).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.53    inference(ennf_transformation,[],[f17])).
% 0.21/0.53  fof(f17,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.53  fof(f157,plain,(
% 0.21/0.53    spl8_9 | ~spl8_3),
% 0.21/0.53    inference(avatar_split_clause,[],[f145,f105,f154])).
% 0.21/0.53  fof(f145,plain,(
% 0.21/0.53    v4_relat_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl8_3),
% 0.21/0.53    inference(resolution,[],[f107,f67])).
% 0.21/0.53  fof(f67,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f38])).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.53    inference(ennf_transformation,[],[f18])).
% 0.21/0.53  fof(f18,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.53  fof(f152,plain,(
% 0.21/0.53    spl8_8 | ~spl8_3),
% 0.21/0.53    inference(avatar_split_clause,[],[f144,f105,f149])).
% 0.21/0.53  fof(f144,plain,(
% 0.21/0.53    v5_relat_1(sK2,sK1) | ~spl8_3),
% 0.21/0.53    inference(resolution,[],[f107,f68])).
% 0.21/0.53  fof(f68,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f38])).
% 0.21/0.53  fof(f118,plain,(
% 0.21/0.53    spl8_5),
% 0.21/0.53    inference(avatar_split_clause,[],[f44,f115])).
% 0.21/0.53  fof(f44,plain,(
% 0.21/0.53    v1_funct_1(sK2)),
% 0.21/0.53    inference(cnf_transformation,[],[f24])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 0.21/0.53    inference(flattening,[],[f23])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ? [X0,X1,X2] : ((~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 0.21/0.53    inference(ennf_transformation,[],[f22])).
% 0.21/0.53  fof(f22,negated_conjecture,(
% 0.21/0.53    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 0.21/0.53    inference(negated_conjecture,[],[f21])).
% 0.21/0.53  fof(f21,conjecture,(
% 0.21/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_2)).
% 0.21/0.53  fof(f113,plain,(
% 0.21/0.53    spl8_4),
% 0.21/0.53    inference(avatar_split_clause,[],[f82,f110])).
% 0.21/0.53  fof(f82,plain,(
% 0.21/0.53    v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 0.21/0.53    inference(definition_unfolding,[],[f45,f80])).
% 0.21/0.53  fof(f45,plain,(
% 0.21/0.53    v1_funct_2(sK2,k1_tarski(sK0),sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f24])).
% 0.21/0.53  fof(f108,plain,(
% 0.21/0.53    spl8_3),
% 0.21/0.53    inference(avatar_split_clause,[],[f81,f105])).
% 0.21/0.53  fof(f81,plain,(
% 0.21/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 0.21/0.53    inference(definition_unfolding,[],[f46,f80])).
% 0.21/0.53  fof(f46,plain,(
% 0.21/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 0.21/0.53    inference(cnf_transformation,[],[f24])).
% 0.21/0.53  fof(f103,plain,(
% 0.21/0.53    ~spl8_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f47,f100])).
% 0.21/0.53  fof(f47,plain,(
% 0.21/0.53    k1_xboole_0 != sK1),
% 0.21/0.53    inference(cnf_transformation,[],[f24])).
% 0.21/0.53  fof(f98,plain,(
% 0.21/0.53    ~spl8_1),
% 0.21/0.53    inference(avatar_split_clause,[],[f48,f95])).
% 0.21/0.53  fof(f48,plain,(
% 0.21/0.53    ~r2_hidden(k1_funct_1(sK2,sK0),sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f24])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (19747)------------------------------
% 0.21/0.53  % (19747)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (19747)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (19747)Memory used [KB]: 11385
% 0.21/0.53  % (19747)Time elapsed: 0.115 s
% 0.21/0.53  % (19747)------------------------------
% 0.21/0.53  % (19747)------------------------------
% 0.21/0.53  % (19730)Success in time 0.173 s
%------------------------------------------------------------------------------
