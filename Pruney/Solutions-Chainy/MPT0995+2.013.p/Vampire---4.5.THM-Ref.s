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
% DateTime   : Thu Dec  3 13:03:30 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 203 expanded)
%              Number of leaves         :   30 (  83 expanded)
%              Depth                    :    7
%              Number of atoms          :  391 ( 761 expanded)
%              Number of equality atoms :   61 ( 137 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f231,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f54,f58,f62,f66,f70,f74,f78,f82,f86,f90,f98,f122,f126,f145,f156,f165,f169,f179,f186,f196,f204,f219,f229])).

fof(f229,plain,
    ( ~ spl7_2
    | ~ spl7_3
    | ~ spl7_32
    | ~ spl7_36 ),
    inference(avatar_contradiction_clause,[],[f228])).

fof(f228,plain,
    ( $false
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_32
    | ~ spl7_36 ),
    inference(subsumption_resolution,[],[f227,f57])).

fof(f57,plain,
    ( r2_hidden(sK5,sK0)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl7_2
  <=> r2_hidden(sK5,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f227,plain,
    ( ~ r2_hidden(sK5,sK0)
    | ~ spl7_3
    | ~ spl7_32
    | ~ spl7_36 ),
    inference(subsumption_resolution,[],[f224,f61])).

fof(f61,plain,
    ( r2_hidden(sK5,sK2)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl7_3
  <=> r2_hidden(sK5,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f224,plain,
    ( ~ r2_hidden(sK5,sK2)
    | ~ r2_hidden(sK5,sK0)
    | ~ spl7_32
    | ~ spl7_36 ),
    inference(resolution,[],[f218,f185])).

fof(f185,plain,
    ( r2_hidden(k4_tarski(sK5,sK4),sK3)
    | ~ spl7_32 ),
    inference(avatar_component_clause,[],[f184])).

fof(f184,plain,
    ( spl7_32
  <=> r2_hidden(k4_tarski(sK5,sK4),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_32])])).

fof(f218,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(X0,sK4),sK3)
        | ~ r2_hidden(X0,sK2)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl7_36 ),
    inference(avatar_component_clause,[],[f217])).

fof(f217,plain,
    ( spl7_36
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | ~ r2_hidden(X0,sK2)
        | ~ r2_hidden(k4_tarski(X0,sK4),sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_36])])).

fof(f219,plain,
    ( ~ spl7_22
    | spl7_36
    | ~ spl7_7
    | ~ spl7_12
    | spl7_25
    | ~ spl7_28
    | ~ spl7_33 ),
    inference(avatar_split_clause,[],[f200,f194,f167,f154,f96,f76,f217,f136])).

fof(f136,plain,
    ( spl7_22
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f76,plain,
    ( spl7_7
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f96,plain,
    ( spl7_12
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f154,plain,
    ( spl7_25
  <=> r2_hidden(sK4,k9_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).

fof(f167,plain,
    ( spl7_28
  <=> ! [X1,X3,X0,X2] :
        ( ~ v1_relat_1(X2)
        | ~ r2_hidden(X3,k1_relat_1(X2))
        | ~ r2_hidden(k4_tarski(X3,X0),X2)
        | ~ r2_hidden(X3,X1)
        | r2_hidden(X0,k9_relat_1(X2,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).

fof(f194,plain,
    ( spl7_33
  <=> sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_33])])).

fof(f200,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | ~ r2_hidden(k4_tarski(X0,sK4),sK3)
        | ~ r2_hidden(X0,sK2)
        | ~ v1_relat_1(sK3) )
    | ~ spl7_7
    | ~ spl7_12
    | spl7_25
    | ~ spl7_28
    | ~ spl7_33 ),
    inference(backward_demodulation,[],[f187,f199])).

fof(f199,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl7_7
    | ~ spl7_12
    | ~ spl7_33 ),
    inference(subsumption_resolution,[],[f197,f77])).

fof(f77,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f76])).

fof(f197,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_12
    | ~ spl7_33 ),
    inference(superposition,[],[f195,f97])).

fof(f97,plain,
    ( ! [X2,X0,X1] :
        ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f96])).

fof(f195,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl7_33 ),
    inference(avatar_component_clause,[],[f194])).

fof(f187,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK3))
        | ~ r2_hidden(k4_tarski(X0,sK4),sK3)
        | ~ r2_hidden(X0,sK2)
        | ~ v1_relat_1(sK3) )
    | spl7_25
    | ~ spl7_28 ),
    inference(resolution,[],[f168,f155])).

fof(f155,plain,
    ( ~ r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | spl7_25 ),
    inference(avatar_component_clause,[],[f154])).

fof(f168,plain,
    ( ! [X2,X0,X3,X1] :
        ( r2_hidden(X0,k9_relat_1(X2,X1))
        | ~ r2_hidden(X3,k1_relat_1(X2))
        | ~ r2_hidden(k4_tarski(X3,X0),X2)
        | ~ r2_hidden(X3,X1)
        | ~ v1_relat_1(X2) )
    | ~ spl7_28 ),
    inference(avatar_component_clause,[],[f167])).

fof(f204,plain,
    ( ~ spl7_2
    | ~ spl7_7
    | ~ spl7_12
    | spl7_31
    | ~ spl7_33 ),
    inference(avatar_contradiction_clause,[],[f203])).

fof(f203,plain,
    ( $false
    | ~ spl7_2
    | ~ spl7_7
    | ~ spl7_12
    | spl7_31
    | ~ spl7_33 ),
    inference(subsumption_resolution,[],[f201,f57])).

fof(f201,plain,
    ( ~ r2_hidden(sK5,sK0)
    | ~ spl7_7
    | ~ spl7_12
    | spl7_31
    | ~ spl7_33 ),
    inference(backward_demodulation,[],[f182,f199])).

fof(f182,plain,
    ( ~ r2_hidden(sK5,k1_relat_1(sK3))
    | spl7_31 ),
    inference(avatar_component_clause,[],[f181])).

fof(f181,plain,
    ( spl7_31
  <=> r2_hidden(sK5,k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).

fof(f196,plain,
    ( spl7_33
    | spl7_4
    | ~ spl7_5
    | ~ spl7_7
    | ~ spl7_30 ),
    inference(avatar_split_clause,[],[f192,f177,f76,f68,f64,f194])).

fof(f64,plain,
    ( spl7_4
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f68,plain,
    ( spl7_5
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f177,plain,
    ( spl7_30
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_xboole_0 = X1
        | k1_relset_1(X0,X1,X2) = X0
        | ~ v1_funct_2(X2,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).

fof(f192,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | spl7_4
    | ~ spl7_5
    | ~ spl7_7
    | ~ spl7_30 ),
    inference(subsumption_resolution,[],[f191,f69])).

fof(f69,plain,
    ( v1_funct_2(sK3,sK0,sK1)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f68])).

fof(f191,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ v1_funct_2(sK3,sK0,sK1)
    | spl7_4
    | ~ spl7_7
    | ~ spl7_30 ),
    inference(subsumption_resolution,[],[f190,f65])).

fof(f65,plain,
    ( k1_xboole_0 != sK1
    | spl7_4 ),
    inference(avatar_component_clause,[],[f64])).

fof(f190,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ v1_funct_2(sK3,sK0,sK1)
    | ~ spl7_7
    | ~ spl7_30 ),
    inference(resolution,[],[f178,f77])).

fof(f178,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_xboole_0 = X1
        | k1_relset_1(X0,X1,X2) = X0
        | ~ v1_funct_2(X2,X0,X1) )
    | ~ spl7_30 ),
    inference(avatar_component_clause,[],[f177])).

fof(f186,plain,
    ( ~ spl7_31
    | spl7_32
    | ~ spl7_6
    | ~ spl7_27 ),
    inference(avatar_split_clause,[],[f171,f163,f72,f184,f181])).

fof(f72,plain,
    ( spl7_6
  <=> sK4 = k1_funct_1(sK3,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f163,plain,
    ( spl7_27
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK3))
        | r2_hidden(k4_tarski(X0,k1_funct_1(sK3,X0)),sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).

fof(f171,plain,
    ( r2_hidden(k4_tarski(sK5,sK4),sK3)
    | ~ r2_hidden(sK5,k1_relat_1(sK3))
    | ~ spl7_6
    | ~ spl7_27 ),
    inference(superposition,[],[f164,f73])).

fof(f73,plain,
    ( sK4 = k1_funct_1(sK3,sK5)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f72])).

fof(f164,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(X0,k1_funct_1(sK3,X0)),sK3)
        | ~ r2_hidden(X0,k1_relat_1(sK3)) )
    | ~ spl7_27 ),
    inference(avatar_component_clause,[],[f163])).

fof(f179,plain,(
    spl7_30 ),
    inference(avatar_split_clause,[],[f40,f177])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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

fof(f169,plain,(
    spl7_28 ),
    inference(avatar_split_clause,[],[f33,f167])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X3,k1_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X3,X0),X2)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X0,k9_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

fof(f165,plain,
    ( spl7_27
    | ~ spl7_22
    | ~ spl7_1
    | ~ spl7_19 ),
    inference(avatar_split_clause,[],[f157,f124,f52,f136,f163])).

fof(f52,plain,
    ( spl7_1
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f124,plain,
    ( spl7_19
  <=> ! [X0,X2] :
        ( ~ v1_relat_1(X2)
        | ~ v1_funct_1(X2)
        | ~ r2_hidden(X0,k1_relat_1(X2))
        | r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f157,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(sK3)
        | ~ r2_hidden(X0,k1_relat_1(sK3))
        | r2_hidden(k4_tarski(X0,k1_funct_1(sK3,X0)),sK3) )
    | ~ spl7_1
    | ~ spl7_19 ),
    inference(resolution,[],[f125,f53])).

fof(f53,plain,
    ( v1_funct_1(sK3)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f52])).

fof(f125,plain,
    ( ! [X2,X0] :
        ( ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2)
        | ~ r2_hidden(X0,k1_relat_1(X2))
        | r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2) )
    | ~ spl7_19 ),
    inference(avatar_component_clause,[],[f124])).

fof(f156,plain,
    ( ~ spl7_25
    | ~ spl7_7
    | spl7_8
    | ~ spl7_18 ),
    inference(avatar_split_clause,[],[f152,f120,f80,f76,f154])).

fof(f80,plain,
    ( spl7_8
  <=> r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f120,plain,
    ( spl7_18
  <=> ! [X1,X3,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f152,plain,
    ( ~ r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | ~ spl7_7
    | spl7_8
    | ~ spl7_18 ),
    inference(backward_demodulation,[],[f81,f151])).

fof(f151,plain,
    ( ! [X0] : k9_relat_1(sK3,X0) = k7_relset_1(sK0,sK1,sK3,X0)
    | ~ spl7_7
    | ~ spl7_18 ),
    inference(resolution,[],[f121,f77])).

fof(f121,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) )
    | ~ spl7_18 ),
    inference(avatar_component_clause,[],[f120])).

fof(f81,plain,
    ( ~ r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))
    | spl7_8 ),
    inference(avatar_component_clause,[],[f80])).

fof(f145,plain,
    ( ~ spl7_7
    | ~ spl7_9
    | ~ spl7_10
    | spl7_22 ),
    inference(avatar_contradiction_clause,[],[f143])).

fof(f143,plain,
    ( $false
    | ~ spl7_7
    | ~ spl7_9
    | ~ spl7_10
    | spl7_22 ),
    inference(unit_resulting_resolution,[],[f85,f77,f137,f89])).

fof(f89,plain,
    ( ! [X0,X1] :
        ( v1_relat_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl7_10
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f137,plain,
    ( ~ v1_relat_1(sK3)
    | spl7_22 ),
    inference(avatar_component_clause,[],[f136])).

fof(f85,plain,
    ( ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl7_9
  <=> ! [X1,X0] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f126,plain,(
    spl7_19 ),
    inference(avatar_split_clause,[],[f50,f124])).

fof(f50,plain,(
    ! [X2,X0] :
      ( ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2) ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | k1_funct_1(X2,X0) != X1
      | r2_hidden(k4_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

fof(f122,plain,(
    spl7_18 ),
    inference(avatar_split_clause,[],[f44,f120])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f98,plain,(
    spl7_12 ),
    inference(avatar_split_clause,[],[f34,f96])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f90,plain,(
    spl7_10 ),
    inference(avatar_split_clause,[],[f28,f88])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f86,plain,(
    spl7_9 ),
    inference(avatar_split_clause,[],[f29,f84])).

fof(f29,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f82,plain,(
    ~ spl7_8 ),
    inference(avatar_split_clause,[],[f23,f80])).

fof(f23,plain,(
    ~ r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ~ r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))
          & ? [X5] :
              ( k1_funct_1(X3,X5) = X4
              & r2_hidden(X5,X2)
              & r2_hidden(X5,X0) ) )
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ~ r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))
          & ? [X5] :
              ( k1_funct_1(X3,X5) = X4
              & r2_hidden(X5,X2)
              & r2_hidden(X5,X0) ) )
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => ! [X4] :
              ( ? [X5] :
                  ( k1_funct_1(X3,X5) = X4
                  & r2_hidden(X5,X2)
                  & r2_hidden(X5,X0) )
             => r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( k1_xboole_0 != X1
       => ! [X4] :
            ( ? [X5] :
                ( k1_funct_1(X3,X5) = X4
                & r2_hidden(X5,X2)
                & r2_hidden(X5,X0) )
           => r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_2)).

fof(f78,plain,(
    spl7_7 ),
    inference(avatar_split_clause,[],[f26,f76])).

fof(f26,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f11])).

fof(f74,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f22,f72])).

fof(f22,plain,(
    sK4 = k1_funct_1(sK3,sK5) ),
    inference(cnf_transformation,[],[f11])).

fof(f70,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f25,f68])).

fof(f25,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f66,plain,(
    ~ spl7_4 ),
    inference(avatar_split_clause,[],[f27,f64])).

fof(f27,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f11])).

fof(f62,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f21,f60])).

fof(f21,plain,(
    r2_hidden(sK5,sK2) ),
    inference(cnf_transformation,[],[f11])).

fof(f58,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f20,f56])).

fof(f20,plain,(
    r2_hidden(sK5,sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f54,plain,(
    spl7_1 ),
    inference(avatar_split_clause,[],[f24,f52])).

fof(f24,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:03:21 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.41  % (1204)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.41  % (1204)Refutation found. Thanks to Tanya!
% 0.21/0.41  % SZS status Theorem for theBenchmark
% 0.21/0.41  % SZS output start Proof for theBenchmark
% 0.21/0.41  fof(f231,plain,(
% 0.21/0.41    $false),
% 0.21/0.41    inference(avatar_sat_refutation,[],[f54,f58,f62,f66,f70,f74,f78,f82,f86,f90,f98,f122,f126,f145,f156,f165,f169,f179,f186,f196,f204,f219,f229])).
% 0.21/0.41  fof(f229,plain,(
% 0.21/0.41    ~spl7_2 | ~spl7_3 | ~spl7_32 | ~spl7_36),
% 0.21/0.41    inference(avatar_contradiction_clause,[],[f228])).
% 0.21/0.41  fof(f228,plain,(
% 0.21/0.41    $false | (~spl7_2 | ~spl7_3 | ~spl7_32 | ~spl7_36)),
% 0.21/0.41    inference(subsumption_resolution,[],[f227,f57])).
% 0.21/0.41  fof(f57,plain,(
% 0.21/0.41    r2_hidden(sK5,sK0) | ~spl7_2),
% 0.21/0.41    inference(avatar_component_clause,[],[f56])).
% 0.21/0.41  fof(f56,plain,(
% 0.21/0.41    spl7_2 <=> r2_hidden(sK5,sK0)),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.21/0.41  fof(f227,plain,(
% 0.21/0.41    ~r2_hidden(sK5,sK0) | (~spl7_3 | ~spl7_32 | ~spl7_36)),
% 0.21/0.41    inference(subsumption_resolution,[],[f224,f61])).
% 0.21/0.41  fof(f61,plain,(
% 0.21/0.41    r2_hidden(sK5,sK2) | ~spl7_3),
% 0.21/0.41    inference(avatar_component_clause,[],[f60])).
% 0.21/0.41  fof(f60,plain,(
% 0.21/0.41    spl7_3 <=> r2_hidden(sK5,sK2)),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.21/0.41  fof(f224,plain,(
% 0.21/0.41    ~r2_hidden(sK5,sK2) | ~r2_hidden(sK5,sK0) | (~spl7_32 | ~spl7_36)),
% 0.21/0.41    inference(resolution,[],[f218,f185])).
% 0.21/0.41  fof(f185,plain,(
% 0.21/0.41    r2_hidden(k4_tarski(sK5,sK4),sK3) | ~spl7_32),
% 0.21/0.41    inference(avatar_component_clause,[],[f184])).
% 0.21/0.41  fof(f184,plain,(
% 0.21/0.41    spl7_32 <=> r2_hidden(k4_tarski(sK5,sK4),sK3)),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl7_32])])).
% 0.21/0.41  fof(f218,plain,(
% 0.21/0.41    ( ! [X0] : (~r2_hidden(k4_tarski(X0,sK4),sK3) | ~r2_hidden(X0,sK2) | ~r2_hidden(X0,sK0)) ) | ~spl7_36),
% 0.21/0.41    inference(avatar_component_clause,[],[f217])).
% 0.21/0.41  fof(f217,plain,(
% 0.21/0.41    spl7_36 <=> ! [X0] : (~r2_hidden(X0,sK0) | ~r2_hidden(X0,sK2) | ~r2_hidden(k4_tarski(X0,sK4),sK3))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl7_36])])).
% 0.21/0.41  fof(f219,plain,(
% 0.21/0.41    ~spl7_22 | spl7_36 | ~spl7_7 | ~spl7_12 | spl7_25 | ~spl7_28 | ~spl7_33),
% 0.21/0.41    inference(avatar_split_clause,[],[f200,f194,f167,f154,f96,f76,f217,f136])).
% 0.21/0.41  fof(f136,plain,(
% 0.21/0.41    spl7_22 <=> v1_relat_1(sK3)),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).
% 0.21/0.41  fof(f76,plain,(
% 0.21/0.41    spl7_7 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.21/0.41  fof(f96,plain,(
% 0.21/0.41    spl7_12 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 0.21/0.41  fof(f154,plain,(
% 0.21/0.41    spl7_25 <=> r2_hidden(sK4,k9_relat_1(sK3,sK2))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).
% 0.21/0.41  fof(f167,plain,(
% 0.21/0.41    spl7_28 <=> ! [X1,X3,X0,X2] : (~v1_relat_1(X2) | ~r2_hidden(X3,k1_relat_1(X2)) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,X1) | r2_hidden(X0,k9_relat_1(X2,X1)))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).
% 0.21/0.41  fof(f194,plain,(
% 0.21/0.41    spl7_33 <=> sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl7_33])])).
% 0.21/0.41  fof(f200,plain,(
% 0.21/0.41    ( ! [X0] : (~r2_hidden(X0,sK0) | ~r2_hidden(k4_tarski(X0,sK4),sK3) | ~r2_hidden(X0,sK2) | ~v1_relat_1(sK3)) ) | (~spl7_7 | ~spl7_12 | spl7_25 | ~spl7_28 | ~spl7_33)),
% 0.21/0.41    inference(backward_demodulation,[],[f187,f199])).
% 0.21/0.41  fof(f199,plain,(
% 0.21/0.41    sK0 = k1_relat_1(sK3) | (~spl7_7 | ~spl7_12 | ~spl7_33)),
% 0.21/0.41    inference(subsumption_resolution,[],[f197,f77])).
% 0.21/0.41  fof(f77,plain,(
% 0.21/0.41    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl7_7),
% 0.21/0.41    inference(avatar_component_clause,[],[f76])).
% 0.21/0.41  fof(f197,plain,(
% 0.21/0.41    sK0 = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | (~spl7_12 | ~spl7_33)),
% 0.21/0.41    inference(superposition,[],[f195,f97])).
% 0.21/0.41  fof(f97,plain,(
% 0.21/0.41    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl7_12),
% 0.21/0.41    inference(avatar_component_clause,[],[f96])).
% 0.21/0.41  fof(f195,plain,(
% 0.21/0.41    sK0 = k1_relset_1(sK0,sK1,sK3) | ~spl7_33),
% 0.21/0.41    inference(avatar_component_clause,[],[f194])).
% 0.21/0.41  fof(f187,plain,(
% 0.21/0.41    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK3)) | ~r2_hidden(k4_tarski(X0,sK4),sK3) | ~r2_hidden(X0,sK2) | ~v1_relat_1(sK3)) ) | (spl7_25 | ~spl7_28)),
% 0.21/0.41    inference(resolution,[],[f168,f155])).
% 0.21/0.41  fof(f155,plain,(
% 0.21/0.41    ~r2_hidden(sK4,k9_relat_1(sK3,sK2)) | spl7_25),
% 0.21/0.41    inference(avatar_component_clause,[],[f154])).
% 0.21/0.41  fof(f168,plain,(
% 0.21/0.41    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,k9_relat_1(X2,X1)) | ~r2_hidden(X3,k1_relat_1(X2)) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,X1) | ~v1_relat_1(X2)) ) | ~spl7_28),
% 0.21/0.41    inference(avatar_component_clause,[],[f167])).
% 0.21/0.41  fof(f204,plain,(
% 0.21/0.41    ~spl7_2 | ~spl7_7 | ~spl7_12 | spl7_31 | ~spl7_33),
% 0.21/0.41    inference(avatar_contradiction_clause,[],[f203])).
% 0.21/0.41  fof(f203,plain,(
% 0.21/0.41    $false | (~spl7_2 | ~spl7_7 | ~spl7_12 | spl7_31 | ~spl7_33)),
% 0.21/0.41    inference(subsumption_resolution,[],[f201,f57])).
% 0.21/0.41  fof(f201,plain,(
% 0.21/0.41    ~r2_hidden(sK5,sK0) | (~spl7_7 | ~spl7_12 | spl7_31 | ~spl7_33)),
% 0.21/0.41    inference(backward_demodulation,[],[f182,f199])).
% 0.21/0.41  fof(f182,plain,(
% 0.21/0.41    ~r2_hidden(sK5,k1_relat_1(sK3)) | spl7_31),
% 0.21/0.41    inference(avatar_component_clause,[],[f181])).
% 0.21/0.41  fof(f181,plain,(
% 0.21/0.41    spl7_31 <=> r2_hidden(sK5,k1_relat_1(sK3))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).
% 0.21/0.41  fof(f196,plain,(
% 0.21/0.41    spl7_33 | spl7_4 | ~spl7_5 | ~spl7_7 | ~spl7_30),
% 0.21/0.41    inference(avatar_split_clause,[],[f192,f177,f76,f68,f64,f194])).
% 0.21/0.41  fof(f64,plain,(
% 0.21/0.41    spl7_4 <=> k1_xboole_0 = sK1),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.21/0.41  fof(f68,plain,(
% 0.21/0.41    spl7_5 <=> v1_funct_2(sK3,sK0,sK1)),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.21/0.41  fof(f177,plain,(
% 0.21/0.41    spl7_30 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).
% 0.21/0.41  fof(f192,plain,(
% 0.21/0.41    sK0 = k1_relset_1(sK0,sK1,sK3) | (spl7_4 | ~spl7_5 | ~spl7_7 | ~spl7_30)),
% 0.21/0.41    inference(subsumption_resolution,[],[f191,f69])).
% 0.21/0.41  fof(f69,plain,(
% 0.21/0.41    v1_funct_2(sK3,sK0,sK1) | ~spl7_5),
% 0.21/0.41    inference(avatar_component_clause,[],[f68])).
% 0.21/0.41  fof(f191,plain,(
% 0.21/0.41    sK0 = k1_relset_1(sK0,sK1,sK3) | ~v1_funct_2(sK3,sK0,sK1) | (spl7_4 | ~spl7_7 | ~spl7_30)),
% 0.21/0.41    inference(subsumption_resolution,[],[f190,f65])).
% 0.21/0.41  fof(f65,plain,(
% 0.21/0.41    k1_xboole_0 != sK1 | spl7_4),
% 0.21/0.41    inference(avatar_component_clause,[],[f64])).
% 0.21/0.41  fof(f190,plain,(
% 0.21/0.41    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3) | ~v1_funct_2(sK3,sK0,sK1) | (~spl7_7 | ~spl7_30)),
% 0.21/0.41    inference(resolution,[],[f178,f77])).
% 0.21/0.41  fof(f178,plain,(
% 0.21/0.41    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) ) | ~spl7_30),
% 0.21/0.41    inference(avatar_component_clause,[],[f177])).
% 0.21/0.41  fof(f186,plain,(
% 0.21/0.41    ~spl7_31 | spl7_32 | ~spl7_6 | ~spl7_27),
% 0.21/0.41    inference(avatar_split_clause,[],[f171,f163,f72,f184,f181])).
% 0.21/0.41  fof(f72,plain,(
% 0.21/0.41    spl7_6 <=> sK4 = k1_funct_1(sK3,sK5)),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.21/0.41  fof(f163,plain,(
% 0.21/0.41    spl7_27 <=> ! [X0] : (~r2_hidden(X0,k1_relat_1(sK3)) | r2_hidden(k4_tarski(X0,k1_funct_1(sK3,X0)),sK3))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).
% 0.21/0.41  fof(f171,plain,(
% 0.21/0.41    r2_hidden(k4_tarski(sK5,sK4),sK3) | ~r2_hidden(sK5,k1_relat_1(sK3)) | (~spl7_6 | ~spl7_27)),
% 0.21/0.41    inference(superposition,[],[f164,f73])).
% 0.21/0.41  fof(f73,plain,(
% 0.21/0.41    sK4 = k1_funct_1(sK3,sK5) | ~spl7_6),
% 0.21/0.41    inference(avatar_component_clause,[],[f72])).
% 0.21/0.41  fof(f164,plain,(
% 0.21/0.41    ( ! [X0] : (r2_hidden(k4_tarski(X0,k1_funct_1(sK3,X0)),sK3) | ~r2_hidden(X0,k1_relat_1(sK3))) ) | ~spl7_27),
% 0.21/0.41    inference(avatar_component_clause,[],[f163])).
% 0.21/0.41  fof(f179,plain,(
% 0.21/0.41    spl7_30),
% 0.21/0.41    inference(avatar_split_clause,[],[f40,f177])).
% 0.21/0.41  fof(f40,plain,(
% 0.21/0.41    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f16])).
% 0.21/0.41  fof(f16,plain,(
% 0.21/0.41    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.41    inference(flattening,[],[f15])).
% 0.21/0.41  fof(f15,plain,(
% 0.21/0.41    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.41    inference(ennf_transformation,[],[f7])).
% 0.21/0.41  fof(f7,axiom,(
% 0.21/0.41    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.41  fof(f169,plain,(
% 0.21/0.41    spl7_28),
% 0.21/0.41    inference(avatar_split_clause,[],[f33,f167])).
% 0.21/0.41  fof(f33,plain,(
% 0.21/0.41    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X2) | ~r2_hidden(X3,k1_relat_1(X2)) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,X1) | r2_hidden(X0,k9_relat_1(X2,X1))) )),
% 0.21/0.41    inference(cnf_transformation,[],[f13])).
% 0.21/0.41  fof(f13,plain,(
% 0.21/0.41    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.21/0.41    inference(ennf_transformation,[],[f3])).
% 0.21/0.41  fof(f3,axiom,(
% 0.21/0.41    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).
% 0.21/0.41  fof(f165,plain,(
% 0.21/0.41    spl7_27 | ~spl7_22 | ~spl7_1 | ~spl7_19),
% 0.21/0.41    inference(avatar_split_clause,[],[f157,f124,f52,f136,f163])).
% 0.21/0.41  fof(f52,plain,(
% 0.21/0.41    spl7_1 <=> v1_funct_1(sK3)),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.21/0.41  fof(f124,plain,(
% 0.21/0.41    spl7_19 <=> ! [X0,X2] : (~v1_relat_1(X2) | ~v1_funct_1(X2) | ~r2_hidden(X0,k1_relat_1(X2)) | r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).
% 0.21/0.41  fof(f157,plain,(
% 0.21/0.41    ( ! [X0] : (~v1_relat_1(sK3) | ~r2_hidden(X0,k1_relat_1(sK3)) | r2_hidden(k4_tarski(X0,k1_funct_1(sK3,X0)),sK3)) ) | (~spl7_1 | ~spl7_19)),
% 0.21/0.41    inference(resolution,[],[f125,f53])).
% 0.21/0.41  fof(f53,plain,(
% 0.21/0.41    v1_funct_1(sK3) | ~spl7_1),
% 0.21/0.41    inference(avatar_component_clause,[],[f52])).
% 0.21/0.41  fof(f125,plain,(
% 0.21/0.41    ( ! [X2,X0] : (~v1_funct_1(X2) | ~v1_relat_1(X2) | ~r2_hidden(X0,k1_relat_1(X2)) | r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2)) ) | ~spl7_19),
% 0.21/0.41    inference(avatar_component_clause,[],[f124])).
% 0.21/0.41  fof(f156,plain,(
% 0.21/0.41    ~spl7_25 | ~spl7_7 | spl7_8 | ~spl7_18),
% 0.21/0.41    inference(avatar_split_clause,[],[f152,f120,f80,f76,f154])).
% 0.21/0.41  fof(f80,plain,(
% 0.21/0.41    spl7_8 <=> r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.21/0.41  fof(f120,plain,(
% 0.21/0.41    spl7_18 <=> ! [X1,X3,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).
% 0.21/0.41  fof(f152,plain,(
% 0.21/0.41    ~r2_hidden(sK4,k9_relat_1(sK3,sK2)) | (~spl7_7 | spl7_8 | ~spl7_18)),
% 0.21/0.41    inference(backward_demodulation,[],[f81,f151])).
% 0.21/0.41  fof(f151,plain,(
% 0.21/0.41    ( ! [X0] : (k9_relat_1(sK3,X0) = k7_relset_1(sK0,sK1,sK3,X0)) ) | (~spl7_7 | ~spl7_18)),
% 0.21/0.41    inference(resolution,[],[f121,f77])).
% 0.21/0.41  fof(f121,plain,(
% 0.21/0.41    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) ) | ~spl7_18),
% 0.21/0.41    inference(avatar_component_clause,[],[f120])).
% 0.21/0.41  fof(f81,plain,(
% 0.21/0.41    ~r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) | spl7_8),
% 0.21/0.41    inference(avatar_component_clause,[],[f80])).
% 0.21/0.41  fof(f145,plain,(
% 0.21/0.41    ~spl7_7 | ~spl7_9 | ~spl7_10 | spl7_22),
% 0.21/0.41    inference(avatar_contradiction_clause,[],[f143])).
% 0.21/0.41  fof(f143,plain,(
% 0.21/0.41    $false | (~spl7_7 | ~spl7_9 | ~spl7_10 | spl7_22)),
% 0.21/0.41    inference(unit_resulting_resolution,[],[f85,f77,f137,f89])).
% 0.21/0.41  fof(f89,plain,(
% 0.21/0.41    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | ~spl7_10),
% 0.21/0.41    inference(avatar_component_clause,[],[f88])).
% 0.21/0.41  fof(f88,plain,(
% 0.21/0.41    spl7_10 <=> ! [X1,X0] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 0.21/0.41  fof(f137,plain,(
% 0.21/0.41    ~v1_relat_1(sK3) | spl7_22),
% 0.21/0.41    inference(avatar_component_clause,[],[f136])).
% 0.21/0.41  fof(f85,plain,(
% 0.21/0.41    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) ) | ~spl7_9),
% 0.21/0.41    inference(avatar_component_clause,[],[f84])).
% 0.21/0.41  fof(f84,plain,(
% 0.21/0.41    spl7_9 <=> ! [X1,X0] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.21/0.41  fof(f126,plain,(
% 0.21/0.41    spl7_19),
% 0.21/0.41    inference(avatar_split_clause,[],[f50,f124])).
% 0.21/0.41  fof(f50,plain,(
% 0.21/0.41    ( ! [X2,X0] : (~v1_relat_1(X2) | ~v1_funct_1(X2) | ~r2_hidden(X0,k1_relat_1(X2)) | r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2)) )),
% 0.21/0.41    inference(equality_resolution,[],[f43])).
% 0.21/0.41  fof(f43,plain,(
% 0.21/0.41    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~v1_funct_1(X2) | ~r2_hidden(X0,k1_relat_1(X2)) | k1_funct_1(X2,X0) != X1 | r2_hidden(k4_tarski(X0,X1),X2)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f18])).
% 0.21/0.41  fof(f18,plain,(
% 0.21/0.41    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.41    inference(flattening,[],[f17])).
% 0.21/0.41  fof(f17,plain,(
% 0.21/0.41    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.21/0.41    inference(ennf_transformation,[],[f4])).
% 0.21/0.41  fof(f4,axiom,(
% 0.21/0.41    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).
% 0.21/0.41  fof(f122,plain,(
% 0.21/0.41    spl7_18),
% 0.21/0.41    inference(avatar_split_clause,[],[f44,f120])).
% 0.21/0.41  fof(f44,plain,(
% 0.21/0.41    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f19])).
% 0.21/0.41  fof(f19,plain,(
% 0.21/0.41    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.41    inference(ennf_transformation,[],[f6])).
% 0.21/0.41  fof(f6,axiom,(
% 0.21/0.41    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.21/0.41  fof(f98,plain,(
% 0.21/0.41    spl7_12),
% 0.21/0.41    inference(avatar_split_clause,[],[f34,f96])).
% 0.21/0.41  fof(f34,plain,(
% 0.21/0.41    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relat_1(X2) = k1_relset_1(X0,X1,X2)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f14])).
% 0.21/0.41  fof(f14,plain,(
% 0.21/0.41    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.41    inference(ennf_transformation,[],[f5])).
% 0.21/0.41  fof(f5,axiom,(
% 0.21/0.41    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.41  fof(f90,plain,(
% 0.21/0.41    spl7_10),
% 0.21/0.41    inference(avatar_split_clause,[],[f28,f88])).
% 0.21/0.41  fof(f28,plain,(
% 0.21/0.41    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f12])).
% 0.21/0.41  fof(f12,plain,(
% 0.21/0.41    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.41    inference(ennf_transformation,[],[f1])).
% 0.21/0.41  fof(f1,axiom,(
% 0.21/0.41    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.41  fof(f86,plain,(
% 0.21/0.41    spl7_9),
% 0.21/0.41    inference(avatar_split_clause,[],[f29,f84])).
% 0.21/0.41  fof(f29,plain,(
% 0.21/0.41    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.41    inference(cnf_transformation,[],[f2])).
% 0.21/0.42  fof(f2,axiom,(
% 0.21/0.42    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.42  fof(f82,plain,(
% 0.21/0.42    ~spl7_8),
% 0.21/0.42    inference(avatar_split_clause,[],[f23,f80])).
% 0.21/0.42  fof(f23,plain,(
% 0.21/0.42    ~r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))),
% 0.21/0.42    inference(cnf_transformation,[],[f11])).
% 0.21/0.42  fof(f11,plain,(
% 0.21/0.42    ? [X0,X1,X2,X3] : (? [X4] : (~r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) & ? [X5] : (k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.21/0.42    inference(flattening,[],[f10])).
% 0.21/0.42  fof(f10,plain,(
% 0.21/0.42    ? [X0,X1,X2,X3] : ((? [X4] : (~r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) & ? [X5] : (k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.21/0.42    inference(ennf_transformation,[],[f9])).
% 0.21/0.42  fof(f9,negated_conjecture,(
% 0.21/0.42    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => ! [X4] : (? [X5] : (k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) => r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)))))),
% 0.21/0.42    inference(negated_conjecture,[],[f8])).
% 0.21/0.42  fof(f8,conjecture,(
% 0.21/0.42    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => ! [X4] : (? [X5] : (k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) => r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)))))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_2)).
% 0.21/0.42  fof(f78,plain,(
% 0.21/0.42    spl7_7),
% 0.21/0.42    inference(avatar_split_clause,[],[f26,f76])).
% 0.21/0.42  fof(f26,plain,(
% 0.21/0.42    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.42    inference(cnf_transformation,[],[f11])).
% 0.21/0.42  fof(f74,plain,(
% 0.21/0.42    spl7_6),
% 0.21/0.42    inference(avatar_split_clause,[],[f22,f72])).
% 0.21/0.42  fof(f22,plain,(
% 0.21/0.42    sK4 = k1_funct_1(sK3,sK5)),
% 0.21/0.42    inference(cnf_transformation,[],[f11])).
% 0.21/0.42  fof(f70,plain,(
% 0.21/0.42    spl7_5),
% 0.21/0.42    inference(avatar_split_clause,[],[f25,f68])).
% 0.21/0.42  fof(f25,plain,(
% 0.21/0.42    v1_funct_2(sK3,sK0,sK1)),
% 0.21/0.42    inference(cnf_transformation,[],[f11])).
% 0.21/0.42  fof(f66,plain,(
% 0.21/0.42    ~spl7_4),
% 0.21/0.42    inference(avatar_split_clause,[],[f27,f64])).
% 0.21/0.42  fof(f27,plain,(
% 0.21/0.42    k1_xboole_0 != sK1),
% 0.21/0.42    inference(cnf_transformation,[],[f11])).
% 0.21/0.42  fof(f62,plain,(
% 0.21/0.42    spl7_3),
% 0.21/0.42    inference(avatar_split_clause,[],[f21,f60])).
% 0.21/0.42  fof(f21,plain,(
% 0.21/0.42    r2_hidden(sK5,sK2)),
% 0.21/0.42    inference(cnf_transformation,[],[f11])).
% 0.21/0.42  fof(f58,plain,(
% 0.21/0.42    spl7_2),
% 0.21/0.42    inference(avatar_split_clause,[],[f20,f56])).
% 0.21/0.42  fof(f20,plain,(
% 0.21/0.42    r2_hidden(sK5,sK0)),
% 0.21/0.42    inference(cnf_transformation,[],[f11])).
% 0.21/0.42  fof(f54,plain,(
% 0.21/0.42    spl7_1),
% 0.21/0.42    inference(avatar_split_clause,[],[f24,f52])).
% 0.21/0.42  fof(f24,plain,(
% 0.21/0.42    v1_funct_1(sK3)),
% 0.21/0.42    inference(cnf_transformation,[],[f11])).
% 0.21/0.42  % SZS output end Proof for theBenchmark
% 0.21/0.42  % (1204)------------------------------
% 0.21/0.42  % (1204)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.42  % (1204)Termination reason: Refutation
% 0.21/0.42  
% 0.21/0.42  % (1204)Memory used [KB]: 10746
% 0.21/0.42  % (1204)Time elapsed: 0.009 s
% 0.21/0.42  % (1204)------------------------------
% 0.21/0.42  % (1204)------------------------------
% 0.21/0.42  % (1194)Success in time 0.062 s
%------------------------------------------------------------------------------
