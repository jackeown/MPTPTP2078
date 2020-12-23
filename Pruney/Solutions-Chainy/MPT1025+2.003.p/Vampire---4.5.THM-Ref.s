%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:21 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  155 ( 311 expanded)
%              Number of leaves         :   35 ( 114 expanded)
%              Depth                    :   11
%              Number of atoms          :  506 (1374 expanded)
%              Number of equality atoms :  106 ( 296 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1954,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f134,f183,f211,f319,f354,f396,f459,f548,f1383,f1547,f1662,f1684,f1770,f1827,f1892,f1893,f1894,f1942])).

fof(f1942,plain,
    ( ~ spl7_6
    | spl7_7
    | ~ spl7_14
    | ~ spl7_33 ),
    inference(avatar_contradiction_clause,[],[f1927])).

fof(f1927,plain,
    ( $false
    | ~ spl7_6
    | spl7_7
    | ~ spl7_14
    | ~ spl7_33 ),
    inference(unit_resulting_resolution,[],[f496,f1896])).

fof(f1896,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | ~ spl7_6
    | spl7_7
    | ~ spl7_14 ),
    inference(forward_demodulation,[],[f1895,f202])).

fof(f202,plain,
    ( k1_xboole_0 = sK0
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f200])).

fof(f200,plain,
    ( spl7_14
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f1895,plain,
    ( sK0 != k1_relset_1(sK0,k1_xboole_0,sK3)
    | ~ spl7_6
    | spl7_7 ),
    inference(forward_demodulation,[],[f124,f121])).

fof(f121,plain,
    ( k1_xboole_0 = sK1
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl7_6
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f124,plain,
    ( sK0 != k1_relset_1(sK0,sK1,sK3)
    | spl7_7 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl7_7
  <=> sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f496,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | ~ spl7_33 ),
    inference(avatar_component_clause,[],[f494])).

fof(f494,plain,
    ( spl7_33
  <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_33])])).

fof(f1894,plain,
    ( ~ spl7_1
    | spl7_27
    | ~ spl7_13 ),
    inference(avatar_split_clause,[],[f1888,f174,f383,f96])).

fof(f96,plain,
    ( spl7_1
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f383,plain,
    ( spl7_27
  <=> r2_hidden(sK6(sK4,sK2,sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).

fof(f174,plain,
    ( spl7_13
  <=> r2_hidden(sK4,k9_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f1888,plain,
    ( r2_hidden(sK6(sK4,sK2,sK3),sK2)
    | ~ v1_relat_1(sK3)
    | ~ spl7_13 ),
    inference(resolution,[],[f176,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK6(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ( r2_hidden(sK6(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(sK6(X0,X1,X2),X0),X2)
            & r2_hidden(sK6(X0,X1,X2),k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f46,f47])).

fof(f47,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK6(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK6(X0,X1,X2),X0),X2)
        & r2_hidden(sK6(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X4,X0),X2)
              & r2_hidden(X4,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X3,X0),X2)
              & r2_hidden(X3,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

fof(f176,plain,
    ( r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f174])).

fof(f1893,plain,
    ( ~ spl7_1
    | spl7_26
    | ~ spl7_13 ),
    inference(avatar_split_clause,[],[f1887,f174,f378,f96])).

fof(f378,plain,
    ( spl7_26
  <=> r2_hidden(k4_tarski(sK6(sK4,sK2,sK3),sK4),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).

fof(f1887,plain,
    ( r2_hidden(k4_tarski(sK6(sK4,sK2,sK3),sK4),sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl7_13 ),
    inference(resolution,[],[f176,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK6(X0,X1,X2),X0),X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f1892,plain,
    ( ~ spl7_1
    | spl7_25
    | ~ spl7_13 ),
    inference(avatar_split_clause,[],[f1886,f174,f373,f96])).

fof(f373,plain,
    ( spl7_25
  <=> r2_hidden(sK6(sK4,sK2,sK3),k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).

fof(f1886,plain,
    ( r2_hidden(sK6(sK4,sK2,sK3),k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ spl7_13 ),
    inference(resolution,[],[f176,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK6(X0,X1,X2),k1_relat_1(X2))
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f1827,plain,
    ( spl7_33
    | ~ spl7_16
    | ~ spl7_6
    | ~ spl7_14 ),
    inference(avatar_split_clause,[],[f1826,f200,f119,f208,f494])).

fof(f208,plain,
    ( spl7_16
  <=> m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f1826,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | ~ spl7_6
    | ~ spl7_14 ),
    inference(forward_demodulation,[],[f1816,f90])).

fof(f90,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f82])).

fof(f82,plain,(
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
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f1816,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl7_6
    | ~ spl7_14 ),
    inference(resolution,[],[f1813,f89])).

fof(f89,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
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
    inference(nnf_transformation,[],[f29])).

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
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
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

fof(f1813,plain,
    ( v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | ~ spl7_6
    | ~ spl7_14 ),
    inference(backward_demodulation,[],[f1698,f202])).

fof(f1698,plain,
    ( v1_funct_2(sK3,sK0,k1_xboole_0)
    | ~ spl7_6 ),
    inference(backward_demodulation,[],[f52,f121])).

fof(f52,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,
    ( ! [X5] :
        ( k1_funct_1(sK3,X5) != sK4
        | ~ r2_hidden(X5,sK2)
        | ~ m1_subset_1(X5,sK0) )
    & r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f21,f36,f35])).

fof(f35,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( ! [X5] :
                ( k1_funct_1(X3,X5) != X4
                | ~ r2_hidden(X5,X2)
                | ~ m1_subset_1(X5,X0) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(sK3,X5) != X4
              | ~ r2_hidden(X5,sK2)
              | ~ m1_subset_1(X5,sK0) )
          & r2_hidden(X4,k7_relset_1(sK0,sK1,sK3,sK2)) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X4] :
        ( ! [X5] :
            ( k1_funct_1(sK3,X5) != X4
            | ~ r2_hidden(X5,sK2)
            | ~ m1_subset_1(X5,sK0) )
        & r2_hidden(X4,k7_relset_1(sK0,sK1,sK3,sK2)) )
   => ( ! [X5] :
          ( k1_funct_1(sK3,X5) != sK4
          | ~ r2_hidden(X5,sK2)
          | ~ m1_subset_1(X5,sK0) )
      & r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ! [X4] :
            ~ ( ! [X5] :
                  ( m1_subset_1(X5,X0)
                 => ~ ( k1_funct_1(X3,X5) = X4
                      & r2_hidden(X5,X2) ) )
              & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ~ ( ! [X5] :
                ( m1_subset_1(X5,X0)
               => ~ ( k1_funct_1(X3,X5) = X4
                    & r2_hidden(X5,X2) ) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_funct_2)).

fof(f1770,plain,
    ( ~ spl7_15
    | spl7_50 ),
    inference(avatar_contradiction_clause,[],[f1758])).

fof(f1758,plain,
    ( $false
    | ~ spl7_15
    | spl7_50 ),
    inference(unit_resulting_resolution,[],[f83,f1723])).

fof(f1723,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl7_15
    | spl7_50 ),
    inference(backward_demodulation,[],[f763,f206])).

fof(f206,plain,
    ( k1_xboole_0 = sK3
    | ~ spl7_15 ),
    inference(avatar_component_clause,[],[f204])).

fof(f204,plain,
    ( spl7_15
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f763,plain,
    ( ~ v1_xboole_0(sK3)
    | spl7_50 ),
    inference(avatar_component_clause,[],[f762])).

fof(f762,plain,
    ( spl7_50
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_50])])).

fof(f83,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f1684,plain,
    ( ~ spl7_1
    | ~ spl7_12
    | spl7_48
    | ~ spl7_26 ),
    inference(avatar_split_clause,[],[f1670,f378,f748,f163,f96])).

fof(f163,plain,
    ( spl7_12
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f748,plain,
    ( spl7_48
  <=> sK4 = k1_funct_1(sK3,sK6(sK4,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_48])])).

fof(f1670,plain,
    ( sK4 = k1_funct_1(sK3,sK6(sK4,sK2,sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl7_26 ),
    inference(resolution,[],[f380,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,X0) = X1
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

fof(f380,plain,
    ( r2_hidden(k4_tarski(sK6(sK4,sK2,sK3),sK4),sK3)
    | ~ spl7_26 ),
    inference(avatar_component_clause,[],[f378])).

fof(f1662,plain,
    ( ~ spl7_27
    | ~ spl7_48
    | ~ spl7_25
    | ~ spl7_28 ),
    inference(avatar_split_clause,[],[f1657,f392,f373,f748,f383])).

fof(f392,plain,
    ( spl7_28
  <=> sK0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).

fof(f1657,plain,
    ( sK4 != k1_funct_1(sK3,sK6(sK4,sK2,sK3))
    | ~ r2_hidden(sK6(sK4,sK2,sK3),sK2)
    | ~ spl7_25
    | ~ spl7_28 ),
    inference(resolution,[],[f1656,f178])).

fof(f178,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | sK4 != k1_funct_1(sK3,X0)
      | ~ r2_hidden(X0,sK2) ) ),
    inference(resolution,[],[f55,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f55,plain,(
    ! [X5] :
      ( ~ m1_subset_1(X5,sK0)
      | ~ r2_hidden(X5,sK2)
      | k1_funct_1(sK3,X5) != sK4 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f1656,plain,
    ( r2_hidden(sK6(sK4,sK2,sK3),sK0)
    | ~ spl7_25
    | ~ spl7_28 ),
    inference(forward_demodulation,[],[f375,f394])).

fof(f394,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl7_28 ),
    inference(avatar_component_clause,[],[f392])).

fof(f375,plain,
    ( r2_hidden(sK6(sK4,sK2,sK3),k1_relat_1(sK3))
    | ~ spl7_25 ),
    inference(avatar_component_clause,[],[f373])).

fof(f1547,plain,
    ( ~ spl7_1
    | ~ spl7_13
    | ~ spl7_50 ),
    inference(avatar_contradiction_clause,[],[f1541])).

fof(f1541,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_13
    | ~ spl7_50 ),
    inference(unit_resulting_resolution,[],[f97,f176,f1540,f73])).

fof(f1540,plain,
    ( ! [X2] : ~ r2_hidden(X2,sK3)
    | ~ spl7_50 ),
    inference(resolution,[],[f764,f61])).

fof(f61,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK5(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f41,f42])).

fof(f42,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK5(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f764,plain,
    ( v1_xboole_0(sK3)
    | ~ spl7_50 ),
    inference(avatar_component_clause,[],[f762])).

fof(f97,plain,
    ( v1_relat_1(sK3)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f96])).

fof(f1383,plain,
    ( spl7_6
    | ~ spl7_8
    | spl7_7 ),
    inference(avatar_split_clause,[],[f1378,f123,f136,f119])).

fof(f136,plain,
    ( spl7_8
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f1378,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ v1_funct_2(sK3,sK0,sK1)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f53,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f53,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f37])).

fof(f548,plain,(
    spl7_12 ),
    inference(avatar_contradiction_clause,[],[f545])).

fof(f545,plain,
    ( $false
    | spl7_12 ),
    inference(unit_resulting_resolution,[],[f51,f165])).

fof(f165,plain,
    ( ~ v1_funct_1(sK3)
    | spl7_12 ),
    inference(avatar_component_clause,[],[f163])).

fof(f51,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f459,plain,
    ( ~ spl7_6
    | spl7_16 ),
    inference(avatar_contradiction_clause,[],[f446])).

fof(f446,plain,
    ( $false
    | ~ spl7_6
    | spl7_16 ),
    inference(unit_resulting_resolution,[],[f64,f300,f430,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f430,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_6 ),
    inference(forward_demodulation,[],[f426,f90])).

fof(f426,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl7_6 ),
    inference(backward_demodulation,[],[f53,f121])).

fof(f300,plain,
    ( ~ r2_hidden(sK3,k1_zfmisc_1(k1_xboole_0))
    | spl7_16 ),
    inference(resolution,[],[f210,f60])).

fof(f210,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | spl7_16 ),
    inference(avatar_component_clause,[],[f208])).

fof(f64,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f396,plain,
    ( ~ spl7_5
    | spl7_28
    | ~ spl7_7 ),
    inference(avatar_split_clause,[],[f388,f123,f392,f115])).

fof(f115,plain,
    ( spl7_5
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f388,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_7 ),
    inference(superposition,[],[f79,f125])).

fof(f125,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f123])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f354,plain,(
    spl7_5 ),
    inference(avatar_contradiction_clause,[],[f350])).

fof(f350,plain,
    ( $false
    | spl7_5 ),
    inference(unit_resulting_resolution,[],[f53,f117])).

fof(f117,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl7_5 ),
    inference(avatar_component_clause,[],[f115])).

fof(f319,plain,
    ( ~ spl7_5
    | spl7_13 ),
    inference(avatar_split_clause,[],[f318,f174,f115])).

fof(f318,plain,
    ( r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f54,f63])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f54,plain,(
    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f37])).

fof(f211,plain,
    ( spl7_14
    | spl7_15
    | ~ spl7_16
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f198,f119,f208,f204,f200])).

fof(f198,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | ~ spl7_6 ),
    inference(forward_demodulation,[],[f189,f90])).

fof(f189,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl7_6 ),
    inference(resolution,[],[f187,f87])).

fof(f87,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f187,plain,
    ( v1_funct_2(sK3,sK0,k1_xboole_0)
    | ~ spl7_6 ),
    inference(backward_demodulation,[],[f52,f121])).

fof(f183,plain,(
    spl7_8 ),
    inference(avatar_contradiction_clause,[],[f179])).

fof(f179,plain,
    ( $false
    | spl7_8 ),
    inference(unit_resulting_resolution,[],[f52,f138])).

fof(f138,plain,
    ( ~ v1_funct_2(sK3,sK0,sK1)
    | spl7_8 ),
    inference(avatar_component_clause,[],[f136])).

fof(f134,plain,(
    spl7_1 ),
    inference(avatar_contradiction_clause,[],[f127])).

fof(f127,plain,
    ( $false
    | spl7_1 ),
    inference(unit_resulting_resolution,[],[f98,f65,f53,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f65,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f98,plain,
    ( ~ v1_relat_1(sK3)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f96])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:54:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.45  % (27891)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.47  % (27895)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.48  % (27887)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.49  % (27885)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.49  % (27891)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f1954,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f134,f183,f211,f319,f354,f396,f459,f548,f1383,f1547,f1662,f1684,f1770,f1827,f1892,f1893,f1894,f1942])).
% 0.21/0.49  fof(f1942,plain,(
% 0.21/0.49    ~spl7_6 | spl7_7 | ~spl7_14 | ~spl7_33),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f1927])).
% 0.21/0.49  fof(f1927,plain,(
% 0.21/0.49    $false | (~spl7_6 | spl7_7 | ~spl7_14 | ~spl7_33)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f496,f1896])).
% 0.21/0.49  fof(f1896,plain,(
% 0.21/0.49    k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) | (~spl7_6 | spl7_7 | ~spl7_14)),
% 0.21/0.49    inference(forward_demodulation,[],[f1895,f202])).
% 0.21/0.49  fof(f202,plain,(
% 0.21/0.49    k1_xboole_0 = sK0 | ~spl7_14),
% 0.21/0.49    inference(avatar_component_clause,[],[f200])).
% 0.21/0.49  fof(f200,plain,(
% 0.21/0.49    spl7_14 <=> k1_xboole_0 = sK0),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 0.21/0.49  fof(f1895,plain,(
% 0.21/0.49    sK0 != k1_relset_1(sK0,k1_xboole_0,sK3) | (~spl7_6 | spl7_7)),
% 0.21/0.49    inference(forward_demodulation,[],[f124,f121])).
% 0.21/0.49  fof(f121,plain,(
% 0.21/0.49    k1_xboole_0 = sK1 | ~spl7_6),
% 0.21/0.49    inference(avatar_component_clause,[],[f119])).
% 0.21/0.49  fof(f119,plain,(
% 0.21/0.49    spl7_6 <=> k1_xboole_0 = sK1),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.21/0.49  fof(f124,plain,(
% 0.21/0.49    sK0 != k1_relset_1(sK0,sK1,sK3) | spl7_7),
% 0.21/0.49    inference(avatar_component_clause,[],[f123])).
% 0.21/0.49  fof(f123,plain,(
% 0.21/0.49    spl7_7 <=> sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.21/0.49  fof(f496,plain,(
% 0.21/0.49    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) | ~spl7_33),
% 0.21/0.49    inference(avatar_component_clause,[],[f494])).
% 0.21/0.49  fof(f494,plain,(
% 0.21/0.49    spl7_33 <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_33])])).
% 0.21/0.49  fof(f1894,plain,(
% 0.21/0.49    ~spl7_1 | spl7_27 | ~spl7_13),
% 0.21/0.49    inference(avatar_split_clause,[],[f1888,f174,f383,f96])).
% 0.21/0.49  fof(f96,plain,(
% 0.21/0.49    spl7_1 <=> v1_relat_1(sK3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.21/0.49  fof(f383,plain,(
% 0.21/0.49    spl7_27 <=> r2_hidden(sK6(sK4,sK2,sK3),sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).
% 0.21/0.49  fof(f174,plain,(
% 0.21/0.49    spl7_13 <=> r2_hidden(sK4,k9_relat_1(sK3,sK2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 0.21/0.49  fof(f1888,plain,(
% 0.21/0.49    r2_hidden(sK6(sK4,sK2,sK3),sK2) | ~v1_relat_1(sK3) | ~spl7_13),
% 0.21/0.49    inference(resolution,[],[f176,f74])).
% 0.21/0.49  fof(f74,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (r2_hidden(sK6(X0,X1,X2),X1) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f48])).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK6(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK6(X0,X1,X2),X0),X2) & r2_hidden(sK6(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f46,f47])).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK6(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK6(X0,X1,X2),X0),X2) & r2_hidden(sK6(X0,X1,X2),k1_relat_1(X2))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.21/0.49    inference(rectify,[],[f45])).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.21/0.49    inference(nnf_transformation,[],[f30])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.21/0.49    inference(ennf_transformation,[],[f13])).
% 0.21/0.49  fof(f13,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).
% 0.21/0.49  fof(f176,plain,(
% 0.21/0.49    r2_hidden(sK4,k9_relat_1(sK3,sK2)) | ~spl7_13),
% 0.21/0.49    inference(avatar_component_clause,[],[f174])).
% 0.21/0.49  fof(f1893,plain,(
% 0.21/0.49    ~spl7_1 | spl7_26 | ~spl7_13),
% 0.21/0.49    inference(avatar_split_clause,[],[f1887,f174,f378,f96])).
% 0.21/0.49  fof(f378,plain,(
% 0.21/0.49    spl7_26 <=> r2_hidden(k4_tarski(sK6(sK4,sK2,sK3),sK4),sK3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).
% 0.21/0.49  fof(f1887,plain,(
% 0.21/0.49    r2_hidden(k4_tarski(sK6(sK4,sK2,sK3),sK4),sK3) | ~v1_relat_1(sK3) | ~spl7_13),
% 0.21/0.49    inference(resolution,[],[f176,f73])).
% 0.21/0.49  fof(f73,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK6(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f48])).
% 0.21/0.49  fof(f1892,plain,(
% 0.21/0.49    ~spl7_1 | spl7_25 | ~spl7_13),
% 0.21/0.49    inference(avatar_split_clause,[],[f1886,f174,f373,f96])).
% 0.21/0.49  fof(f373,plain,(
% 0.21/0.49    spl7_25 <=> r2_hidden(sK6(sK4,sK2,sK3),k1_relat_1(sK3))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).
% 0.21/0.49  fof(f1886,plain,(
% 0.21/0.49    r2_hidden(sK6(sK4,sK2,sK3),k1_relat_1(sK3)) | ~v1_relat_1(sK3) | ~spl7_13),
% 0.21/0.49    inference(resolution,[],[f176,f72])).
% 0.21/0.49  fof(f72,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (r2_hidden(sK6(X0,X1,X2),k1_relat_1(X2)) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f48])).
% 0.21/0.49  fof(f1827,plain,(
% 0.21/0.49    spl7_33 | ~spl7_16 | ~spl7_6 | ~spl7_14),
% 0.21/0.49    inference(avatar_split_clause,[],[f1826,f200,f119,f208,f494])).
% 0.21/0.49  fof(f208,plain,(
% 0.21/0.49    spl7_16 <=> m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).
% 0.21/0.49  fof(f1826,plain,(
% 0.21/0.49    ~m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) | (~spl7_6 | ~spl7_14)),
% 0.21/0.49    inference(forward_demodulation,[],[f1816,f90])).
% 0.21/0.49  fof(f90,plain,(
% 0.21/0.49    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.21/0.49    inference(equality_resolution,[],[f82])).
% 0.21/0.49  fof(f82,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.21/0.49    inference(cnf_transformation,[],[f50])).
% 0.21/0.49  fof(f50,plain,(
% 0.21/0.49    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.49    inference(flattening,[],[f49])).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.49    inference(nnf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.49  fof(f1816,plain,(
% 0.21/0.49    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl7_6 | ~spl7_14)),
% 0.21/0.49    inference(resolution,[],[f1813,f89])).
% 0.21/0.49  fof(f89,plain,(
% 0.21/0.49    ( ! [X2,X1] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 0.21/0.49    inference(equality_resolution,[],[f67])).
% 0.21/0.49  fof(f67,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f44])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(nnf_transformation,[],[f29])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(flattening,[],[f28])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f17])).
% 0.21/0.49  fof(f17,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.49  fof(f1813,plain,(
% 0.21/0.49    v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | (~spl7_6 | ~spl7_14)),
% 0.21/0.49    inference(backward_demodulation,[],[f1698,f202])).
% 0.21/0.49  fof(f1698,plain,(
% 0.21/0.49    v1_funct_2(sK3,sK0,k1_xboole_0) | ~spl7_6),
% 0.21/0.49    inference(backward_demodulation,[],[f52,f121])).
% 0.21/0.49  fof(f52,plain,(
% 0.21/0.49    v1_funct_2(sK3,sK0,sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f37])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    (! [X5] : (k1_funct_1(sK3,X5) != sK4 | ~r2_hidden(X5,sK2) | ~m1_subset_1(X5,sK0)) & r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f21,f36,f35])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (? [X4] : (! [X5] : (k1_funct_1(sK3,X5) != X4 | ~r2_hidden(X5,sK2) | ~m1_subset_1(X5,sK0)) & r2_hidden(X4,k7_relset_1(sK0,sK1,sK3,sK2))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ? [X4] : (! [X5] : (k1_funct_1(sK3,X5) != X4 | ~r2_hidden(X5,sK2) | ~m1_subset_1(X5,sK0)) & r2_hidden(X4,k7_relset_1(sK0,sK1,sK3,sK2))) => (! [X5] : (k1_funct_1(sK3,X5) != sK4 | ~r2_hidden(X5,sK2) | ~m1_subset_1(X5,sK0)) & r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.21/0.49    inference(flattening,[],[f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : ((k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2)) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.21/0.49    inference(ennf_transformation,[],[f19])).
% 0.21/0.49  fof(f19,negated_conjecture,(
% 0.21/0.49    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 0.21/0.49    inference(negated_conjecture,[],[f18])).
% 0.21/0.49  fof(f18,conjecture,(
% 0.21/0.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_funct_2)).
% 0.21/0.49  fof(f1770,plain,(
% 0.21/0.49    ~spl7_15 | spl7_50),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f1758])).
% 0.21/0.49  fof(f1758,plain,(
% 0.21/0.49    $false | (~spl7_15 | spl7_50)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f83,f1723])).
% 0.21/0.49  fof(f1723,plain,(
% 0.21/0.49    ~v1_xboole_0(k1_xboole_0) | (~spl7_15 | spl7_50)),
% 0.21/0.49    inference(backward_demodulation,[],[f763,f206])).
% 0.21/0.49  fof(f206,plain,(
% 0.21/0.49    k1_xboole_0 = sK3 | ~spl7_15),
% 0.21/0.49    inference(avatar_component_clause,[],[f204])).
% 0.21/0.49  fof(f204,plain,(
% 0.21/0.49    spl7_15 <=> k1_xboole_0 = sK3),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 0.21/0.49  fof(f763,plain,(
% 0.21/0.49    ~v1_xboole_0(sK3) | spl7_50),
% 0.21/0.49    inference(avatar_component_clause,[],[f762])).
% 0.21/0.49  fof(f762,plain,(
% 0.21/0.49    spl7_50 <=> v1_xboole_0(sK3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_50])])).
% 0.21/0.49  fof(f83,plain,(
% 0.21/0.49    v1_xboole_0(k1_xboole_0)),
% 0.21/0.49    inference(cnf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    v1_xboole_0(k1_xboole_0)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.49  fof(f1684,plain,(
% 0.21/0.49    ~spl7_1 | ~spl7_12 | spl7_48 | ~spl7_26),
% 0.21/0.49    inference(avatar_split_clause,[],[f1670,f378,f748,f163,f96])).
% 0.21/0.49  fof(f163,plain,(
% 0.21/0.49    spl7_12 <=> v1_funct_1(sK3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 0.21/0.49  fof(f748,plain,(
% 0.21/0.49    spl7_48 <=> sK4 = k1_funct_1(sK3,sK6(sK4,sK2,sK3))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_48])])).
% 0.21/0.49  fof(f1670,plain,(
% 0.21/0.49    sK4 = k1_funct_1(sK3,sK6(sK4,sK2,sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl7_26),
% 0.21/0.49    inference(resolution,[],[f380,f57])).
% 0.21/0.49  fof(f57,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k1_funct_1(X2,X0) = X1 | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f39])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.50    inference(flattening,[],[f38])).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.50    inference(nnf_transformation,[],[f23])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.50    inference(flattening,[],[f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.21/0.50    inference(ennf_transformation,[],[f14])).
% 0.21/0.50  fof(f14,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).
% 0.21/0.50  fof(f380,plain,(
% 0.21/0.50    r2_hidden(k4_tarski(sK6(sK4,sK2,sK3),sK4),sK3) | ~spl7_26),
% 0.21/0.50    inference(avatar_component_clause,[],[f378])).
% 0.21/0.50  fof(f1662,plain,(
% 0.21/0.50    ~spl7_27 | ~spl7_48 | ~spl7_25 | ~spl7_28),
% 0.21/0.50    inference(avatar_split_clause,[],[f1657,f392,f373,f748,f383])).
% 0.21/0.50  fof(f392,plain,(
% 0.21/0.50    spl7_28 <=> sK0 = k1_relat_1(sK3)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).
% 0.21/0.50  fof(f1657,plain,(
% 0.21/0.50    sK4 != k1_funct_1(sK3,sK6(sK4,sK2,sK3)) | ~r2_hidden(sK6(sK4,sK2,sK3),sK2) | (~spl7_25 | ~spl7_28)),
% 0.21/0.50    inference(resolution,[],[f1656,f178])).
% 0.21/0.50  fof(f178,plain,(
% 0.21/0.50    ( ! [X0] : (~r2_hidden(X0,sK0) | sK4 != k1_funct_1(sK3,X0) | ~r2_hidden(X0,sK2)) )),
% 0.21/0.50    inference(resolution,[],[f55,f60])).
% 0.21/0.50  fof(f60,plain,(
% 0.21/0.50    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f26])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,axiom,(
% 0.21/0.50    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 0.21/0.50  fof(f55,plain,(
% 0.21/0.50    ( ! [X5] : (~m1_subset_1(X5,sK0) | ~r2_hidden(X5,sK2) | k1_funct_1(sK3,X5) != sK4) )),
% 0.21/0.50    inference(cnf_transformation,[],[f37])).
% 0.21/0.50  fof(f1656,plain,(
% 0.21/0.50    r2_hidden(sK6(sK4,sK2,sK3),sK0) | (~spl7_25 | ~spl7_28)),
% 0.21/0.50    inference(forward_demodulation,[],[f375,f394])).
% 0.21/0.50  fof(f394,plain,(
% 0.21/0.50    sK0 = k1_relat_1(sK3) | ~spl7_28),
% 0.21/0.50    inference(avatar_component_clause,[],[f392])).
% 0.21/0.50  fof(f375,plain,(
% 0.21/0.50    r2_hidden(sK6(sK4,sK2,sK3),k1_relat_1(sK3)) | ~spl7_25),
% 0.21/0.50    inference(avatar_component_clause,[],[f373])).
% 0.21/0.50  fof(f1547,plain,(
% 0.21/0.50    ~spl7_1 | ~spl7_13 | ~spl7_50),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f1541])).
% 0.21/0.50  fof(f1541,plain,(
% 0.21/0.50    $false | (~spl7_1 | ~spl7_13 | ~spl7_50)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f97,f176,f1540,f73])).
% 0.21/0.50  fof(f1540,plain,(
% 0.21/0.50    ( ! [X2] : (~r2_hidden(X2,sK3)) ) | ~spl7_50),
% 0.21/0.50    inference(resolution,[],[f764,f61])).
% 0.21/0.50  fof(f61,plain,(
% 0.21/0.50    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f43])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK5(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f41,f42])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK5(X0),X0))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.50    inference(rectify,[],[f40])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.50    inference(nnf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.50  fof(f764,plain,(
% 0.21/0.50    v1_xboole_0(sK3) | ~spl7_50),
% 0.21/0.50    inference(avatar_component_clause,[],[f762])).
% 0.21/0.50  fof(f97,plain,(
% 0.21/0.50    v1_relat_1(sK3) | ~spl7_1),
% 0.21/0.50    inference(avatar_component_clause,[],[f96])).
% 0.21/0.50  fof(f1383,plain,(
% 0.21/0.50    spl7_6 | ~spl7_8 | spl7_7),
% 0.21/0.50    inference(avatar_split_clause,[],[f1378,f123,f136,f119])).
% 0.21/0.50  fof(f136,plain,(
% 0.21/0.50    spl7_8 <=> v1_funct_2(sK3,sK0,sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.21/0.50  fof(f1378,plain,(
% 0.21/0.50    sK0 = k1_relset_1(sK0,sK1,sK3) | ~v1_funct_2(sK3,sK0,sK1) | k1_xboole_0 = sK1),
% 0.21/0.50    inference(resolution,[],[f53,f66])).
% 0.21/0.50  fof(f66,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f44])).
% 0.21/0.50  fof(f53,plain,(
% 0.21/0.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.50    inference(cnf_transformation,[],[f37])).
% 0.21/0.50  fof(f548,plain,(
% 0.21/0.50    spl7_12),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f545])).
% 0.21/0.50  fof(f545,plain,(
% 0.21/0.50    $false | spl7_12),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f51,f165])).
% 0.21/0.50  fof(f165,plain,(
% 0.21/0.50    ~v1_funct_1(sK3) | spl7_12),
% 0.21/0.50    inference(avatar_component_clause,[],[f163])).
% 0.21/0.50  fof(f51,plain,(
% 0.21/0.50    v1_funct_1(sK3)),
% 0.21/0.50    inference(cnf_transformation,[],[f37])).
% 0.21/0.50  fof(f459,plain,(
% 0.21/0.50    ~spl7_6 | spl7_16),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f446])).
% 0.21/0.50  fof(f446,plain,(
% 0.21/0.50    $false | (~spl7_6 | spl7_16)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f64,f300,f430,f59])).
% 0.21/0.50  fof(f59,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f25])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.21/0.50    inference(flattening,[],[f24])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,axiom,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.21/0.50  fof(f430,plain,(
% 0.21/0.50    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | ~spl7_6),
% 0.21/0.50    inference(forward_demodulation,[],[f426,f90])).
% 0.21/0.50  fof(f426,plain,(
% 0.21/0.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | ~spl7_6),
% 0.21/0.50    inference(backward_demodulation,[],[f53,f121])).
% 0.21/0.50  fof(f300,plain,(
% 0.21/0.50    ~r2_hidden(sK3,k1_zfmisc_1(k1_xboole_0)) | spl7_16),
% 0.21/0.50    inference(resolution,[],[f210,f60])).
% 0.21/0.50  fof(f210,plain,(
% 0.21/0.50    ~m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | spl7_16),
% 0.21/0.50    inference(avatar_component_clause,[],[f208])).
% 0.21/0.50  fof(f64,plain,(
% 0.21/0.50    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 0.21/0.50  fof(f396,plain,(
% 0.21/0.50    ~spl7_5 | spl7_28 | ~spl7_7),
% 0.21/0.50    inference(avatar_split_clause,[],[f388,f123,f392,f115])).
% 0.21/0.50  fof(f115,plain,(
% 0.21/0.50    spl7_5 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.21/0.50  fof(f388,plain,(
% 0.21/0.50    sK0 = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl7_7),
% 0.21/0.50    inference(superposition,[],[f79,f125])).
% 0.21/0.50  fof(f125,plain,(
% 0.21/0.50    sK0 = k1_relset_1(sK0,sK1,sK3) | ~spl7_7),
% 0.21/0.50    inference(avatar_component_clause,[],[f123])).
% 0.21/0.50  fof(f79,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f34])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f15])).
% 0.21/0.50  fof(f15,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.50  fof(f354,plain,(
% 0.21/0.50    spl7_5),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f350])).
% 0.21/0.50  fof(f350,plain,(
% 0.21/0.50    $false | spl7_5),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f53,f117])).
% 0.21/0.50  fof(f117,plain,(
% 0.21/0.50    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl7_5),
% 0.21/0.50    inference(avatar_component_clause,[],[f115])).
% 0.21/0.50  fof(f319,plain,(
% 0.21/0.50    ~spl7_5 | spl7_13),
% 0.21/0.50    inference(avatar_split_clause,[],[f318,f174,f115])).
% 0.21/0.50  fof(f318,plain,(
% 0.21/0.50    r2_hidden(sK4,k9_relat_1(sK3,sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.50    inference(superposition,[],[f54,f63])).
% 0.21/0.50  fof(f63,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f27])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f16])).
% 0.21/0.50  fof(f16,axiom,(
% 0.21/0.50    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.21/0.50  fof(f54,plain,(
% 0.21/0.50    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))),
% 0.21/0.50    inference(cnf_transformation,[],[f37])).
% 0.21/0.50  fof(f211,plain,(
% 0.21/0.50    spl7_14 | spl7_15 | ~spl7_16 | ~spl7_6),
% 0.21/0.50    inference(avatar_split_clause,[],[f198,f119,f208,f204,f200])).
% 0.21/0.50  fof(f198,plain,(
% 0.21/0.50    ~m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | ~spl7_6),
% 0.21/0.50    inference(forward_demodulation,[],[f189,f90])).
% 0.21/0.50  fof(f189,plain,(
% 0.21/0.50    k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | ~spl7_6),
% 0.21/0.50    inference(resolution,[],[f187,f87])).
% 0.21/0.50  fof(f87,plain,(
% 0.21/0.50    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 0.21/0.50    inference(equality_resolution,[],[f70])).
% 0.21/0.50  fof(f70,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f44])).
% 0.21/0.50  fof(f187,plain,(
% 0.21/0.50    v1_funct_2(sK3,sK0,k1_xboole_0) | ~spl7_6),
% 0.21/0.50    inference(backward_demodulation,[],[f52,f121])).
% 0.21/0.50  fof(f183,plain,(
% 0.21/0.50    spl7_8),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f179])).
% 0.21/0.50  fof(f179,plain,(
% 0.21/0.50    $false | spl7_8),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f52,f138])).
% 0.21/0.50  fof(f138,plain,(
% 0.21/0.50    ~v1_funct_2(sK3,sK0,sK1) | spl7_8),
% 0.21/0.50    inference(avatar_component_clause,[],[f136])).
% 0.21/0.50  fof(f134,plain,(
% 0.21/0.50    spl7_1),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f127])).
% 0.21/0.50  fof(f127,plain,(
% 0.21/0.50    $false | spl7_1),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f98,f65,f53,f76])).
% 0.21/0.50  fof(f76,plain,(
% 0.21/0.50    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f31])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f11])).
% 0.21/0.50  fof(f11,axiom,(
% 0.21/0.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.50  fof(f65,plain,(
% 0.21/0.50    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f12])).
% 0.21/0.50  fof(f12,axiom,(
% 0.21/0.50    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.50  fof(f98,plain,(
% 0.21/0.50    ~v1_relat_1(sK3) | spl7_1),
% 0.21/0.50    inference(avatar_component_clause,[],[f96])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (27891)------------------------------
% 0.21/0.50  % (27891)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (27891)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (27891)Memory used [KB]: 6908
% 0.21/0.50  % (27891)Time elapsed: 0.044 s
% 0.21/0.50  % (27891)------------------------------
% 0.21/0.50  % (27891)------------------------------
% 0.21/0.50  % (27877)Success in time 0.139 s
%------------------------------------------------------------------------------
