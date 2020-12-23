%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:28 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  164 ( 302 expanded)
%              Number of leaves         :   39 ( 134 expanded)
%              Depth                    :    9
%              Number of atoms          :  466 ( 885 expanded)
%              Number of equality atoms :   80 ( 156 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f456,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f62,f66,f70,f83,f87,f92,f115,f126,f144,f160,f164,f176,f183,f210,f229,f246,f259,f276,f283,f296,f302,f359,f363,f385,f386,f399,f454,f455])).

fof(f455,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 != sK0
    | k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | k1_relat_1(sK3) != k1_relset_1(sK0,sK1,sK3)
    | m1_subset_1(sK6(sK4,sK2,sK3),sK0)
    | ~ m1_subset_1(sK6(sK4,sK2,sK3),k1_relat_1(sK3)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f454,plain,
    ( spl7_47
    | ~ spl7_39
    | ~ spl7_41 ),
    inference(avatar_split_clause,[],[f418,f397,f383,f452])).

fof(f452,plain,
    ( spl7_47
  <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_47])])).

fof(f383,plain,
    ( spl7_39
  <=> v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_39])])).

fof(f397,plain,
    ( spl7_41
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_41])])).

fof(f418,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | ~ spl7_39
    | ~ spl7_41 ),
    inference(subsumption_resolution,[],[f409,f384])).

fof(f384,plain,
    ( v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | ~ spl7_39 ),
    inference(avatar_component_clause,[],[f383])).

fof(f409,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | ~ v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | ~ spl7_41 ),
    inference(resolution,[],[f398,f54])).

fof(f54,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f398,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl7_41 ),
    inference(avatar_component_clause,[],[f397])).

fof(f399,plain,
    ( spl7_41
    | ~ spl7_3
    | ~ spl7_20
    | ~ spl7_30 ),
    inference(avatar_split_clause,[],[f375,f257,f181,f68,f397])).

fof(f68,plain,
    ( spl7_3
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f181,plain,
    ( spl7_20
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f257,plain,
    ( spl7_30
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).

fof(f375,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl7_3
    | ~ spl7_20
    | ~ spl7_30 ),
    inference(forward_demodulation,[],[f367,f182])).

fof(f182,plain,
    ( k1_xboole_0 = sK1
    | ~ spl7_20 ),
    inference(avatar_component_clause,[],[f181])).

fof(f367,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ spl7_3
    | ~ spl7_30 ),
    inference(superposition,[],[f69,f258])).

fof(f258,plain,
    ( k1_xboole_0 = sK0
    | ~ spl7_30 ),
    inference(avatar_component_clause,[],[f257])).

fof(f69,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f68])).

fof(f386,plain,
    ( spl7_24
    | ~ spl7_3
    | ~ spl7_20 ),
    inference(avatar_split_clause,[],[f326,f181,f68,f202])).

fof(f202,plain,
    ( spl7_24
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).

fof(f326,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl7_3
    | ~ spl7_20 ),
    inference(superposition,[],[f69,f182])).

fof(f385,plain,
    ( spl7_39
    | ~ spl7_22
    | ~ spl7_30 ),
    inference(avatar_split_clause,[],[f364,f257,f194,f383])).

fof(f194,plain,
    ( spl7_22
  <=> v1_funct_2(sK3,sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f364,plain,
    ( v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | ~ spl7_22
    | ~ spl7_30 ),
    inference(forward_demodulation,[],[f195,f258])).

fof(f195,plain,
    ( v1_funct_2(sK3,sK0,k1_xboole_0)
    | ~ spl7_22 ),
    inference(avatar_component_clause,[],[f194])).

fof(f363,plain,
    ( spl7_22
    | ~ spl7_2
    | ~ spl7_20 ),
    inference(avatar_split_clause,[],[f325,f181,f64,f194])).

fof(f64,plain,
    ( spl7_2
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f325,plain,
    ( v1_funct_2(sK3,sK0,k1_xboole_0)
    | ~ spl7_2
    | ~ spl7_20 ),
    inference(superposition,[],[f65,f182])).

fof(f65,plain,
    ( v1_funct_2(sK3,sK0,sK1)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f64])).

fof(f359,plain,
    ( spl7_13
    | ~ spl7_29 ),
    inference(avatar_contradiction_clause,[],[f358])).

fof(f358,plain,
    ( $false
    | spl7_13
    | ~ spl7_29 ),
    inference(subsumption_resolution,[],[f351,f52])).

fof(f52,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f351,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl7_13
    | ~ spl7_29 ),
    inference(superposition,[],[f175,f255])).

fof(f255,plain,
    ( k1_xboole_0 = sK3
    | ~ spl7_29 ),
    inference(avatar_component_clause,[],[f254])).

fof(f254,plain,
    ( spl7_29
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_29])])).

fof(f175,plain,
    ( ~ v1_xboole_0(sK3)
    | spl7_13 ),
    inference(avatar_component_clause,[],[f131])).

fof(f131,plain,
    ( spl7_13
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f302,plain,
    ( ~ spl7_9
    | ~ spl7_32
    | ~ spl7_35 ),
    inference(avatar_contradiction_clause,[],[f301])).

fof(f301,plain,
    ( $false
    | ~ spl7_9
    | ~ spl7_32
    | ~ spl7_35 ),
    inference(subsumption_resolution,[],[f300,f282])).

fof(f282,plain,
    ( sK4 = k1_funct_1(sK3,sK6(sK4,sK2,sK3))
    | ~ spl7_32 ),
    inference(avatar_component_clause,[],[f281])).

fof(f281,plain,
    ( spl7_32
  <=> sK4 = k1_funct_1(sK3,sK6(sK4,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_32])])).

fof(f300,plain,
    ( sK4 != k1_funct_1(sK3,sK6(sK4,sK2,sK3))
    | ~ spl7_9
    | ~ spl7_35 ),
    inference(subsumption_resolution,[],[f297,f114])).

fof(f114,plain,
    ( r2_hidden(sK6(sK4,sK2,sK3),sK2)
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl7_9
  <=> r2_hidden(sK6(sK4,sK2,sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f297,plain,
    ( ~ r2_hidden(sK6(sK4,sK2,sK3),sK2)
    | sK4 != k1_funct_1(sK3,sK6(sK4,sK2,sK3))
    | ~ spl7_35 ),
    inference(resolution,[],[f295,f24])).

fof(f24,plain,(
    ! [X5] :
      ( ~ m1_subset_1(X5,sK0)
      | ~ r2_hidden(X5,sK2)
      | sK4 != k1_funct_1(sK3,X5) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f13,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
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
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_funct_2)).

fof(f295,plain,
    ( m1_subset_1(sK6(sK4,sK2,sK3),sK0)
    | ~ spl7_35 ),
    inference(avatar_component_clause,[],[f294])).

fof(f294,plain,
    ( spl7_35
  <=> m1_subset_1(sK6(sK4,sK2,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_35])])).

fof(f296,plain,
    ( spl7_35
    | spl7_27
    | ~ spl7_28 ),
    inference(avatar_split_clause,[],[f272,f244,f227,f294])).

fof(f227,plain,
    ( spl7_27
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).

fof(f244,plain,
    ( spl7_28
  <=> r2_hidden(sK6(sK4,sK2,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).

fof(f272,plain,
    ( m1_subset_1(sK6(sK4,sK2,sK3),sK0)
    | spl7_27
    | ~ spl7_28 ),
    inference(subsumption_resolution,[],[f271,f228])).

fof(f228,plain,
    ( ~ v1_xboole_0(sK0)
    | spl7_27 ),
    inference(avatar_component_clause,[],[f227])).

fof(f271,plain,
    ( v1_xboole_0(sK0)
    | m1_subset_1(sK6(sK4,sK2,sK3),sK0)
    | ~ spl7_28 ),
    inference(resolution,[],[f245,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0)
      | m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f245,plain,
    ( r2_hidden(sK6(sK4,sK2,sK3),sK0)
    | ~ spl7_28 ),
    inference(avatar_component_clause,[],[f244])).

fof(f283,plain,
    ( spl7_32
    | ~ spl7_1
    | ~ spl7_4
    | ~ spl7_18 ),
    inference(avatar_split_clause,[],[f173,f162,f81,f60,f281])).

fof(f60,plain,
    ( spl7_1
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f81,plain,
    ( spl7_4
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f162,plain,
    ( spl7_18
  <=> r2_hidden(k4_tarski(sK6(sK4,sK2,sK3),sK4),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f173,plain,
    ( sK4 = k1_funct_1(sK3,sK6(sK4,sK2,sK3))
    | ~ spl7_1
    | ~ spl7_4
    | ~ spl7_18 ),
    inference(subsumption_resolution,[],[f172,f82])).

fof(f82,plain,
    ( v1_relat_1(sK3)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f81])).

fof(f172,plain,
    ( sK4 = k1_funct_1(sK3,sK6(sK4,sK2,sK3))
    | ~ v1_relat_1(sK3)
    | ~ spl7_1
    | ~ spl7_18 ),
    inference(subsumption_resolution,[],[f167,f61])).

fof(f61,plain,
    ( v1_funct_1(sK3)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f60])).

fof(f167,plain,
    ( ~ v1_funct_1(sK3)
    | sK4 = k1_funct_1(sK3,sK6(sK4,sK2,sK3))
    | ~ v1_relat_1(sK3)
    | ~ spl7_18 ),
    inference(resolution,[],[f163,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | k1_funct_1(X2,X0) = X1
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

fof(f163,plain,
    ( r2_hidden(k4_tarski(sK6(sK4,sK2,sK3),sK4),sK3)
    | ~ spl7_18 ),
    inference(avatar_component_clause,[],[f162])).

fof(f276,plain,
    ( spl7_31
    | ~ spl7_15 ),
    inference(avatar_split_clause,[],[f156,f142,f274])).

fof(f274,plain,
    ( spl7_31
  <=> m1_subset_1(sK6(sK4,sK2,sK3),k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).

fof(f142,plain,
    ( spl7_15
  <=> r2_hidden(sK6(sK4,sK2,sK3),k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f156,plain,
    ( m1_subset_1(sK6(sK4,sK2,sK3),k1_relat_1(sK3))
    | ~ spl7_15 ),
    inference(subsumption_resolution,[],[f153,f152])).

fof(f152,plain,
    ( ~ v1_xboole_0(k1_relat_1(sK3))
    | ~ spl7_15 ),
    inference(resolution,[],[f143,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f143,plain,
    ( r2_hidden(sK6(sK4,sK2,sK3),k1_relat_1(sK3))
    | ~ spl7_15 ),
    inference(avatar_component_clause,[],[f142])).

fof(f153,plain,
    ( v1_xboole_0(k1_relat_1(sK3))
    | m1_subset_1(sK6(sK4,sK2,sK3),k1_relat_1(sK3))
    | ~ spl7_15 ),
    inference(resolution,[],[f143,f34])).

fof(f259,plain,
    ( spl7_29
    | spl7_30
    | ~ spl7_22
    | ~ spl7_24 ),
    inference(avatar_split_clause,[],[f240,f202,f194,f257,f254])).

fof(f240,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK3
    | ~ spl7_22
    | ~ spl7_24 ),
    inference(subsumption_resolution,[],[f232,f195])).

fof(f232,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK3
    | ~ v1_funct_2(sK3,sK0,k1_xboole_0)
    | ~ spl7_24 ),
    inference(resolution,[],[f203,f56])).

fof(f56,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X1
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f203,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl7_24 ),
    inference(avatar_component_clause,[],[f202])).

fof(f246,plain,
    ( spl7_28
    | ~ spl7_15
    | ~ spl7_25 ),
    inference(avatar_split_clause,[],[f222,f206,f142,f244])).

fof(f206,plain,
    ( spl7_25
  <=> sK0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).

fof(f222,plain,
    ( r2_hidden(sK6(sK4,sK2,sK3),sK0)
    | ~ spl7_15
    | ~ spl7_25 ),
    inference(superposition,[],[f143,f207])).

fof(f207,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl7_25 ),
    inference(avatar_component_clause,[],[f206])).

fof(f229,plain,
    ( ~ spl7_27
    | spl7_17
    | ~ spl7_25 ),
    inference(avatar_split_clause,[],[f221,f206,f158,f227])).

fof(f158,plain,
    ( spl7_17
  <=> v1_xboole_0(k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f221,plain,
    ( ~ v1_xboole_0(sK0)
    | spl7_17
    | ~ spl7_25 ),
    inference(superposition,[],[f159,f207])).

fof(f159,plain,
    ( ~ v1_xboole_0(k1_relat_1(sK3))
    | spl7_17 ),
    inference(avatar_component_clause,[],[f158])).

fof(f210,plain,
    ( spl7_25
    | ~ spl7_11
    | ~ spl7_19 ),
    inference(avatar_split_clause,[],[f208,f178,f124,f206])).

fof(f124,plain,
    ( spl7_11
  <=> k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f178,plain,
    ( spl7_19
  <=> sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f208,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl7_11
    | ~ spl7_19 ),
    inference(superposition,[],[f179,f125])).

fof(f125,plain,
    ( k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3)
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f124])).

fof(f179,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl7_19 ),
    inference(avatar_component_clause,[],[f178])).

fof(f183,plain,
    ( spl7_19
    | spl7_20
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f78,f68,f64,f181,f178])).

fof(f78,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f73,f65])).

fof(f73,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ v1_funct_2(sK3,sK0,sK1)
    | ~ spl7_3 ),
    inference(resolution,[],[f69,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f176,plain,
    ( ~ spl7_13
    | ~ spl7_18 ),
    inference(avatar_split_clause,[],[f168,f162,f131])).

fof(f168,plain,
    ( ~ v1_xboole_0(sK3)
    | ~ spl7_18 ),
    inference(resolution,[],[f163,f37])).

fof(f164,plain,
    ( spl7_18
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f99,f90,f81,f162])).

fof(f90,plain,
    ( spl7_6
  <=> r2_hidden(sK4,k9_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f99,plain,
    ( r2_hidden(k4_tarski(sK6(sK4,sK2,sK3),sK4),sK3)
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f94,f82])).

fof(f94,plain,
    ( r2_hidden(k4_tarski(sK6(sK4,sK2,sK3),sK4),sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl7_6 ),
    inference(resolution,[],[f91,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(k4_tarski(sK6(X0,X1,X2),X0),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

fof(f91,plain,
    ( r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f90])).

fof(f160,plain,
    ( ~ spl7_17
    | ~ spl7_15 ),
    inference(avatar_split_clause,[],[f152,f142,f158])).

fof(f144,plain,
    ( spl7_15
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f98,f90,f81,f142])).

fof(f98,plain,
    ( r2_hidden(sK6(sK4,sK2,sK3),k1_relat_1(sK3))
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f93,f82])).

fof(f93,plain,
    ( r2_hidden(sK6(sK4,sK2,sK3),k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ spl7_6 ),
    inference(resolution,[],[f91,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(sK6(X0,X1,X2),k1_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f126,plain,
    ( spl7_11
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f71,f68,f124])).

fof(f71,plain,
    ( k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3)
    | ~ spl7_3 ),
    inference(resolution,[],[f69,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f115,plain,
    ( spl7_9
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f100,f90,f81,f113])).

fof(f100,plain,
    ( r2_hidden(sK6(sK4,sK2,sK3),sK2)
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f95,f82])).

fof(f95,plain,
    ( r2_hidden(sK6(sK4,sK2,sK3),sK2)
    | ~ v1_relat_1(sK3)
    | ~ spl7_6 ),
    inference(resolution,[],[f91,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(sK6(X0,X1,X2),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f92,plain,
    ( spl7_6
    | ~ spl7_3
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f88,f85,f68,f90])).

fof(f85,plain,
    ( spl7_5
  <=> r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f88,plain,
    ( r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | ~ spl7_3
    | ~ spl7_5 ),
    inference(forward_demodulation,[],[f86,f74])).

fof(f74,plain,
    ( ! [X0] : k7_relset_1(sK0,sK1,sK3,X0) = k9_relat_1(sK3,X0)
    | ~ spl7_3 ),
    inference(resolution,[],[f69,f38])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f86,plain,
    ( r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f85])).

fof(f87,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f25,f85])).

fof(f25,plain,(
    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f83,plain,
    ( spl7_4
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f79,f68,f81])).

fof(f79,plain,
    ( v1_relat_1(sK3)
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f75,f40])).

fof(f40,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f75,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK3)
    | ~ spl7_3 ),
    inference(resolution,[],[f69,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f70,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f28,f68])).

fof(f28,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f14])).

fof(f66,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f27,f64])).

fof(f27,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f62,plain,(
    spl7_1 ),
    inference(avatar_split_clause,[],[f26,f60])).

fof(f26,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:42:38 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.40  % (17527)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.19/0.40  % (17527)Refutation not found, incomplete strategy% (17527)------------------------------
% 0.19/0.40  % (17527)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.40  % (17527)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.40  
% 0.19/0.40  % (17527)Memory used [KB]: 1663
% 0.19/0.40  % (17527)Time elapsed: 0.005 s
% 0.19/0.40  % (17527)------------------------------
% 0.19/0.40  % (17527)------------------------------
% 0.19/0.43  % (17528)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.19/0.45  % (17520)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.19/0.47  % (17514)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.19/0.47  % (17515)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.47  % (17524)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.19/0.47  % (17518)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.19/0.47  % (17515)Refutation not found, incomplete strategy% (17515)------------------------------
% 0.19/0.47  % (17515)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.47  % (17515)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.47  
% 0.19/0.47  % (17515)Memory used [KB]: 10618
% 0.19/0.47  % (17515)Time elapsed: 0.075 s
% 0.19/0.47  % (17515)------------------------------
% 0.19/0.47  % (17515)------------------------------
% 0.19/0.48  % (17521)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.19/0.48  % (17517)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.19/0.48  % (17531)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.19/0.48  % (17519)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.19/0.48  % (17522)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.19/0.48  % (17516)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.19/0.49  % (17529)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.19/0.49  % (17532)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.19/0.49  % (17530)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.19/0.49  % (17533)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.19/0.49  % (17514)Refutation found. Thanks to Tanya!
% 0.19/0.49  % SZS status Theorem for theBenchmark
% 0.19/0.49  % SZS output start Proof for theBenchmark
% 0.19/0.49  fof(f456,plain,(
% 0.19/0.49    $false),
% 0.19/0.49    inference(avatar_sat_refutation,[],[f62,f66,f70,f83,f87,f92,f115,f126,f144,f160,f164,f176,f183,f210,f229,f246,f259,f276,f283,f296,f302,f359,f363,f385,f386,f399,f454,f455])).
% 0.19/0.49  fof(f455,plain,(
% 0.19/0.49    k1_xboole_0 != sK1 | k1_xboole_0 != sK0 | k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) | k1_relat_1(sK3) != k1_relset_1(sK0,sK1,sK3) | m1_subset_1(sK6(sK4,sK2,sK3),sK0) | ~m1_subset_1(sK6(sK4,sK2,sK3),k1_relat_1(sK3))),
% 0.19/0.49    introduced(theory_tautology_sat_conflict,[])).
% 0.19/0.49  fof(f454,plain,(
% 0.19/0.49    spl7_47 | ~spl7_39 | ~spl7_41),
% 0.19/0.49    inference(avatar_split_clause,[],[f418,f397,f383,f452])).
% 0.19/0.49  fof(f452,plain,(
% 0.19/0.49    spl7_47 <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)),
% 0.19/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_47])])).
% 0.19/0.49  fof(f383,plain,(
% 0.19/0.49    spl7_39 <=> v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)),
% 0.19/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_39])])).
% 0.19/0.49  fof(f397,plain,(
% 0.19/0.49    spl7_41 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 0.19/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_41])])).
% 0.19/0.49  fof(f418,plain,(
% 0.19/0.49    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) | (~spl7_39 | ~spl7_41)),
% 0.19/0.49    inference(subsumption_resolution,[],[f409,f384])).
% 0.19/0.49  fof(f384,plain,(
% 0.19/0.49    v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | ~spl7_39),
% 0.19/0.49    inference(avatar_component_clause,[],[f383])).
% 0.19/0.49  fof(f409,plain,(
% 0.19/0.49    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) | ~v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | ~spl7_41),
% 0.19/0.49    inference(resolution,[],[f398,f54])).
% 0.19/0.49  fof(f54,plain,(
% 0.19/0.49    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1)) )),
% 0.19/0.49    inference(equality_resolution,[],[f44])).
% 0.19/0.49  fof(f44,plain,(
% 0.19/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f21])).
% 0.19/0.49  fof(f21,plain,(
% 0.19/0.49    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.49    inference(flattening,[],[f20])).
% 0.19/0.49  fof(f20,plain,(
% 0.19/0.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.49    inference(ennf_transformation,[],[f10])).
% 0.19/0.49  fof(f10,axiom,(
% 0.19/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.19/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.19/0.49  fof(f398,plain,(
% 0.19/0.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~spl7_41),
% 0.19/0.49    inference(avatar_component_clause,[],[f397])).
% 0.19/0.49  fof(f399,plain,(
% 0.19/0.49    spl7_41 | ~spl7_3 | ~spl7_20 | ~spl7_30),
% 0.19/0.49    inference(avatar_split_clause,[],[f375,f257,f181,f68,f397])).
% 0.19/0.49  fof(f68,plain,(
% 0.19/0.49    spl7_3 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.19/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.19/0.49  fof(f181,plain,(
% 0.19/0.49    spl7_20 <=> k1_xboole_0 = sK1),
% 0.19/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).
% 0.19/0.49  fof(f257,plain,(
% 0.19/0.49    spl7_30 <=> k1_xboole_0 = sK0),
% 0.19/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).
% 0.19/0.49  fof(f375,plain,(
% 0.19/0.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl7_3 | ~spl7_20 | ~spl7_30)),
% 0.19/0.49    inference(forward_demodulation,[],[f367,f182])).
% 0.19/0.49  fof(f182,plain,(
% 0.19/0.49    k1_xboole_0 = sK1 | ~spl7_20),
% 0.19/0.49    inference(avatar_component_clause,[],[f181])).
% 0.19/0.49  fof(f367,plain,(
% 0.19/0.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) | (~spl7_3 | ~spl7_30)),
% 0.19/0.49    inference(superposition,[],[f69,f258])).
% 0.19/0.49  fof(f258,plain,(
% 0.19/0.49    k1_xboole_0 = sK0 | ~spl7_30),
% 0.19/0.49    inference(avatar_component_clause,[],[f257])).
% 0.19/0.49  fof(f69,plain,(
% 0.19/0.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl7_3),
% 0.19/0.49    inference(avatar_component_clause,[],[f68])).
% 0.19/0.49  fof(f386,plain,(
% 0.19/0.49    spl7_24 | ~spl7_3 | ~spl7_20),
% 0.19/0.49    inference(avatar_split_clause,[],[f326,f181,f68,f202])).
% 0.19/0.49  fof(f202,plain,(
% 0.19/0.49    spl7_24 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))),
% 0.19/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).
% 0.19/0.49  fof(f326,plain,(
% 0.19/0.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | (~spl7_3 | ~spl7_20)),
% 0.19/0.49    inference(superposition,[],[f69,f182])).
% 0.19/0.49  fof(f385,plain,(
% 0.19/0.49    spl7_39 | ~spl7_22 | ~spl7_30),
% 0.19/0.49    inference(avatar_split_clause,[],[f364,f257,f194,f383])).
% 0.19/0.49  fof(f194,plain,(
% 0.19/0.49    spl7_22 <=> v1_funct_2(sK3,sK0,k1_xboole_0)),
% 0.19/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).
% 0.19/0.49  fof(f364,plain,(
% 0.19/0.49    v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | (~spl7_22 | ~spl7_30)),
% 0.19/0.49    inference(forward_demodulation,[],[f195,f258])).
% 0.19/0.49  fof(f195,plain,(
% 0.19/0.49    v1_funct_2(sK3,sK0,k1_xboole_0) | ~spl7_22),
% 0.19/0.49    inference(avatar_component_clause,[],[f194])).
% 0.19/0.49  fof(f363,plain,(
% 0.19/0.49    spl7_22 | ~spl7_2 | ~spl7_20),
% 0.19/0.49    inference(avatar_split_clause,[],[f325,f181,f64,f194])).
% 0.19/0.49  fof(f64,plain,(
% 0.19/0.49    spl7_2 <=> v1_funct_2(sK3,sK0,sK1)),
% 0.19/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.19/0.49  fof(f325,plain,(
% 0.19/0.49    v1_funct_2(sK3,sK0,k1_xboole_0) | (~spl7_2 | ~spl7_20)),
% 0.19/0.49    inference(superposition,[],[f65,f182])).
% 0.19/0.49  fof(f65,plain,(
% 0.19/0.49    v1_funct_2(sK3,sK0,sK1) | ~spl7_2),
% 0.19/0.49    inference(avatar_component_clause,[],[f64])).
% 0.19/0.49  fof(f359,plain,(
% 0.19/0.49    spl7_13 | ~spl7_29),
% 0.19/0.49    inference(avatar_contradiction_clause,[],[f358])).
% 0.19/0.49  fof(f358,plain,(
% 0.19/0.49    $false | (spl7_13 | ~spl7_29)),
% 0.19/0.49    inference(subsumption_resolution,[],[f351,f52])).
% 0.19/0.49  fof(f52,plain,(
% 0.19/0.49    v1_xboole_0(k1_xboole_0)),
% 0.19/0.49    inference(cnf_transformation,[],[f2])).
% 0.19/0.49  fof(f2,axiom,(
% 0.19/0.49    v1_xboole_0(k1_xboole_0)),
% 0.19/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.19/0.49  fof(f351,plain,(
% 0.19/0.49    ~v1_xboole_0(k1_xboole_0) | (spl7_13 | ~spl7_29)),
% 0.19/0.49    inference(superposition,[],[f175,f255])).
% 0.19/0.49  fof(f255,plain,(
% 0.19/0.49    k1_xboole_0 = sK3 | ~spl7_29),
% 0.19/0.49    inference(avatar_component_clause,[],[f254])).
% 0.19/0.49  fof(f254,plain,(
% 0.19/0.49    spl7_29 <=> k1_xboole_0 = sK3),
% 0.19/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_29])])).
% 0.19/0.49  fof(f175,plain,(
% 0.19/0.49    ~v1_xboole_0(sK3) | spl7_13),
% 0.19/0.49    inference(avatar_component_clause,[],[f131])).
% 0.19/0.49  fof(f131,plain,(
% 0.19/0.49    spl7_13 <=> v1_xboole_0(sK3)),
% 0.19/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 0.19/0.49  fof(f302,plain,(
% 0.19/0.49    ~spl7_9 | ~spl7_32 | ~spl7_35),
% 0.19/0.49    inference(avatar_contradiction_clause,[],[f301])).
% 0.19/0.49  fof(f301,plain,(
% 0.19/0.49    $false | (~spl7_9 | ~spl7_32 | ~spl7_35)),
% 0.19/0.49    inference(subsumption_resolution,[],[f300,f282])).
% 0.19/0.49  fof(f282,plain,(
% 0.19/0.49    sK4 = k1_funct_1(sK3,sK6(sK4,sK2,sK3)) | ~spl7_32),
% 0.19/0.49    inference(avatar_component_clause,[],[f281])).
% 0.19/0.49  fof(f281,plain,(
% 0.19/0.49    spl7_32 <=> sK4 = k1_funct_1(sK3,sK6(sK4,sK2,sK3))),
% 0.19/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_32])])).
% 0.19/0.49  fof(f300,plain,(
% 0.19/0.49    sK4 != k1_funct_1(sK3,sK6(sK4,sK2,sK3)) | (~spl7_9 | ~spl7_35)),
% 0.19/0.49    inference(subsumption_resolution,[],[f297,f114])).
% 0.19/0.49  fof(f114,plain,(
% 0.19/0.49    r2_hidden(sK6(sK4,sK2,sK3),sK2) | ~spl7_9),
% 0.19/0.49    inference(avatar_component_clause,[],[f113])).
% 0.19/0.49  fof(f113,plain,(
% 0.19/0.49    spl7_9 <=> r2_hidden(sK6(sK4,sK2,sK3),sK2)),
% 0.19/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.19/0.49  fof(f297,plain,(
% 0.19/0.49    ~r2_hidden(sK6(sK4,sK2,sK3),sK2) | sK4 != k1_funct_1(sK3,sK6(sK4,sK2,sK3)) | ~spl7_35),
% 0.19/0.49    inference(resolution,[],[f295,f24])).
% 0.19/0.49  fof(f24,plain,(
% 0.19/0.49    ( ! [X5] : (~m1_subset_1(X5,sK0) | ~r2_hidden(X5,sK2) | sK4 != k1_funct_1(sK3,X5)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f14])).
% 0.19/0.49  fof(f14,plain,(
% 0.19/0.49    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.19/0.49    inference(flattening,[],[f13])).
% 0.19/0.49  fof(f13,plain,(
% 0.19/0.49    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : ((k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2)) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.19/0.49    inference(ennf_transformation,[],[f12])).
% 0.19/0.49  fof(f12,negated_conjecture,(
% 0.19/0.49    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 0.19/0.49    inference(negated_conjecture,[],[f11])).
% 0.19/0.49  fof(f11,conjecture,(
% 0.19/0.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 0.19/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_funct_2)).
% 0.19/0.49  fof(f295,plain,(
% 0.19/0.49    m1_subset_1(sK6(sK4,sK2,sK3),sK0) | ~spl7_35),
% 0.19/0.49    inference(avatar_component_clause,[],[f294])).
% 0.19/0.49  fof(f294,plain,(
% 0.19/0.49    spl7_35 <=> m1_subset_1(sK6(sK4,sK2,sK3),sK0)),
% 0.19/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_35])])).
% 0.19/0.49  fof(f296,plain,(
% 0.19/0.49    spl7_35 | spl7_27 | ~spl7_28),
% 0.19/0.49    inference(avatar_split_clause,[],[f272,f244,f227,f294])).
% 0.19/0.49  fof(f227,plain,(
% 0.19/0.49    spl7_27 <=> v1_xboole_0(sK0)),
% 0.19/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).
% 0.19/0.49  fof(f244,plain,(
% 0.19/0.49    spl7_28 <=> r2_hidden(sK6(sK4,sK2,sK3),sK0)),
% 0.19/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).
% 0.19/0.49  fof(f272,plain,(
% 0.19/0.49    m1_subset_1(sK6(sK4,sK2,sK3),sK0) | (spl7_27 | ~spl7_28)),
% 0.19/0.49    inference(subsumption_resolution,[],[f271,f228])).
% 0.19/0.49  fof(f228,plain,(
% 0.19/0.49    ~v1_xboole_0(sK0) | spl7_27),
% 0.19/0.49    inference(avatar_component_clause,[],[f227])).
% 0.19/0.49  fof(f271,plain,(
% 0.19/0.49    v1_xboole_0(sK0) | m1_subset_1(sK6(sK4,sK2,sK3),sK0) | ~spl7_28),
% 0.19/0.49    inference(resolution,[],[f245,f34])).
% 0.19/0.49  fof(f34,plain,(
% 0.19/0.49    ( ! [X0,X1] : (~r2_hidden(X1,X0) | v1_xboole_0(X0) | m1_subset_1(X1,X0)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f17])).
% 0.19/0.49  fof(f17,plain,(
% 0.19/0.49    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.19/0.49    inference(ennf_transformation,[],[f3])).
% 0.19/0.49  fof(f3,axiom,(
% 0.19/0.49    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.19/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 0.19/0.49  fof(f245,plain,(
% 0.19/0.49    r2_hidden(sK6(sK4,sK2,sK3),sK0) | ~spl7_28),
% 0.19/0.49    inference(avatar_component_clause,[],[f244])).
% 0.19/0.49  fof(f283,plain,(
% 0.19/0.49    spl7_32 | ~spl7_1 | ~spl7_4 | ~spl7_18),
% 0.19/0.49    inference(avatar_split_clause,[],[f173,f162,f81,f60,f281])).
% 0.19/0.49  fof(f60,plain,(
% 0.19/0.49    spl7_1 <=> v1_funct_1(sK3)),
% 0.19/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.19/0.49  fof(f81,plain,(
% 0.19/0.49    spl7_4 <=> v1_relat_1(sK3)),
% 0.19/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.19/0.49  fof(f162,plain,(
% 0.19/0.49    spl7_18 <=> r2_hidden(k4_tarski(sK6(sK4,sK2,sK3),sK4),sK3)),
% 0.19/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).
% 0.19/0.49  fof(f173,plain,(
% 0.19/0.49    sK4 = k1_funct_1(sK3,sK6(sK4,sK2,sK3)) | (~spl7_1 | ~spl7_4 | ~spl7_18)),
% 0.19/0.49    inference(subsumption_resolution,[],[f172,f82])).
% 0.19/0.49  fof(f82,plain,(
% 0.19/0.49    v1_relat_1(sK3) | ~spl7_4),
% 0.19/0.49    inference(avatar_component_clause,[],[f81])).
% 0.19/0.49  fof(f172,plain,(
% 0.19/0.49    sK4 = k1_funct_1(sK3,sK6(sK4,sK2,sK3)) | ~v1_relat_1(sK3) | (~spl7_1 | ~spl7_18)),
% 0.19/0.49    inference(subsumption_resolution,[],[f167,f61])).
% 0.19/0.49  fof(f61,plain,(
% 0.19/0.49    v1_funct_1(sK3) | ~spl7_1),
% 0.19/0.49    inference(avatar_component_clause,[],[f60])).
% 0.19/0.49  fof(f167,plain,(
% 0.19/0.49    ~v1_funct_1(sK3) | sK4 = k1_funct_1(sK3,sK6(sK4,sK2,sK3)) | ~v1_relat_1(sK3) | ~spl7_18),
% 0.19/0.49    inference(resolution,[],[f163,f30])).
% 0.19/0.49  fof(f30,plain,(
% 0.19/0.49    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | k1_funct_1(X2,X0) = X1 | ~v1_relat_1(X2)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f16])).
% 0.19/0.49  fof(f16,plain,(
% 0.19/0.49    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.19/0.49    inference(flattening,[],[f15])).
% 0.19/0.49  fof(f15,plain,(
% 0.19/0.49    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.19/0.49    inference(ennf_transformation,[],[f7])).
% 0.19/0.49  fof(f7,axiom,(
% 0.19/0.49    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.19/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).
% 0.19/0.49  fof(f163,plain,(
% 0.19/0.49    r2_hidden(k4_tarski(sK6(sK4,sK2,sK3),sK4),sK3) | ~spl7_18),
% 0.19/0.49    inference(avatar_component_clause,[],[f162])).
% 0.19/0.49  fof(f276,plain,(
% 0.19/0.49    spl7_31 | ~spl7_15),
% 0.19/0.49    inference(avatar_split_clause,[],[f156,f142,f274])).
% 0.19/0.49  fof(f274,plain,(
% 0.19/0.49    spl7_31 <=> m1_subset_1(sK6(sK4,sK2,sK3),k1_relat_1(sK3))),
% 0.19/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).
% 0.19/0.49  fof(f142,plain,(
% 0.19/0.49    spl7_15 <=> r2_hidden(sK6(sK4,sK2,sK3),k1_relat_1(sK3))),
% 0.19/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 0.19/0.49  fof(f156,plain,(
% 0.19/0.49    m1_subset_1(sK6(sK4,sK2,sK3),k1_relat_1(sK3)) | ~spl7_15),
% 0.19/0.49    inference(subsumption_resolution,[],[f153,f152])).
% 0.19/0.49  fof(f152,plain,(
% 0.19/0.49    ~v1_xboole_0(k1_relat_1(sK3)) | ~spl7_15),
% 0.19/0.49    inference(resolution,[],[f143,f37])).
% 0.19/0.49  fof(f37,plain,(
% 0.19/0.49    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f1])).
% 0.19/0.49  fof(f1,axiom,(
% 0.19/0.49    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.19/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.19/0.49  fof(f143,plain,(
% 0.19/0.49    r2_hidden(sK6(sK4,sK2,sK3),k1_relat_1(sK3)) | ~spl7_15),
% 0.19/0.49    inference(avatar_component_clause,[],[f142])).
% 0.19/0.49  fof(f153,plain,(
% 0.19/0.49    v1_xboole_0(k1_relat_1(sK3)) | m1_subset_1(sK6(sK4,sK2,sK3),k1_relat_1(sK3)) | ~spl7_15),
% 0.19/0.49    inference(resolution,[],[f143,f34])).
% 0.19/0.49  fof(f259,plain,(
% 0.19/0.49    spl7_29 | spl7_30 | ~spl7_22 | ~spl7_24),
% 0.19/0.49    inference(avatar_split_clause,[],[f240,f202,f194,f257,f254])).
% 0.19/0.49  fof(f240,plain,(
% 0.19/0.49    k1_xboole_0 = sK0 | k1_xboole_0 = sK3 | (~spl7_22 | ~spl7_24)),
% 0.19/0.49    inference(subsumption_resolution,[],[f232,f195])).
% 0.19/0.49  fof(f232,plain,(
% 0.19/0.49    k1_xboole_0 = sK0 | k1_xboole_0 = sK3 | ~v1_funct_2(sK3,sK0,k1_xboole_0) | ~spl7_24),
% 0.19/0.49    inference(resolution,[],[f203,f56])).
% 0.19/0.49  fof(f56,plain,(
% 0.19/0.49    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | k1_xboole_0 = X0 | k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0)) )),
% 0.19/0.49    inference(equality_resolution,[],[f42])).
% 0.19/0.49  fof(f42,plain,(
% 0.19/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X1 | k1_xboole_0 = X0 | k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f21])).
% 0.19/0.49  fof(f203,plain,(
% 0.19/0.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | ~spl7_24),
% 0.19/0.49    inference(avatar_component_clause,[],[f202])).
% 0.19/0.49  fof(f246,plain,(
% 0.19/0.49    spl7_28 | ~spl7_15 | ~spl7_25),
% 0.19/0.49    inference(avatar_split_clause,[],[f222,f206,f142,f244])).
% 0.19/0.49  fof(f206,plain,(
% 0.19/0.49    spl7_25 <=> sK0 = k1_relat_1(sK3)),
% 0.19/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).
% 0.19/0.49  fof(f222,plain,(
% 0.19/0.49    r2_hidden(sK6(sK4,sK2,sK3),sK0) | (~spl7_15 | ~spl7_25)),
% 0.19/0.49    inference(superposition,[],[f143,f207])).
% 0.19/0.49  fof(f207,plain,(
% 0.19/0.49    sK0 = k1_relat_1(sK3) | ~spl7_25),
% 0.19/0.49    inference(avatar_component_clause,[],[f206])).
% 0.19/0.49  fof(f229,plain,(
% 0.19/0.49    ~spl7_27 | spl7_17 | ~spl7_25),
% 0.19/0.49    inference(avatar_split_clause,[],[f221,f206,f158,f227])).
% 0.19/0.49  fof(f158,plain,(
% 0.19/0.49    spl7_17 <=> v1_xboole_0(k1_relat_1(sK3))),
% 0.19/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).
% 0.19/0.49  fof(f221,plain,(
% 0.19/0.49    ~v1_xboole_0(sK0) | (spl7_17 | ~spl7_25)),
% 0.19/0.49    inference(superposition,[],[f159,f207])).
% 0.19/0.49  fof(f159,plain,(
% 0.19/0.49    ~v1_xboole_0(k1_relat_1(sK3)) | spl7_17),
% 0.19/0.49    inference(avatar_component_clause,[],[f158])).
% 0.19/0.49  fof(f210,plain,(
% 0.19/0.49    spl7_25 | ~spl7_11 | ~spl7_19),
% 0.19/0.49    inference(avatar_split_clause,[],[f208,f178,f124,f206])).
% 0.19/0.49  fof(f124,plain,(
% 0.19/0.49    spl7_11 <=> k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3)),
% 0.19/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 0.19/0.49  fof(f178,plain,(
% 0.19/0.49    spl7_19 <=> sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.19/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).
% 0.19/0.49  fof(f208,plain,(
% 0.19/0.49    sK0 = k1_relat_1(sK3) | (~spl7_11 | ~spl7_19)),
% 0.19/0.49    inference(superposition,[],[f179,f125])).
% 0.19/0.49  fof(f125,plain,(
% 0.19/0.49    k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3) | ~spl7_11),
% 0.19/0.49    inference(avatar_component_clause,[],[f124])).
% 0.19/0.49  fof(f179,plain,(
% 0.19/0.49    sK0 = k1_relset_1(sK0,sK1,sK3) | ~spl7_19),
% 0.19/0.49    inference(avatar_component_clause,[],[f178])).
% 0.19/0.49  fof(f183,plain,(
% 0.19/0.49    spl7_19 | spl7_20 | ~spl7_2 | ~spl7_3),
% 0.19/0.49    inference(avatar_split_clause,[],[f78,f68,f64,f181,f178])).
% 0.19/0.49  fof(f78,plain,(
% 0.19/0.49    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3) | (~spl7_2 | ~spl7_3)),
% 0.19/0.49    inference(subsumption_resolution,[],[f73,f65])).
% 0.19/0.49  fof(f73,plain,(
% 0.19/0.49    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3) | ~v1_funct_2(sK3,sK0,sK1) | ~spl7_3),
% 0.19/0.49    inference(resolution,[],[f69,f46])).
% 0.19/0.49  fof(f46,plain,(
% 0.19/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f21])).
% 0.19/0.49  fof(f176,plain,(
% 0.19/0.49    ~spl7_13 | ~spl7_18),
% 0.19/0.49    inference(avatar_split_clause,[],[f168,f162,f131])).
% 0.19/0.49  fof(f168,plain,(
% 0.19/0.49    ~v1_xboole_0(sK3) | ~spl7_18),
% 0.19/0.49    inference(resolution,[],[f163,f37])).
% 0.19/0.49  fof(f164,plain,(
% 0.19/0.49    spl7_18 | ~spl7_4 | ~spl7_6),
% 0.19/0.49    inference(avatar_split_clause,[],[f99,f90,f81,f162])).
% 0.19/0.49  fof(f90,plain,(
% 0.19/0.49    spl7_6 <=> r2_hidden(sK4,k9_relat_1(sK3,sK2))),
% 0.19/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.19/0.49  fof(f99,plain,(
% 0.19/0.49    r2_hidden(k4_tarski(sK6(sK4,sK2,sK3),sK4),sK3) | (~spl7_4 | ~spl7_6)),
% 0.19/0.49    inference(subsumption_resolution,[],[f94,f82])).
% 0.19/0.49  fof(f94,plain,(
% 0.19/0.49    r2_hidden(k4_tarski(sK6(sK4,sK2,sK3),sK4),sK3) | ~v1_relat_1(sK3) | ~spl7_6),
% 0.19/0.49    inference(resolution,[],[f91,f49])).
% 0.19/0.49  fof(f49,plain,(
% 0.19/0.49    ( ! [X2,X0,X1] : (~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(k4_tarski(sK6(X0,X1,X2),X0),X2) | ~v1_relat_1(X2)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f23])).
% 0.19/0.49  fof(f23,plain,(
% 0.19/0.49    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.19/0.49    inference(ennf_transformation,[],[f6])).
% 0.19/0.49  fof(f6,axiom,(
% 0.19/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 0.19/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).
% 0.19/0.49  fof(f91,plain,(
% 0.19/0.49    r2_hidden(sK4,k9_relat_1(sK3,sK2)) | ~spl7_6),
% 0.19/0.49    inference(avatar_component_clause,[],[f90])).
% 0.19/0.49  fof(f160,plain,(
% 0.19/0.49    ~spl7_17 | ~spl7_15),
% 0.19/0.49    inference(avatar_split_clause,[],[f152,f142,f158])).
% 0.19/0.49  fof(f144,plain,(
% 0.19/0.49    spl7_15 | ~spl7_4 | ~spl7_6),
% 0.19/0.49    inference(avatar_split_clause,[],[f98,f90,f81,f142])).
% 0.19/0.49  fof(f98,plain,(
% 0.19/0.49    r2_hidden(sK6(sK4,sK2,sK3),k1_relat_1(sK3)) | (~spl7_4 | ~spl7_6)),
% 0.19/0.49    inference(subsumption_resolution,[],[f93,f82])).
% 0.19/0.49  fof(f93,plain,(
% 0.19/0.49    r2_hidden(sK6(sK4,sK2,sK3),k1_relat_1(sK3)) | ~v1_relat_1(sK3) | ~spl7_6),
% 0.19/0.49    inference(resolution,[],[f91,f48])).
% 0.19/0.49  fof(f48,plain,(
% 0.19/0.49    ( ! [X2,X0,X1] : (~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(sK6(X0,X1,X2),k1_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f23])).
% 0.19/0.49  fof(f126,plain,(
% 0.19/0.49    spl7_11 | ~spl7_3),
% 0.19/0.49    inference(avatar_split_clause,[],[f71,f68,f124])).
% 0.19/0.49  fof(f71,plain,(
% 0.19/0.49    k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3) | ~spl7_3),
% 0.19/0.49    inference(resolution,[],[f69,f47])).
% 0.19/0.49  fof(f47,plain,(
% 0.19/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relat_1(X2) = k1_relset_1(X0,X1,X2)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f22])).
% 0.19/0.49  fof(f22,plain,(
% 0.19/0.49    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.49    inference(ennf_transformation,[],[f8])).
% 0.19/0.49  fof(f8,axiom,(
% 0.19/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 0.19/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.19/0.49  fof(f115,plain,(
% 0.19/0.49    spl7_9 | ~spl7_4 | ~spl7_6),
% 0.19/0.49    inference(avatar_split_clause,[],[f100,f90,f81,f113])).
% 0.19/0.49  fof(f100,plain,(
% 0.19/0.49    r2_hidden(sK6(sK4,sK2,sK3),sK2) | (~spl7_4 | ~spl7_6)),
% 0.19/0.49    inference(subsumption_resolution,[],[f95,f82])).
% 0.19/0.49  fof(f95,plain,(
% 0.19/0.49    r2_hidden(sK6(sK4,sK2,sK3),sK2) | ~v1_relat_1(sK3) | ~spl7_6),
% 0.19/0.49    inference(resolution,[],[f91,f50])).
% 0.19/0.49  fof(f50,plain,(
% 0.19/0.49    ( ! [X2,X0,X1] : (~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(sK6(X0,X1,X2),X1) | ~v1_relat_1(X2)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f23])).
% 0.19/0.49  fof(f92,plain,(
% 0.19/0.49    spl7_6 | ~spl7_3 | ~spl7_5),
% 0.19/0.49    inference(avatar_split_clause,[],[f88,f85,f68,f90])).
% 0.19/0.49  fof(f85,plain,(
% 0.19/0.49    spl7_5 <=> r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))),
% 0.19/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.19/0.49  fof(f88,plain,(
% 0.19/0.49    r2_hidden(sK4,k9_relat_1(sK3,sK2)) | (~spl7_3 | ~spl7_5)),
% 0.19/0.49    inference(forward_demodulation,[],[f86,f74])).
% 0.19/0.49  fof(f74,plain,(
% 0.19/0.49    ( ! [X0] : (k7_relset_1(sK0,sK1,sK3,X0) = k9_relat_1(sK3,X0)) ) | ~spl7_3),
% 0.19/0.49    inference(resolution,[],[f69,f38])).
% 0.19/0.49  fof(f38,plain,(
% 0.19/0.49    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f18])).
% 0.19/0.49  fof(f18,plain,(
% 0.19/0.49    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.49    inference(ennf_transformation,[],[f9])).
% 0.19/0.49  fof(f9,axiom,(
% 0.19/0.49    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.19/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.19/0.49  fof(f86,plain,(
% 0.19/0.49    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) | ~spl7_5),
% 0.19/0.49    inference(avatar_component_clause,[],[f85])).
% 0.19/0.49  fof(f87,plain,(
% 0.19/0.49    spl7_5),
% 0.19/0.49    inference(avatar_split_clause,[],[f25,f85])).
% 0.19/0.49  fof(f25,plain,(
% 0.19/0.49    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))),
% 0.19/0.49    inference(cnf_transformation,[],[f14])).
% 0.19/0.49  fof(f83,plain,(
% 0.19/0.49    spl7_4 | ~spl7_3),
% 0.19/0.49    inference(avatar_split_clause,[],[f79,f68,f81])).
% 0.19/0.49  fof(f79,plain,(
% 0.19/0.49    v1_relat_1(sK3) | ~spl7_3),
% 0.19/0.49    inference(subsumption_resolution,[],[f75,f40])).
% 0.19/0.49  fof(f40,plain,(
% 0.19/0.49    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.19/0.49    inference(cnf_transformation,[],[f5])).
% 0.19/0.49  fof(f5,axiom,(
% 0.19/0.49    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.19/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.19/0.49  fof(f75,plain,(
% 0.19/0.49    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | v1_relat_1(sK3) | ~spl7_3),
% 0.19/0.49    inference(resolution,[],[f69,f39])).
% 0.19/0.49  fof(f39,plain,(
% 0.19/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f19])).
% 0.19/0.49  fof(f19,plain,(
% 0.19/0.49    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.19/0.49    inference(ennf_transformation,[],[f4])).
% 0.19/0.49  fof(f4,axiom,(
% 0.19/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.19/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.19/0.49  fof(f70,plain,(
% 0.19/0.49    spl7_3),
% 0.19/0.49    inference(avatar_split_clause,[],[f28,f68])).
% 0.19/0.49  fof(f28,plain,(
% 0.19/0.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.19/0.49    inference(cnf_transformation,[],[f14])).
% 0.19/0.49  fof(f66,plain,(
% 0.19/0.49    spl7_2),
% 0.19/0.49    inference(avatar_split_clause,[],[f27,f64])).
% 0.19/0.49  fof(f27,plain,(
% 0.19/0.49    v1_funct_2(sK3,sK0,sK1)),
% 0.19/0.49    inference(cnf_transformation,[],[f14])).
% 0.19/0.49  fof(f62,plain,(
% 0.19/0.49    spl7_1),
% 0.19/0.49    inference(avatar_split_clause,[],[f26,f60])).
% 0.19/0.49  fof(f26,plain,(
% 0.19/0.49    v1_funct_1(sK3)),
% 0.19/0.49    inference(cnf_transformation,[],[f14])).
% 0.19/0.49  % SZS output end Proof for theBenchmark
% 0.19/0.49  % (17514)------------------------------
% 0.19/0.49  % (17514)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.49  % (17514)Termination reason: Refutation
% 0.19/0.49  
% 0.19/0.49  % (17514)Memory used [KB]: 6396
% 0.19/0.49  % (17514)Time elapsed: 0.076 s
% 0.19/0.49  % (17514)------------------------------
% 0.19/0.49  % (17514)------------------------------
% 0.19/0.49  % (17513)Success in time 0.151 s
%------------------------------------------------------------------------------
