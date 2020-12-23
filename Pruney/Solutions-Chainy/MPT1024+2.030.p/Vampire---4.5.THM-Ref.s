%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:16 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 253 expanded)
%              Number of leaves         :   33 ( 113 expanded)
%              Depth                    :    9
%              Number of atoms          :  400 ( 768 expanded)
%              Number of equality atoms :   78 ( 157 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f380,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f60,f64,f68,f80,f84,f89,f113,f126,f144,f164,f177,f184,f204,f212,f216,f217,f243,f276,f303,f326,f373,f378,f379])).

fof(f379,plain,
    ( k1_xboole_0 != k1_relat_1(sK3)
    | k1_xboole_0 != sK0
    | r2_hidden(sK6(sK4,sK2,sK3),sK0)
    | ~ r2_hidden(sK6(sK4,sK2,sK3),k1_relat_1(sK3)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f378,plain,
    ( spl7_45
    | ~ spl7_33
    | ~ spl7_34
    | ~ spl7_39 ),
    inference(avatar_split_clause,[],[f374,f324,f301,f278,f376])).

fof(f376,plain,
    ( spl7_45
  <=> k1_xboole_0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_45])])).

fof(f278,plain,
    ( spl7_33
  <=> k1_relat_1(sK3) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_33])])).

fof(f301,plain,
    ( spl7_34
  <=> v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).

fof(f324,plain,
    ( spl7_39
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_39])])).

fof(f374,plain,
    ( k1_xboole_0 = k1_relat_1(sK3)
    | ~ spl7_33
    | ~ spl7_34
    | ~ spl7_39 ),
    inference(forward_demodulation,[],[f279,f364])).

fof(f364,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | ~ spl7_34
    | ~ spl7_39 ),
    inference(subsumption_resolution,[],[f355,f302])).

fof(f302,plain,
    ( v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | ~ spl7_34 ),
    inference(avatar_component_clause,[],[f301])).

fof(f355,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | ~ v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | ~ spl7_39 ),
    inference(resolution,[],[f325,f52])).

fof(f52,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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

fof(f325,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl7_39 ),
    inference(avatar_component_clause,[],[f324])).

fof(f279,plain,
    ( k1_relat_1(sK3) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | ~ spl7_33 ),
    inference(avatar_component_clause,[],[f278])).

fof(f373,plain,
    ( spl7_33
    | ~ spl7_11
    | ~ spl7_20
    | ~ spl7_31 ),
    inference(avatar_split_clause,[],[f295,f241,f182,f124,f278])).

fof(f124,plain,
    ( spl7_11
  <=> k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f182,plain,
    ( spl7_20
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f241,plain,
    ( spl7_31
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).

fof(f295,plain,
    ( k1_relat_1(sK3) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | ~ spl7_11
    | ~ spl7_20
    | ~ spl7_31 ),
    inference(forward_demodulation,[],[f283,f183])).

fof(f183,plain,
    ( k1_xboole_0 = sK1
    | ~ spl7_20 ),
    inference(avatar_component_clause,[],[f182])).

fof(f283,plain,
    ( k1_relat_1(sK3) = k1_relset_1(k1_xboole_0,sK1,sK3)
    | ~ spl7_11
    | ~ spl7_31 ),
    inference(superposition,[],[f125,f242])).

fof(f242,plain,
    ( k1_xboole_0 = sK0
    | ~ spl7_31 ),
    inference(avatar_component_clause,[],[f241])).

fof(f125,plain,
    ( k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3)
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f124])).

fof(f326,plain,
    ( spl7_39
    | ~ spl7_3
    | ~ spl7_20
    | ~ spl7_31 ),
    inference(avatar_split_clause,[],[f293,f241,f182,f66,f324])).

fof(f66,plain,
    ( spl7_3
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f293,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl7_3
    | ~ spl7_20
    | ~ spl7_31 ),
    inference(forward_demodulation,[],[f281,f183])).

fof(f281,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ spl7_3
    | ~ spl7_31 ),
    inference(superposition,[],[f67,f242])).

fof(f67,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f66])).

fof(f303,plain,
    ( spl7_34
    | ~ spl7_2
    | ~ spl7_20
    | ~ spl7_31 ),
    inference(avatar_split_clause,[],[f292,f241,f182,f62,f301])).

fof(f62,plain,
    ( spl7_2
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f292,plain,
    ( v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | ~ spl7_2
    | ~ spl7_20
    | ~ spl7_31 ),
    inference(forward_demodulation,[],[f280,f183])).

fof(f280,plain,
    ( v1_funct_2(sK3,k1_xboole_0,sK1)
    | ~ spl7_2
    | ~ spl7_31 ),
    inference(superposition,[],[f63,f242])).

fof(f63,plain,
    ( v1_funct_2(sK3,sK0,sK1)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f62])).

fof(f276,plain,
    ( spl7_13
    | ~ spl7_30 ),
    inference(avatar_contradiction_clause,[],[f275])).

fof(f275,plain,
    ( $false
    | spl7_13
    | ~ spl7_30 ),
    inference(subsumption_resolution,[],[f264,f50])).

fof(f50,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f264,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl7_13
    | ~ spl7_30 ),
    inference(superposition,[],[f176,f239])).

fof(f239,plain,
    ( k1_xboole_0 = sK3
    | ~ spl7_30 ),
    inference(avatar_component_clause,[],[f238])).

fof(f238,plain,
    ( spl7_30
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).

fof(f176,plain,
    ( ~ v1_xboole_0(sK3)
    | spl7_13 ),
    inference(avatar_component_clause,[],[f131])).

fof(f131,plain,
    ( spl7_13
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f243,plain,
    ( spl7_30
    | spl7_31
    | ~ spl7_24
    | ~ spl7_27 ),
    inference(avatar_split_clause,[],[f230,f214,f202,f241,f238])).

fof(f202,plain,
    ( spl7_24
  <=> v1_funct_2(sK3,sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).

fof(f214,plain,
    ( spl7_27
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).

fof(f230,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK3
    | ~ spl7_24
    | ~ spl7_27 ),
    inference(subsumption_resolution,[],[f222,f203])).

fof(f203,plain,
    ( v1_funct_2(sK3,sK0,k1_xboole_0)
    | ~ spl7_24 ),
    inference(avatar_component_clause,[],[f202])).

fof(f222,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK3
    | ~ v1_funct_2(sK3,sK0,k1_xboole_0)
    | ~ spl7_27 ),
    inference(resolution,[],[f215,f54])).

fof(f54,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X1
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f215,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl7_27 ),
    inference(avatar_component_clause,[],[f214])).

fof(f217,plain,
    ( sK0 != k1_relset_1(sK0,sK1,sK3)
    | k1_relat_1(sK3) != k1_relset_1(sK0,sK1,sK3)
    | r2_hidden(sK6(sK4,sK2,sK3),sK0)
    | ~ r2_hidden(sK6(sK4,sK2,sK3),k1_relat_1(sK3)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f216,plain,
    ( spl7_27
    | ~ spl7_3
    | ~ spl7_20 ),
    inference(avatar_split_clause,[],[f189,f182,f66,f214])).

fof(f189,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl7_3
    | ~ spl7_20 ),
    inference(superposition,[],[f67,f183])).

fof(f212,plain,
    ( ~ spl7_26
    | ~ spl7_1
    | ~ spl7_4
    | ~ spl7_9
    | ~ spl7_18 ),
    inference(avatar_split_clause,[],[f174,f162,f111,f78,f58,f210])).

fof(f210,plain,
    ( spl7_26
  <=> r2_hidden(sK6(sK4,sK2,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).

fof(f58,plain,
    ( spl7_1
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f78,plain,
    ( spl7_4
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f111,plain,
    ( spl7_9
  <=> r2_hidden(sK6(sK4,sK2,sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f162,plain,
    ( spl7_18
  <=> r2_hidden(k4_tarski(sK6(sK4,sK2,sK3),sK4),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f174,plain,
    ( ~ r2_hidden(sK6(sK4,sK2,sK3),sK0)
    | ~ spl7_1
    | ~ spl7_4
    | ~ spl7_9
    | ~ spl7_18 ),
    inference(subsumption_resolution,[],[f114,f173])).

fof(f173,plain,
    ( sK4 = k1_funct_1(sK3,sK6(sK4,sK2,sK3))
    | ~ spl7_1
    | ~ spl7_4
    | ~ spl7_18 ),
    inference(subsumption_resolution,[],[f172,f79])).

fof(f79,plain,
    ( v1_relat_1(sK3)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f78])).

fof(f172,plain,
    ( sK4 = k1_funct_1(sK3,sK6(sK4,sK2,sK3))
    | ~ v1_relat_1(sK3)
    | ~ spl7_1
    | ~ spl7_18 ),
    inference(subsumption_resolution,[],[f167,f59])).

fof(f59,plain,
    ( v1_funct_1(sK3)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f58])).

fof(f167,plain,
    ( ~ v1_funct_1(sK3)
    | sK4 = k1_funct_1(sK3,sK6(sK4,sK2,sK3))
    | ~ v1_relat_1(sK3)
    | ~ spl7_18 ),
    inference(resolution,[],[f163,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | k1_funct_1(X2,X0) = X1
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
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

fof(f163,plain,
    ( r2_hidden(k4_tarski(sK6(sK4,sK2,sK3),sK4),sK3)
    | ~ spl7_18 ),
    inference(avatar_component_clause,[],[f162])).

fof(f114,plain,
    ( ~ r2_hidden(sK6(sK4,sK2,sK3),sK0)
    | sK4 != k1_funct_1(sK3,sK6(sK4,sK2,sK3))
    | ~ spl7_9 ),
    inference(resolution,[],[f112,f23])).

fof(f23,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,sK2)
      | ~ r2_hidden(X5,sK0)
      | sK4 != k1_funct_1(sK3,X5) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ r2_hidden(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ r2_hidden(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ! [X4] :
            ~ ( ! [X5] :
                  ~ ( k1_funct_1(X3,X5) = X4
                    & r2_hidden(X5,X2)
                    & r2_hidden(X5,X0) )
              & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ~ ( ! [X5] :
                ~ ( k1_funct_1(X3,X5) = X4
                  & r2_hidden(X5,X2)
                  & r2_hidden(X5,X0) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t115_funct_2)).

fof(f112,plain,
    ( r2_hidden(sK6(sK4,sK2,sK3),sK2)
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f111])).

fof(f204,plain,
    ( spl7_24
    | ~ spl7_2
    | ~ spl7_20 ),
    inference(avatar_split_clause,[],[f188,f182,f62,f202])).

fof(f188,plain,
    ( v1_funct_2(sK3,sK0,k1_xboole_0)
    | ~ spl7_2
    | ~ spl7_20 ),
    inference(superposition,[],[f63,f183])).

fof(f184,plain,
    ( spl7_19
    | spl7_20
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f76,f66,f62,f182,f179])).

fof(f179,plain,
    ( spl7_19
  <=> sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f76,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f71,f63])).

fof(f71,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ v1_funct_2(sK3,sK0,sK1)
    | ~ spl7_3 ),
    inference(resolution,[],[f67,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f177,plain,
    ( ~ spl7_13
    | ~ spl7_18 ),
    inference(avatar_split_clause,[],[f168,f162,f131])).

fof(f168,plain,
    ( ~ v1_xboole_0(sK3)
    | ~ spl7_18 ),
    inference(resolution,[],[f163,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f164,plain,
    ( spl7_18
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f96,f87,f78,f162])).

fof(f87,plain,
    ( spl7_6
  <=> r2_hidden(sK4,k9_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f96,plain,
    ( r2_hidden(k4_tarski(sK6(sK4,sK2,sK3),sK4),sK3)
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f91,f79])).

fof(f91,plain,
    ( r2_hidden(k4_tarski(sK6(sK4,sK2,sK3),sK4),sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl7_6 ),
    inference(resolution,[],[f88,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(k4_tarski(sK6(X0,X1,X2),X0),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

fof(f88,plain,
    ( r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f87])).

fof(f144,plain,
    ( spl7_15
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f95,f87,f78,f142])).

fof(f142,plain,
    ( spl7_15
  <=> r2_hidden(sK6(sK4,sK2,sK3),k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f95,plain,
    ( r2_hidden(sK6(sK4,sK2,sK3),k1_relat_1(sK3))
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f90,f79])).

fof(f90,plain,
    ( r2_hidden(sK6(sK4,sK2,sK3),k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ spl7_6 ),
    inference(resolution,[],[f88,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(sK6(X0,X1,X2),k1_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f126,plain,
    ( spl7_11
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f69,f66,f124])).

fof(f69,plain,
    ( k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3)
    | ~ spl7_3 ),
    inference(resolution,[],[f67,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f113,plain,
    ( spl7_9
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f97,f87,f78,f111])).

fof(f97,plain,
    ( r2_hidden(sK6(sK4,sK2,sK3),sK2)
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f92,f79])).

fof(f92,plain,
    ( r2_hidden(sK6(sK4,sK2,sK3),sK2)
    | ~ v1_relat_1(sK3)
    | ~ spl7_6 ),
    inference(resolution,[],[f88,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(sK6(X0,X1,X2),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f89,plain,
    ( spl7_6
    | ~ spl7_3
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f85,f82,f66,f87])).

fof(f82,plain,
    ( spl7_5
  <=> r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f85,plain,
    ( r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | ~ spl7_3
    | ~ spl7_5 ),
    inference(forward_demodulation,[],[f83,f73])).

fof(f73,plain,
    ( ! [X0] : k7_relset_1(sK0,sK1,sK3,X0) = k9_relat_1(sK3,X0)
    | ~ spl7_3 ),
    inference(resolution,[],[f67,f37])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f83,plain,
    ( r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f82])).

fof(f84,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f24,f82])).

fof(f24,plain,(
    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f13])).

fof(f80,plain,
    ( spl7_4
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f72,f66,f78])).

fof(f72,plain,
    ( v1_relat_1(sK3)
    | ~ spl7_3 ),
    inference(resolution,[],[f67,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
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

fof(f68,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f27,f66])).

fof(f27,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f13])).

fof(f64,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f26,f62])).

fof(f26,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f60,plain,(
    spl7_1 ),
    inference(avatar_split_clause,[],[f25,f58])).

fof(f25,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:57:08 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (30166)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.51  % (30164)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (30174)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.51  % (30172)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.52  % (30164)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.53  % (30181)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.53  % (30170)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.53  % (30173)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f380,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(avatar_sat_refutation,[],[f60,f64,f68,f80,f84,f89,f113,f126,f144,f164,f177,f184,f204,f212,f216,f217,f243,f276,f303,f326,f373,f378,f379])).
% 0.21/0.53  fof(f379,plain,(
% 0.21/0.53    k1_xboole_0 != k1_relat_1(sK3) | k1_xboole_0 != sK0 | r2_hidden(sK6(sK4,sK2,sK3),sK0) | ~r2_hidden(sK6(sK4,sK2,sK3),k1_relat_1(sK3))),
% 0.21/0.53    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.53  fof(f378,plain,(
% 0.21/0.53    spl7_45 | ~spl7_33 | ~spl7_34 | ~spl7_39),
% 0.21/0.53    inference(avatar_split_clause,[],[f374,f324,f301,f278,f376])).
% 0.21/0.53  fof(f376,plain,(
% 0.21/0.53    spl7_45 <=> k1_xboole_0 = k1_relat_1(sK3)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_45])])).
% 0.21/0.53  fof(f278,plain,(
% 0.21/0.53    spl7_33 <=> k1_relat_1(sK3) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_33])])).
% 0.21/0.53  fof(f301,plain,(
% 0.21/0.53    spl7_34 <=> v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).
% 0.21/0.53  fof(f324,plain,(
% 0.21/0.53    spl7_39 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_39])])).
% 0.21/0.53  fof(f374,plain,(
% 0.21/0.53    k1_xboole_0 = k1_relat_1(sK3) | (~spl7_33 | ~spl7_34 | ~spl7_39)),
% 0.21/0.53    inference(forward_demodulation,[],[f279,f364])).
% 0.21/0.53  fof(f364,plain,(
% 0.21/0.53    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) | (~spl7_34 | ~spl7_39)),
% 0.21/0.53    inference(subsumption_resolution,[],[f355,f302])).
% 0.21/0.53  fof(f302,plain,(
% 0.21/0.53    v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | ~spl7_34),
% 0.21/0.53    inference(avatar_component_clause,[],[f301])).
% 0.21/0.53  fof(f355,plain,(
% 0.21/0.53    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) | ~v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | ~spl7_39),
% 0.21/0.53    inference(resolution,[],[f325,f52])).
% 0.21/0.53  fof(f52,plain,(
% 0.21/0.53    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1)) )),
% 0.21/0.53    inference(equality_resolution,[],[f42])).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f20])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.53    inference(flattening,[],[f19])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.53    inference(ennf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.53  fof(f325,plain,(
% 0.21/0.53    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~spl7_39),
% 0.21/0.53    inference(avatar_component_clause,[],[f324])).
% 0.21/0.53  fof(f279,plain,(
% 0.21/0.53    k1_relat_1(sK3) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) | ~spl7_33),
% 0.21/0.53    inference(avatar_component_clause,[],[f278])).
% 0.21/0.53  fof(f373,plain,(
% 0.21/0.53    spl7_33 | ~spl7_11 | ~spl7_20 | ~spl7_31),
% 0.21/0.53    inference(avatar_split_clause,[],[f295,f241,f182,f124,f278])).
% 0.21/0.53  fof(f124,plain,(
% 0.21/0.53    spl7_11 <=> k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 0.21/0.53  fof(f182,plain,(
% 0.21/0.53    spl7_20 <=> k1_xboole_0 = sK1),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).
% 0.21/0.53  fof(f241,plain,(
% 0.21/0.53    spl7_31 <=> k1_xboole_0 = sK0),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).
% 0.21/0.53  fof(f295,plain,(
% 0.21/0.53    k1_relat_1(sK3) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) | (~spl7_11 | ~spl7_20 | ~spl7_31)),
% 0.21/0.53    inference(forward_demodulation,[],[f283,f183])).
% 0.21/0.53  fof(f183,plain,(
% 0.21/0.53    k1_xboole_0 = sK1 | ~spl7_20),
% 0.21/0.53    inference(avatar_component_clause,[],[f182])).
% 0.21/0.53  fof(f283,plain,(
% 0.21/0.53    k1_relat_1(sK3) = k1_relset_1(k1_xboole_0,sK1,sK3) | (~spl7_11 | ~spl7_31)),
% 0.21/0.53    inference(superposition,[],[f125,f242])).
% 0.21/0.53  fof(f242,plain,(
% 0.21/0.53    k1_xboole_0 = sK0 | ~spl7_31),
% 0.21/0.53    inference(avatar_component_clause,[],[f241])).
% 0.21/0.53  fof(f125,plain,(
% 0.21/0.53    k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3) | ~spl7_11),
% 0.21/0.53    inference(avatar_component_clause,[],[f124])).
% 0.21/0.53  fof(f326,plain,(
% 0.21/0.53    spl7_39 | ~spl7_3 | ~spl7_20 | ~spl7_31),
% 0.21/0.53    inference(avatar_split_clause,[],[f293,f241,f182,f66,f324])).
% 0.21/0.53  fof(f66,plain,(
% 0.21/0.53    spl7_3 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.21/0.53  fof(f293,plain,(
% 0.21/0.53    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl7_3 | ~spl7_20 | ~spl7_31)),
% 0.21/0.53    inference(forward_demodulation,[],[f281,f183])).
% 0.21/0.53  fof(f281,plain,(
% 0.21/0.53    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) | (~spl7_3 | ~spl7_31)),
% 0.21/0.53    inference(superposition,[],[f67,f242])).
% 0.21/0.53  fof(f67,plain,(
% 0.21/0.53    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl7_3),
% 0.21/0.53    inference(avatar_component_clause,[],[f66])).
% 0.21/0.53  fof(f303,plain,(
% 0.21/0.53    spl7_34 | ~spl7_2 | ~spl7_20 | ~spl7_31),
% 0.21/0.53    inference(avatar_split_clause,[],[f292,f241,f182,f62,f301])).
% 0.21/0.53  fof(f62,plain,(
% 0.21/0.53    spl7_2 <=> v1_funct_2(sK3,sK0,sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.21/0.53  fof(f292,plain,(
% 0.21/0.53    v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | (~spl7_2 | ~spl7_20 | ~spl7_31)),
% 0.21/0.53    inference(forward_demodulation,[],[f280,f183])).
% 0.21/0.53  fof(f280,plain,(
% 0.21/0.53    v1_funct_2(sK3,k1_xboole_0,sK1) | (~spl7_2 | ~spl7_31)),
% 0.21/0.53    inference(superposition,[],[f63,f242])).
% 0.21/0.53  fof(f63,plain,(
% 0.21/0.53    v1_funct_2(sK3,sK0,sK1) | ~spl7_2),
% 0.21/0.53    inference(avatar_component_clause,[],[f62])).
% 0.21/0.53  fof(f276,plain,(
% 0.21/0.53    spl7_13 | ~spl7_30),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f275])).
% 0.21/0.53  fof(f275,plain,(
% 0.21/0.53    $false | (spl7_13 | ~spl7_30)),
% 0.21/0.53    inference(subsumption_resolution,[],[f264,f50])).
% 0.21/0.53  fof(f50,plain,(
% 0.21/0.53    v1_xboole_0(k1_xboole_0)),
% 0.21/0.53    inference(cnf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    v1_xboole_0(k1_xboole_0)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.53  fof(f264,plain,(
% 0.21/0.53    ~v1_xboole_0(k1_xboole_0) | (spl7_13 | ~spl7_30)),
% 0.21/0.53    inference(superposition,[],[f176,f239])).
% 0.21/0.53  fof(f239,plain,(
% 0.21/0.53    k1_xboole_0 = sK3 | ~spl7_30),
% 0.21/0.53    inference(avatar_component_clause,[],[f238])).
% 0.21/0.53  fof(f238,plain,(
% 0.21/0.53    spl7_30 <=> k1_xboole_0 = sK3),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).
% 0.21/0.53  fof(f176,plain,(
% 0.21/0.53    ~v1_xboole_0(sK3) | spl7_13),
% 0.21/0.53    inference(avatar_component_clause,[],[f131])).
% 0.21/0.53  fof(f131,plain,(
% 0.21/0.53    spl7_13 <=> v1_xboole_0(sK3)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 0.21/0.53  fof(f243,plain,(
% 0.21/0.53    spl7_30 | spl7_31 | ~spl7_24 | ~spl7_27),
% 0.21/0.53    inference(avatar_split_clause,[],[f230,f214,f202,f241,f238])).
% 0.21/0.53  fof(f202,plain,(
% 0.21/0.53    spl7_24 <=> v1_funct_2(sK3,sK0,k1_xboole_0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).
% 0.21/0.53  fof(f214,plain,(
% 0.21/0.53    spl7_27 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).
% 0.21/0.53  fof(f230,plain,(
% 0.21/0.53    k1_xboole_0 = sK0 | k1_xboole_0 = sK3 | (~spl7_24 | ~spl7_27)),
% 0.21/0.53    inference(subsumption_resolution,[],[f222,f203])).
% 0.21/0.53  fof(f203,plain,(
% 0.21/0.53    v1_funct_2(sK3,sK0,k1_xboole_0) | ~spl7_24),
% 0.21/0.53    inference(avatar_component_clause,[],[f202])).
% 0.21/0.53  fof(f222,plain,(
% 0.21/0.53    k1_xboole_0 = sK0 | k1_xboole_0 = sK3 | ~v1_funct_2(sK3,sK0,k1_xboole_0) | ~spl7_27),
% 0.21/0.53    inference(resolution,[],[f215,f54])).
% 0.21/0.53  fof(f54,plain,(
% 0.21/0.53    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | k1_xboole_0 = X0 | k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0)) )),
% 0.21/0.53    inference(equality_resolution,[],[f40])).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X1 | k1_xboole_0 = X0 | k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f20])).
% 0.21/0.53  fof(f215,plain,(
% 0.21/0.53    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | ~spl7_27),
% 0.21/0.53    inference(avatar_component_clause,[],[f214])).
% 0.21/0.54  fof(f217,plain,(
% 0.21/0.54    sK0 != k1_relset_1(sK0,sK1,sK3) | k1_relat_1(sK3) != k1_relset_1(sK0,sK1,sK3) | r2_hidden(sK6(sK4,sK2,sK3),sK0) | ~r2_hidden(sK6(sK4,sK2,sK3),k1_relat_1(sK3))),
% 0.21/0.54    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.54  fof(f216,plain,(
% 0.21/0.54    spl7_27 | ~spl7_3 | ~spl7_20),
% 0.21/0.54    inference(avatar_split_clause,[],[f189,f182,f66,f214])).
% 0.21/0.54  fof(f189,plain,(
% 0.21/0.54    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | (~spl7_3 | ~spl7_20)),
% 0.21/0.54    inference(superposition,[],[f67,f183])).
% 0.21/0.54  fof(f212,plain,(
% 0.21/0.54    ~spl7_26 | ~spl7_1 | ~spl7_4 | ~spl7_9 | ~spl7_18),
% 0.21/0.54    inference(avatar_split_clause,[],[f174,f162,f111,f78,f58,f210])).
% 0.21/0.54  fof(f210,plain,(
% 0.21/0.54    spl7_26 <=> r2_hidden(sK6(sK4,sK2,sK3),sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).
% 0.21/0.54  fof(f58,plain,(
% 0.21/0.54    spl7_1 <=> v1_funct_1(sK3)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.21/0.54  fof(f78,plain,(
% 0.21/0.54    spl7_4 <=> v1_relat_1(sK3)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.21/0.54  fof(f111,plain,(
% 0.21/0.54    spl7_9 <=> r2_hidden(sK6(sK4,sK2,sK3),sK2)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.21/0.54  fof(f162,plain,(
% 0.21/0.54    spl7_18 <=> r2_hidden(k4_tarski(sK6(sK4,sK2,sK3),sK4),sK3)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).
% 0.21/0.54  fof(f174,plain,(
% 0.21/0.54    ~r2_hidden(sK6(sK4,sK2,sK3),sK0) | (~spl7_1 | ~spl7_4 | ~spl7_9 | ~spl7_18)),
% 0.21/0.54    inference(subsumption_resolution,[],[f114,f173])).
% 0.21/0.54  fof(f173,plain,(
% 0.21/0.54    sK4 = k1_funct_1(sK3,sK6(sK4,sK2,sK3)) | (~spl7_1 | ~spl7_4 | ~spl7_18)),
% 0.21/0.54    inference(subsumption_resolution,[],[f172,f79])).
% 0.21/0.54  fof(f79,plain,(
% 0.21/0.54    v1_relat_1(sK3) | ~spl7_4),
% 0.21/0.54    inference(avatar_component_clause,[],[f78])).
% 0.21/0.54  fof(f172,plain,(
% 0.21/0.54    sK4 = k1_funct_1(sK3,sK6(sK4,sK2,sK3)) | ~v1_relat_1(sK3) | (~spl7_1 | ~spl7_18)),
% 0.21/0.54    inference(subsumption_resolution,[],[f167,f59])).
% 0.21/0.54  fof(f59,plain,(
% 0.21/0.54    v1_funct_1(sK3) | ~spl7_1),
% 0.21/0.54    inference(avatar_component_clause,[],[f58])).
% 0.21/0.54  fof(f167,plain,(
% 0.21/0.54    ~v1_funct_1(sK3) | sK4 = k1_funct_1(sK3,sK6(sK4,sK2,sK3)) | ~v1_relat_1(sK3) | ~spl7_18),
% 0.21/0.54    inference(resolution,[],[f163,f29])).
% 0.21/0.54  fof(f29,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | k1_funct_1(X2,X0) = X1 | ~v1_relat_1(X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f15])).
% 0.21/0.54  fof(f15,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.54    inference(flattening,[],[f14])).
% 0.21/0.54  fof(f14,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.21/0.54    inference(ennf_transformation,[],[f5])).
% 0.21/0.54  fof(f5,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).
% 0.21/0.54  fof(f163,plain,(
% 0.21/0.54    r2_hidden(k4_tarski(sK6(sK4,sK2,sK3),sK4),sK3) | ~spl7_18),
% 0.21/0.54    inference(avatar_component_clause,[],[f162])).
% 0.21/0.54  fof(f114,plain,(
% 0.21/0.54    ~r2_hidden(sK6(sK4,sK2,sK3),sK0) | sK4 != k1_funct_1(sK3,sK6(sK4,sK2,sK3)) | ~spl7_9),
% 0.21/0.54    inference(resolution,[],[f112,f23])).
% 0.21/0.54  fof(f23,plain,(
% 0.21/0.54    ( ! [X5] : (~r2_hidden(X5,sK2) | ~r2_hidden(X5,sK0) | sK4 != k1_funct_1(sK3,X5)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f13])).
% 0.21/0.54  fof(f13,plain,(
% 0.21/0.54    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.21/0.54    inference(flattening,[],[f12])).
% 0.21/0.54  fof(f12,plain,(
% 0.21/0.54    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.21/0.54    inference(ennf_transformation,[],[f11])).
% 0.21/0.54  fof(f11,negated_conjecture,(
% 0.21/0.54    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 0.21/0.54    inference(negated_conjecture,[],[f10])).
% 0.21/0.54  fof(f10,conjecture,(
% 0.21/0.54    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t115_funct_2)).
% 0.21/0.54  fof(f112,plain,(
% 0.21/0.54    r2_hidden(sK6(sK4,sK2,sK3),sK2) | ~spl7_9),
% 0.21/0.54    inference(avatar_component_clause,[],[f111])).
% 0.21/0.54  fof(f204,plain,(
% 0.21/0.54    spl7_24 | ~spl7_2 | ~spl7_20),
% 0.21/0.54    inference(avatar_split_clause,[],[f188,f182,f62,f202])).
% 0.21/0.54  fof(f188,plain,(
% 0.21/0.54    v1_funct_2(sK3,sK0,k1_xboole_0) | (~spl7_2 | ~spl7_20)),
% 0.21/0.54    inference(superposition,[],[f63,f183])).
% 0.21/0.54  fof(f184,plain,(
% 0.21/0.54    spl7_19 | spl7_20 | ~spl7_2 | ~spl7_3),
% 0.21/0.54    inference(avatar_split_clause,[],[f76,f66,f62,f182,f179])).
% 0.21/0.54  fof(f179,plain,(
% 0.21/0.54    spl7_19 <=> sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).
% 0.21/0.54  fof(f76,plain,(
% 0.21/0.54    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3) | (~spl7_2 | ~spl7_3)),
% 0.21/0.54    inference(subsumption_resolution,[],[f71,f63])).
% 0.21/0.54  fof(f71,plain,(
% 0.21/0.54    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3) | ~v1_funct_2(sK3,sK0,sK1) | ~spl7_3),
% 0.21/0.54    inference(resolution,[],[f67,f44])).
% 0.21/0.54  fof(f44,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f20])).
% 0.21/0.54  fof(f177,plain,(
% 0.21/0.54    ~spl7_13 | ~spl7_18),
% 0.21/0.54    inference(avatar_split_clause,[],[f168,f162,f131])).
% 0.21/0.54  fof(f168,plain,(
% 0.21/0.54    ~v1_xboole_0(sK3) | ~spl7_18),
% 0.21/0.54    inference(resolution,[],[f163,f36])).
% 0.21/0.54  fof(f36,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f1])).
% 0.21/0.54  fof(f1,axiom,(
% 0.21/0.54    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.54  fof(f164,plain,(
% 0.21/0.54    spl7_18 | ~spl7_4 | ~spl7_6),
% 0.21/0.54    inference(avatar_split_clause,[],[f96,f87,f78,f162])).
% 0.21/0.54  fof(f87,plain,(
% 0.21/0.54    spl7_6 <=> r2_hidden(sK4,k9_relat_1(sK3,sK2))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.21/0.54  fof(f96,plain,(
% 0.21/0.54    r2_hidden(k4_tarski(sK6(sK4,sK2,sK3),sK4),sK3) | (~spl7_4 | ~spl7_6)),
% 0.21/0.54    inference(subsumption_resolution,[],[f91,f79])).
% 0.21/0.54  fof(f91,plain,(
% 0.21/0.54    r2_hidden(k4_tarski(sK6(sK4,sK2,sK3),sK4),sK3) | ~v1_relat_1(sK3) | ~spl7_6),
% 0.21/0.54    inference(resolution,[],[f88,f47])).
% 0.21/0.54  fof(f47,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(k4_tarski(sK6(X0,X1,X2),X0),X2) | ~v1_relat_1(X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f22])).
% 0.21/0.54  fof(f22,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.21/0.54    inference(ennf_transformation,[],[f4])).
% 0.21/0.54  fof(f4,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).
% 0.21/0.54  fof(f88,plain,(
% 0.21/0.54    r2_hidden(sK4,k9_relat_1(sK3,sK2)) | ~spl7_6),
% 0.21/0.54    inference(avatar_component_clause,[],[f87])).
% 0.21/0.54  fof(f144,plain,(
% 0.21/0.54    spl7_15 | ~spl7_4 | ~spl7_6),
% 0.21/0.54    inference(avatar_split_clause,[],[f95,f87,f78,f142])).
% 0.21/0.54  fof(f142,plain,(
% 0.21/0.54    spl7_15 <=> r2_hidden(sK6(sK4,sK2,sK3),k1_relat_1(sK3))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 0.21/0.54  fof(f95,plain,(
% 0.21/0.54    r2_hidden(sK6(sK4,sK2,sK3),k1_relat_1(sK3)) | (~spl7_4 | ~spl7_6)),
% 0.21/0.54    inference(subsumption_resolution,[],[f90,f79])).
% 0.21/0.54  fof(f90,plain,(
% 0.21/0.54    r2_hidden(sK6(sK4,sK2,sK3),k1_relat_1(sK3)) | ~v1_relat_1(sK3) | ~spl7_6),
% 0.21/0.54    inference(resolution,[],[f88,f46])).
% 0.21/0.54  fof(f46,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(sK6(X0,X1,X2),k1_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f22])).
% 0.21/0.54  fof(f126,plain,(
% 0.21/0.54    spl7_11 | ~spl7_3),
% 0.21/0.54    inference(avatar_split_clause,[],[f69,f66,f124])).
% 0.21/0.54  fof(f69,plain,(
% 0.21/0.54    k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3) | ~spl7_3),
% 0.21/0.54    inference(resolution,[],[f67,f45])).
% 0.21/0.54  fof(f45,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relat_1(X2) = k1_relset_1(X0,X1,X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f21])).
% 0.21/0.54  fof(f21,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.54    inference(ennf_transformation,[],[f7])).
% 0.21/0.54  fof(f7,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.54  fof(f113,plain,(
% 0.21/0.54    spl7_9 | ~spl7_4 | ~spl7_6),
% 0.21/0.54    inference(avatar_split_clause,[],[f97,f87,f78,f111])).
% 0.21/0.54  fof(f97,plain,(
% 0.21/0.54    r2_hidden(sK6(sK4,sK2,sK3),sK2) | (~spl7_4 | ~spl7_6)),
% 0.21/0.54    inference(subsumption_resolution,[],[f92,f79])).
% 0.21/0.54  fof(f92,plain,(
% 0.21/0.54    r2_hidden(sK6(sK4,sK2,sK3),sK2) | ~v1_relat_1(sK3) | ~spl7_6),
% 0.21/0.54    inference(resolution,[],[f88,f48])).
% 0.21/0.54  fof(f48,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(sK6(X0,X1,X2),X1) | ~v1_relat_1(X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f22])).
% 0.21/0.54  fof(f89,plain,(
% 0.21/0.54    spl7_6 | ~spl7_3 | ~spl7_5),
% 0.21/0.54    inference(avatar_split_clause,[],[f85,f82,f66,f87])).
% 0.21/0.54  fof(f82,plain,(
% 0.21/0.54    spl7_5 <=> r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.21/0.54  fof(f85,plain,(
% 0.21/0.54    r2_hidden(sK4,k9_relat_1(sK3,sK2)) | (~spl7_3 | ~spl7_5)),
% 0.21/0.54    inference(forward_demodulation,[],[f83,f73])).
% 0.21/0.54  fof(f73,plain,(
% 0.21/0.54    ( ! [X0] : (k7_relset_1(sK0,sK1,sK3,X0) = k9_relat_1(sK3,X0)) ) | ~spl7_3),
% 0.21/0.54    inference(resolution,[],[f67,f37])).
% 0.21/0.54  fof(f37,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f17])).
% 0.21/0.54  fof(f17,plain,(
% 0.21/0.54    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.54    inference(ennf_transformation,[],[f8])).
% 0.21/0.54  fof(f8,axiom,(
% 0.21/0.54    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.21/0.54  fof(f83,plain,(
% 0.21/0.54    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) | ~spl7_5),
% 0.21/0.54    inference(avatar_component_clause,[],[f82])).
% 0.21/0.54  fof(f84,plain,(
% 0.21/0.54    spl7_5),
% 0.21/0.54    inference(avatar_split_clause,[],[f24,f82])).
% 0.21/0.54  fof(f24,plain,(
% 0.21/0.54    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))),
% 0.21/0.54    inference(cnf_transformation,[],[f13])).
% 0.21/0.54  fof(f80,plain,(
% 0.21/0.54    spl7_4 | ~spl7_3),
% 0.21/0.54    inference(avatar_split_clause,[],[f72,f66,f78])).
% 0.21/0.54  fof(f72,plain,(
% 0.21/0.54    v1_relat_1(sK3) | ~spl7_3),
% 0.21/0.54    inference(resolution,[],[f67,f38])).
% 0.21/0.54  fof(f38,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f18])).
% 0.21/0.54  fof(f18,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.54    inference(ennf_transformation,[],[f6])).
% 0.21/0.54  fof(f6,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.54  fof(f68,plain,(
% 0.21/0.54    spl7_3),
% 0.21/0.54    inference(avatar_split_clause,[],[f27,f66])).
% 0.21/0.54  fof(f27,plain,(
% 0.21/0.54    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.54    inference(cnf_transformation,[],[f13])).
% 0.21/0.54  fof(f64,plain,(
% 0.21/0.54    spl7_2),
% 0.21/0.54    inference(avatar_split_clause,[],[f26,f62])).
% 0.21/0.54  fof(f26,plain,(
% 0.21/0.54    v1_funct_2(sK3,sK0,sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f13])).
% 0.21/0.54  fof(f60,plain,(
% 0.21/0.54    spl7_1),
% 0.21/0.54    inference(avatar_split_clause,[],[f25,f58])).
% 0.21/0.54  fof(f25,plain,(
% 0.21/0.54    v1_funct_1(sK3)),
% 0.21/0.54    inference(cnf_transformation,[],[f13])).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (30164)------------------------------
% 0.21/0.54  % (30164)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (30164)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (30164)Memory used [KB]: 6396
% 0.21/0.54  % (30164)Time elapsed: 0.088 s
% 0.21/0.54  % (30164)------------------------------
% 0.21/0.54  % (30164)------------------------------
% 0.21/0.54  % (30163)Success in time 0.178 s
%------------------------------------------------------------------------------
