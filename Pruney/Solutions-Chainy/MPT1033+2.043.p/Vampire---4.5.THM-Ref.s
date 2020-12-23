%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:49 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  168 ( 323 expanded)
%              Number of leaves         :   46 ( 146 expanded)
%              Depth                    :    8
%              Number of atoms          :  569 (1513 expanded)
%              Number of equality atoms :   77 ( 258 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f412,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f61,f66,f71,f76,f81,f86,f91,f96,f101,f110,f116,f123,f140,f144,f148,f161,f188,f194,f199,f213,f227,f238,f243,f262,f322,f350,f372,f402,f408,f409,f410])).

fof(f410,plain,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 != sK3
    | sK2 = sK3 ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f409,plain,
    ( sK2 != sK3
    | r2_relset_1(sK0,sK1,sK2,sK3)
    | ~ r2_relset_1(sK0,sK1,sK3,sK3) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f408,plain,
    ( ~ spl7_8
    | ~ spl7_9
    | ~ spl7_47 ),
    inference(avatar_contradiction_clause,[],[f407])).

fof(f407,plain,
    ( $false
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_47 ),
    inference(subsumption_resolution,[],[f404,f95])).

fof(f95,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl7_8
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f404,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_9
    | ~ spl7_47 ),
    inference(resolution,[],[f397,f100])).

fof(f100,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl7_9
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f397,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) )
    | ~ spl7_47 ),
    inference(avatar_component_clause,[],[f396])).

fof(f396,plain,
    ( spl7_47
  <=> ! [X0] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_47])])).

fof(f402,plain,
    ( spl7_47
    | spl7_48
    | ~ spl7_1
    | ~ spl7_4
    | ~ spl7_19
    | ~ spl7_44 ),
    inference(avatar_split_clause,[],[f393,f370,f158,f73,f58,f399,f396])).

fof(f399,plain,
    ( spl7_48
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_48])])).

fof(f58,plain,
    ( spl7_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f73,plain,
    ( spl7_4
  <=> r1_partfun1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f158,plain,
    ( spl7_19
  <=> v1_partfun1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f370,plain,
    ( spl7_44
  <=> ! [X1,X0] :
        ( ~ r1_partfun1(X0,sK3)
        | sK3 = X0
        | ~ v1_partfun1(X0,sK0)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
        | ~ v1_funct_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_44])])).

fof(f393,plain,
    ( ! [X0] :
        ( sK2 = sK3
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) )
    | ~ spl7_1
    | ~ spl7_4
    | ~ spl7_19
    | ~ spl7_44 ),
    inference(subsumption_resolution,[],[f384,f160])).

fof(f160,plain,
    ( v1_partfun1(sK2,sK0)
    | ~ spl7_19 ),
    inference(avatar_component_clause,[],[f158])).

fof(f384,plain,
    ( ! [X0] :
        ( sK2 = sK3
        | ~ v1_partfun1(sK2,sK0)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) )
    | ~ spl7_1
    | ~ spl7_4
    | ~ spl7_44 ),
    inference(subsumption_resolution,[],[f383,f60])).

fof(f60,plain,
    ( v1_funct_1(sK2)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f58])).

fof(f383,plain,
    ( ! [X0] :
        ( sK2 = sK3
        | ~ v1_partfun1(sK2,sK0)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
        | ~ v1_funct_1(sK2) )
    | ~ spl7_4
    | ~ spl7_44 ),
    inference(resolution,[],[f75,f371])).

fof(f371,plain,
    ( ! [X0,X1] :
        ( ~ r1_partfun1(X0,sK3)
        | sK3 = X0
        | ~ v1_partfun1(X0,sK0)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
        | ~ v1_funct_1(X0) )
    | ~ spl7_44 ),
    inference(avatar_component_clause,[],[f370])).

fof(f75,plain,
    ( r1_partfun1(sK2,sK3)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f73])).

fof(f372,plain,
    ( spl7_44
    | ~ spl7_2
    | ~ spl7_41 ),
    inference(avatar_split_clause,[],[f354,f347,f63,f370])).

fof(f63,plain,
    ( spl7_2
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f347,plain,
    ( spl7_41
  <=> v1_partfun1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_41])])).

fof(f354,plain,
    ( ! [X0,X1] :
        ( ~ r1_partfun1(X0,sK3)
        | sK3 = X0
        | ~ v1_partfun1(X0,sK0)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
        | ~ v1_funct_1(X0) )
    | ~ spl7_2
    | ~ spl7_41 ),
    inference(subsumption_resolution,[],[f353,f65])).

fof(f65,plain,
    ( v1_funct_1(sK3)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f63])).

fof(f353,plain,
    ( ! [X0,X1] :
        ( ~ r1_partfun1(X0,sK3)
        | sK3 = X0
        | ~ v1_partfun1(X0,sK0)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
        | ~ v1_funct_1(sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
        | ~ v1_funct_1(X0) )
    | ~ spl7_41 ),
    inference(resolution,[],[f349,f48])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_partfun1(X3,X0)
      | ~ r1_partfun1(X2,X3)
      | X2 = X3
      | ~ v1_partfun1(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( X2 = X3
          | ~ r1_partfun1(X2,X3)
          | ~ v1_partfun1(X3,X0)
          | ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( X2 = X3
          | ~ r1_partfun1(X2,X3)
          | ~ v1_partfun1(X3,X0)
          | ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_1(X3) )
         => ( ( r1_partfun1(X2,X3)
              & v1_partfun1(X3,X0)
              & v1_partfun1(X2,X0) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_partfun1)).

fof(f349,plain,
    ( v1_partfun1(sK3,sK0)
    | ~ spl7_41 ),
    inference(avatar_component_clause,[],[f347])).

fof(f350,plain,
    ( spl7_41
    | ~ spl7_6
    | ~ spl7_9
    | ~ spl7_17
    | spl7_18 ),
    inference(avatar_split_clause,[],[f345,f154,f146,f98,f83,f347])).

fof(f83,plain,
    ( spl7_6
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f146,plain,
    ( spl7_17
  <=> ! [X3,X2] :
        ( ~ v1_funct_2(sK3,X2,X3)
        | v1_partfun1(sK3,X2)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | v1_xboole_0(X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f154,plain,
    ( spl7_18
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f345,plain,
    ( v1_partfun1(sK3,sK0)
    | ~ spl7_6
    | ~ spl7_9
    | ~ spl7_17
    | spl7_18 ),
    inference(subsumption_resolution,[],[f344,f155])).

fof(f155,plain,
    ( ~ v1_xboole_0(sK1)
    | spl7_18 ),
    inference(avatar_component_clause,[],[f154])).

fof(f344,plain,
    ( v1_partfun1(sK3,sK0)
    | v1_xboole_0(sK1)
    | ~ spl7_6
    | ~ spl7_9
    | ~ spl7_17 ),
    inference(subsumption_resolution,[],[f342,f100])).

fof(f342,plain,
    ( v1_partfun1(sK3,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_xboole_0(sK1)
    | ~ spl7_6
    | ~ spl7_17 ),
    inference(resolution,[],[f147,f85])).

fof(f85,plain,
    ( v1_funct_2(sK3,sK0,sK1)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f83])).

fof(f147,plain,
    ( ! [X2,X3] :
        ( ~ v1_funct_2(sK3,X2,X3)
        | v1_partfun1(sK3,X2)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | v1_xboole_0(X3) )
    | ~ spl7_17 ),
    inference(avatar_component_clause,[],[f146])).

fof(f322,plain,
    ( spl7_38
    | ~ spl7_28 ),
    inference(avatar_split_clause,[],[f246,f241,f319])).

fof(f319,plain,
    ( spl7_38
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_38])])).

fof(f241,plain,
    ( spl7_28
  <=> ! [X0] : ~ r2_hidden(X0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).

fof(f246,plain,
    ( k1_xboole_0 = sK3
    | ~ spl7_28 ),
    inference(resolution,[],[f242,f39])).

fof(f39,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( ! [X2,X3] :
            ( k4_tarski(X2,X3) != sK4(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK4(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f13,f25])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] :
            ( k4_tarski(X2,X3) != sK4(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK4(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3] :
                  ~ ( k4_tarski(X2,X3) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_mcart_1)).

fof(f242,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK3)
    | ~ spl7_28 ),
    inference(avatar_component_clause,[],[f241])).

fof(f262,plain,
    ( spl7_29
    | ~ spl7_27 ),
    inference(avatar_split_clause,[],[f244,f236,f259])).

fof(f259,plain,
    ( spl7_29
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_29])])).

fof(f236,plain,
    ( spl7_27
  <=> ! [X0] : ~ r2_hidden(X0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).

fof(f244,plain,
    ( k1_xboole_0 = sK2
    | ~ spl7_27 ),
    inference(resolution,[],[f237,f39])).

fof(f237,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK2)
    | ~ spl7_27 ),
    inference(avatar_component_clause,[],[f236])).

fof(f243,plain,
    ( spl7_28
    | ~ spl7_26 ),
    inference(avatar_split_clause,[],[f228,f224,f241])).

fof(f224,plain,
    ( spl7_26
  <=> sP5(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).

fof(f228,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK3)
    | ~ spl7_26 ),
    inference(resolution,[],[f226,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ sP5(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(general_splitting,[],[f49,f53_D])).

fof(f53,plain,(
    ! [X2,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | sP5(X1) ) ),
    inference(cnf_transformation,[],[f53_D])).

fof(f53_D,plain,(
    ! [X1] :
      ( ! [X2] :
          ( ~ v1_xboole_0(X2)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) )
    <=> ~ sP5(X1) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP5])])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f226,plain,
    ( sP5(sK3)
    | ~ spl7_26 ),
    inference(avatar_component_clause,[],[f224])).

fof(f238,plain,
    ( spl7_27
    | ~ spl7_24 ),
    inference(avatar_split_clause,[],[f217,f210,f236])).

fof(f210,plain,
    ( spl7_24
  <=> sP5(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).

fof(f217,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK2)
    | ~ spl7_24 ),
    inference(resolution,[],[f212,f54])).

fof(f212,plain,
    ( sP5(sK2)
    | ~ spl7_24 ),
    inference(avatar_component_clause,[],[f210])).

fof(f227,plain,
    ( spl7_26
    | ~ spl7_13
    | ~ spl7_22 ),
    inference(avatar_split_clause,[],[f216,f196,f121,f224])).

fof(f121,plain,
    ( spl7_13
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | sP5(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f196,plain,
    ( spl7_22
  <=> m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f216,plain,
    ( sP5(sK3)
    | ~ spl7_13
    | ~ spl7_22 ),
    inference(resolution,[],[f198,f122])).

fof(f122,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | sP5(X0) )
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f121])).

fof(f198,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_22 ),
    inference(avatar_component_clause,[],[f196])).

fof(f213,plain,
    ( spl7_24
    | ~ spl7_13
    | ~ spl7_21 ),
    inference(avatar_split_clause,[],[f208,f191,f121,f210])).

fof(f191,plain,
    ( spl7_21
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).

fof(f208,plain,
    ( sP5(sK2)
    | ~ spl7_13
    | ~ spl7_21 ),
    inference(resolution,[],[f193,f122])).

fof(f193,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_21 ),
    inference(avatar_component_clause,[],[f191])).

fof(f199,plain,
    ( spl7_22
    | ~ spl7_9
    | ~ spl7_11 ),
    inference(avatar_split_clause,[],[f181,f107,f98,f196])).

fof(f107,plain,
    ( spl7_11
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f181,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_9
    | ~ spl7_11 ),
    inference(forward_demodulation,[],[f177,f52])).

fof(f52,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f177,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ spl7_9
    | ~ spl7_11 ),
    inference(backward_demodulation,[],[f100,f109])).

fof(f109,plain,
    ( k1_xboole_0 = sK0
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f107])).

fof(f194,plain,
    ( spl7_21
    | ~ spl7_8
    | ~ spl7_11 ),
    inference(avatar_split_clause,[],[f180,f107,f93,f191])).

fof(f180,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_8
    | ~ spl7_11 ),
    inference(forward_demodulation,[],[f176,f52])).

fof(f176,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ spl7_8
    | ~ spl7_11 ),
    inference(backward_demodulation,[],[f95,f109])).

fof(f188,plain,
    ( spl7_10
    | ~ spl7_12
    | ~ spl7_18 ),
    inference(avatar_split_clause,[],[f165,f154,f114,f103])).

fof(f103,plain,
    ( spl7_10
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f114,plain,
    ( spl7_12
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f165,plain,
    ( k1_xboole_0 = sK1
    | ~ spl7_12
    | ~ spl7_18 ),
    inference(resolution,[],[f156,f115])).

fof(f115,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = X0 )
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f114])).

fof(f156,plain,
    ( v1_xboole_0(sK1)
    | ~ spl7_18 ),
    inference(avatar_component_clause,[],[f154])).

fof(f161,plain,
    ( spl7_18
    | spl7_19
    | ~ spl7_5
    | ~ spl7_8
    | ~ spl7_16 ),
    inference(avatar_split_clause,[],[f150,f142,f93,f78,f158,f154])).

fof(f78,plain,
    ( spl7_5
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f142,plain,
    ( spl7_16
  <=> ! [X1,X0] :
        ( ~ v1_funct_2(sK2,X0,X1)
        | v1_partfun1(sK2,X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_xboole_0(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f150,plain,
    ( v1_partfun1(sK2,sK0)
    | v1_xboole_0(sK1)
    | ~ spl7_5
    | ~ spl7_8
    | ~ spl7_16 ),
    inference(subsumption_resolution,[],[f149,f95])).

fof(f149,plain,
    ( v1_partfun1(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_xboole_0(sK1)
    | ~ spl7_5
    | ~ spl7_16 ),
    inference(resolution,[],[f143,f80])).

fof(f80,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f78])).

fof(f143,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(sK2,X0,X1)
        | v1_partfun1(sK2,X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_xboole_0(X1) )
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f142])).

fof(f148,plain,
    ( spl7_17
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f135,f63,f146])).

fof(f135,plain,
    ( ! [X2,X3] :
        ( ~ v1_funct_2(sK3,X2,X3)
        | v1_partfun1(sK3,X2)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | v1_xboole_0(X3) )
    | ~ spl7_2 ),
    inference(resolution,[],[f43,f65])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | v1_partfun1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f144,plain,
    ( spl7_16
    | ~ spl7_1 ),
    inference(avatar_split_clause,[],[f134,f58,f142])).

fof(f134,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(sK2,X0,X1)
        | v1_partfun1(sK2,X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_xboole_0(X1) )
    | ~ spl7_1 ),
    inference(resolution,[],[f43,f60])).

fof(f140,plain,
    ( spl7_15
    | ~ spl7_9 ),
    inference(avatar_split_clause,[],[f126,f98,f137])).

fof(f137,plain,
    ( spl7_15
  <=> r2_relset_1(sK0,sK1,sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f126,plain,
    ( r2_relset_1(sK0,sK1,sK3,sK3)
    | ~ spl7_9 ),
    inference(resolution,[],[f124,f100])).

fof(f124,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X2,X2) ) ),
    inference(subsumption_resolution,[],[f55,f56])).

fof(f56,plain,(
    ! [X0,X3,X1] :
      ( ~ sP6(X1,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(general_splitting,[],[f50,f55_D])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP6(X1,X0) ) ),
    inference(cnf_transformation,[],[f55_D])).

fof(f55_D,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_relset_1(X0,X1,X2,X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    <=> ~ sP6(X1,X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP6])])).

fof(f123,plain,
    ( spl7_13
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f112,f68,f121])).

fof(f68,plain,
    ( spl7_3
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f112,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | sP5(X0) )
    | ~ spl7_3 ),
    inference(resolution,[],[f53,f70])).

fof(f70,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f68])).

fof(f116,plain,
    ( spl7_12
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f111,f68,f114])).

fof(f111,plain,
    ( ! [X0] :
        ( k1_xboole_0 = X0
        | ~ v1_xboole_0(X0) )
    | ~ spl7_3 ),
    inference(resolution,[],[f47,f70])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | X0 = X1
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

fof(f110,plain,
    ( ~ spl7_10
    | spl7_11 ),
    inference(avatar_split_clause,[],[f36,f107,f103])).

fof(f36,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK3)
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_partfun1(sK2,sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f12,f23,f22])).

fof(f22,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ~ r2_relset_1(X0,X1,X2,X3)
            & ( k1_xboole_0 = X0
              | k1_xboole_0 != X1 )
            & r1_partfun1(X2,X3)
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ~ r2_relset_1(sK0,sK1,sK2,X3)
          & ( k1_xboole_0 = sK0
            | k1_xboole_0 != sK1 )
          & r1_partfun1(sK2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
          & v1_funct_2(X3,sK0,sK1)
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X3] :
        ( ~ r2_relset_1(sK0,sK1,sK2,X3)
        & ( k1_xboole_0 = sK0
          | k1_xboole_0 != sK1 )
        & r1_partfun1(sK2,X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        & v1_funct_2(X3,sK0,sK1)
        & v1_funct_1(X3) )
   => ( ~ r2_relset_1(sK0,sK1,sK2,sK3)
      & ( k1_xboole_0 = sK0
        | k1_xboole_0 != sK1 )
      & r1_partfun1(sK2,sK3)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & r1_partfun1(X2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & r1_partfun1(X2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X3,X0,X1)
              & v1_funct_1(X3) )
           => ( r1_partfun1(X2,X3)
             => ( r2_relset_1(X0,X1,X2,X3)
                | ( k1_xboole_0 != X0
                  & k1_xboole_0 = X1 ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( r1_partfun1(X2,X3)
           => ( r2_relset_1(X0,X1,X2,X3)
              | ( k1_xboole_0 != X0
                & k1_xboole_0 = X1 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_2)).

fof(f101,plain,(
    spl7_9 ),
    inference(avatar_split_clause,[],[f34,f98])).

fof(f34,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f24])).

fof(f96,plain,(
    spl7_8 ),
    inference(avatar_split_clause,[],[f31,f93])).

fof(f31,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f24])).

fof(f91,plain,(
    ~ spl7_7 ),
    inference(avatar_split_clause,[],[f37,f88])).

fof(f88,plain,
    ( spl7_7
  <=> r2_relset_1(sK0,sK1,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f37,plain,(
    ~ r2_relset_1(sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f24])).

fof(f86,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f33,f83])).

fof(f33,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f81,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f30,f78])).

fof(f30,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f76,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f35,f73])).

fof(f35,plain,(
    r1_partfun1(sK2,sK3) ),
    inference(cnf_transformation,[],[f24])).

fof(f71,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f38,f68])).

fof(f38,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f66,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f32,f63])).

fof(f32,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f24])).

fof(f61,plain,(
    spl7_1 ),
    inference(avatar_split_clause,[],[f29,f58])).

fof(f29,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:24:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.53  % (3846)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.54  % (3846)Refutation found. Thanks to Tanya!
% 0.22/0.54  % SZS status Theorem for theBenchmark
% 0.22/0.54  % (3867)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.54  % (3859)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.54  % (3864)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.55  % (3849)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.55  % SZS output start Proof for theBenchmark
% 0.22/0.55  fof(f412,plain,(
% 0.22/0.55    $false),
% 0.22/0.55    inference(avatar_sat_refutation,[],[f61,f66,f71,f76,f81,f86,f91,f96,f101,f110,f116,f123,f140,f144,f148,f161,f188,f194,f199,f213,f227,f238,f243,f262,f322,f350,f372,f402,f408,f409,f410])).
% 0.22/0.55  fof(f410,plain,(
% 0.22/0.55    k1_xboole_0 != sK2 | k1_xboole_0 != sK3 | sK2 = sK3),
% 0.22/0.55    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.55  fof(f409,plain,(
% 0.22/0.55    sK2 != sK3 | r2_relset_1(sK0,sK1,sK2,sK3) | ~r2_relset_1(sK0,sK1,sK3,sK3)),
% 0.22/0.55    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.55  fof(f408,plain,(
% 0.22/0.55    ~spl7_8 | ~spl7_9 | ~spl7_47),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f407])).
% 0.22/0.55  fof(f407,plain,(
% 0.22/0.55    $false | (~spl7_8 | ~spl7_9 | ~spl7_47)),
% 0.22/0.55    inference(subsumption_resolution,[],[f404,f95])).
% 0.22/0.55  fof(f95,plain,(
% 0.22/0.55    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl7_8),
% 0.22/0.55    inference(avatar_component_clause,[],[f93])).
% 0.22/0.55  fof(f93,plain,(
% 0.22/0.55    spl7_8 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.22/0.55  fof(f404,plain,(
% 0.22/0.55    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | (~spl7_9 | ~spl7_47)),
% 0.22/0.55    inference(resolution,[],[f397,f100])).
% 0.22/0.55  fof(f100,plain,(
% 0.22/0.55    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl7_9),
% 0.22/0.55    inference(avatar_component_clause,[],[f98])).
% 0.22/0.55  fof(f98,plain,(
% 0.22/0.55    spl7_9 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.22/0.55  fof(f397,plain,(
% 0.22/0.55    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))) ) | ~spl7_47),
% 0.22/0.55    inference(avatar_component_clause,[],[f396])).
% 0.22/0.55  fof(f396,plain,(
% 0.22/0.55    spl7_47 <=> ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_47])])).
% 0.22/0.55  fof(f402,plain,(
% 0.22/0.55    spl7_47 | spl7_48 | ~spl7_1 | ~spl7_4 | ~spl7_19 | ~spl7_44),
% 0.22/0.55    inference(avatar_split_clause,[],[f393,f370,f158,f73,f58,f399,f396])).
% 0.22/0.55  fof(f399,plain,(
% 0.22/0.55    spl7_48 <=> sK2 = sK3),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_48])])).
% 0.22/0.55  fof(f58,plain,(
% 0.22/0.55    spl7_1 <=> v1_funct_1(sK2)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.22/0.55  fof(f73,plain,(
% 0.22/0.55    spl7_4 <=> r1_partfun1(sK2,sK3)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.22/0.55  fof(f158,plain,(
% 0.22/0.55    spl7_19 <=> v1_partfun1(sK2,sK0)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).
% 0.22/0.55  fof(f370,plain,(
% 0.22/0.55    spl7_44 <=> ! [X1,X0] : (~r1_partfun1(X0,sK3) | sK3 = X0 | ~v1_partfun1(X0,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) | ~v1_funct_1(X0))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_44])])).
% 0.22/0.55  fof(f393,plain,(
% 0.22/0.55    ( ! [X0] : (sK2 = sK3 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))) ) | (~spl7_1 | ~spl7_4 | ~spl7_19 | ~spl7_44)),
% 0.22/0.55    inference(subsumption_resolution,[],[f384,f160])).
% 0.22/0.55  fof(f160,plain,(
% 0.22/0.55    v1_partfun1(sK2,sK0) | ~spl7_19),
% 0.22/0.55    inference(avatar_component_clause,[],[f158])).
% 0.22/0.55  fof(f384,plain,(
% 0.22/0.55    ( ! [X0] : (sK2 = sK3 | ~v1_partfun1(sK2,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))) ) | (~spl7_1 | ~spl7_4 | ~spl7_44)),
% 0.22/0.55    inference(subsumption_resolution,[],[f383,f60])).
% 0.22/0.55  fof(f60,plain,(
% 0.22/0.55    v1_funct_1(sK2) | ~spl7_1),
% 0.22/0.55    inference(avatar_component_clause,[],[f58])).
% 0.22/0.55  fof(f383,plain,(
% 0.22/0.55    ( ! [X0] : (sK2 = sK3 | ~v1_partfun1(sK2,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) | ~v1_funct_1(sK2)) ) | (~spl7_4 | ~spl7_44)),
% 0.22/0.55    inference(resolution,[],[f75,f371])).
% 0.22/0.55  fof(f371,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~r1_partfun1(X0,sK3) | sK3 = X0 | ~v1_partfun1(X0,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) | ~v1_funct_1(X0)) ) | ~spl7_44),
% 0.22/0.55    inference(avatar_component_clause,[],[f370])).
% 0.22/0.55  fof(f75,plain,(
% 0.22/0.55    r1_partfun1(sK2,sK3) | ~spl7_4),
% 0.22/0.55    inference(avatar_component_clause,[],[f73])).
% 0.22/0.55  fof(f372,plain,(
% 0.22/0.55    spl7_44 | ~spl7_2 | ~spl7_41),
% 0.22/0.55    inference(avatar_split_clause,[],[f354,f347,f63,f370])).
% 0.22/0.55  fof(f63,plain,(
% 0.22/0.55    spl7_2 <=> v1_funct_1(sK3)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.22/0.55  fof(f347,plain,(
% 0.22/0.55    spl7_41 <=> v1_partfun1(sK3,sK0)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_41])])).
% 0.22/0.55  fof(f354,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~r1_partfun1(X0,sK3) | sK3 = X0 | ~v1_partfun1(X0,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) | ~v1_funct_1(X0)) ) | (~spl7_2 | ~spl7_41)),
% 0.22/0.55    inference(subsumption_resolution,[],[f353,f65])).
% 0.22/0.55  fof(f65,plain,(
% 0.22/0.55    v1_funct_1(sK3) | ~spl7_2),
% 0.22/0.55    inference(avatar_component_clause,[],[f63])).
% 0.22/0.55  fof(f353,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~r1_partfun1(X0,sK3) | sK3 = X0 | ~v1_partfun1(X0,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) | ~v1_funct_1(sK3) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) | ~v1_funct_1(X0)) ) | ~spl7_41),
% 0.22/0.55    inference(resolution,[],[f349,f48])).
% 0.22/0.55  fof(f48,plain,(
% 0.22/0.55    ( ! [X2,X0,X3,X1] : (~v1_partfun1(X3,X0) | ~r1_partfun1(X2,X3) | X2 = X3 | ~v1_partfun1(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f18])).
% 0.22/0.55  fof(f18,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (! [X3] : (X2 = X3 | ~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.22/0.55    inference(flattening,[],[f17])).
% 0.22/0.55  fof(f17,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (! [X3] : ((X2 = X3 | (~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.22/0.55    inference(ennf_transformation,[],[f8])).
% 0.22/0.55  fof(f8,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ((r1_partfun1(X2,X3) & v1_partfun1(X3,X0) & v1_partfun1(X2,X0)) => X2 = X3)))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_partfun1)).
% 0.22/0.55  fof(f349,plain,(
% 0.22/0.55    v1_partfun1(sK3,sK0) | ~spl7_41),
% 0.22/0.55    inference(avatar_component_clause,[],[f347])).
% 0.22/0.55  fof(f350,plain,(
% 0.22/0.55    spl7_41 | ~spl7_6 | ~spl7_9 | ~spl7_17 | spl7_18),
% 0.22/0.55    inference(avatar_split_clause,[],[f345,f154,f146,f98,f83,f347])).
% 0.22/0.55  fof(f83,plain,(
% 0.22/0.55    spl7_6 <=> v1_funct_2(sK3,sK0,sK1)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.22/0.55  fof(f146,plain,(
% 0.22/0.55    spl7_17 <=> ! [X3,X2] : (~v1_funct_2(sK3,X2,X3) | v1_partfun1(sK3,X2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | v1_xboole_0(X3))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).
% 0.22/0.55  fof(f154,plain,(
% 0.22/0.55    spl7_18 <=> v1_xboole_0(sK1)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).
% 0.22/0.55  fof(f345,plain,(
% 0.22/0.55    v1_partfun1(sK3,sK0) | (~spl7_6 | ~spl7_9 | ~spl7_17 | spl7_18)),
% 0.22/0.55    inference(subsumption_resolution,[],[f344,f155])).
% 0.22/0.55  fof(f155,plain,(
% 0.22/0.55    ~v1_xboole_0(sK1) | spl7_18),
% 0.22/0.55    inference(avatar_component_clause,[],[f154])).
% 0.22/0.55  fof(f344,plain,(
% 0.22/0.55    v1_partfun1(sK3,sK0) | v1_xboole_0(sK1) | (~spl7_6 | ~spl7_9 | ~spl7_17)),
% 0.22/0.55    inference(subsumption_resolution,[],[f342,f100])).
% 0.22/0.55  fof(f342,plain,(
% 0.22/0.55    v1_partfun1(sK3,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | v1_xboole_0(sK1) | (~spl7_6 | ~spl7_17)),
% 0.22/0.55    inference(resolution,[],[f147,f85])).
% 0.22/0.55  fof(f85,plain,(
% 0.22/0.55    v1_funct_2(sK3,sK0,sK1) | ~spl7_6),
% 0.22/0.55    inference(avatar_component_clause,[],[f83])).
% 0.22/0.55  fof(f147,plain,(
% 0.22/0.55    ( ! [X2,X3] : (~v1_funct_2(sK3,X2,X3) | v1_partfun1(sK3,X2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | v1_xboole_0(X3)) ) | ~spl7_17),
% 0.22/0.55    inference(avatar_component_clause,[],[f146])).
% 0.22/0.55  fof(f322,plain,(
% 0.22/0.55    spl7_38 | ~spl7_28),
% 0.22/0.55    inference(avatar_split_clause,[],[f246,f241,f319])).
% 0.22/0.55  fof(f319,plain,(
% 0.22/0.55    spl7_38 <=> k1_xboole_0 = sK3),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_38])])).
% 0.22/0.55  fof(f241,plain,(
% 0.22/0.55    spl7_28 <=> ! [X0] : ~r2_hidden(X0,sK3)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).
% 0.22/0.55  fof(f246,plain,(
% 0.22/0.55    k1_xboole_0 = sK3 | ~spl7_28),
% 0.22/0.55    inference(resolution,[],[f242,f39])).
% 0.22/0.55  fof(f39,plain,(
% 0.22/0.55    ( ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0) )),
% 0.22/0.55    inference(cnf_transformation,[],[f26])).
% 0.22/0.55  fof(f26,plain,(
% 0.22/0.55    ! [X0] : ((! [X2,X3] : (k4_tarski(X2,X3) != sK4(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK4(X0),X0)) | k1_xboole_0 = X0)),
% 0.22/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f13,f25])).
% 0.22/0.55  fof(f25,plain,(
% 0.22/0.55    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X3,X2] : (k4_tarski(X2,X3) != sK4(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK4(X0),X0)))),
% 0.22/0.55    introduced(choice_axiom,[])).
% 0.22/0.55  fof(f13,plain,(
% 0.22/0.55    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.22/0.55    inference(ennf_transformation,[],[f6])).
% 0.22/0.55  fof(f6,axiom,(
% 0.22/0.55    ! [X0] : ~(! [X1] : ~(! [X2,X3] : ~(k4_tarski(X2,X3) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_mcart_1)).
% 0.22/0.55  fof(f242,plain,(
% 0.22/0.55    ( ! [X0] : (~r2_hidden(X0,sK3)) ) | ~spl7_28),
% 0.22/0.55    inference(avatar_component_clause,[],[f241])).
% 0.22/0.55  fof(f262,plain,(
% 0.22/0.55    spl7_29 | ~spl7_27),
% 0.22/0.55    inference(avatar_split_clause,[],[f244,f236,f259])).
% 0.22/0.55  fof(f259,plain,(
% 0.22/0.55    spl7_29 <=> k1_xboole_0 = sK2),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_29])])).
% 0.22/0.55  fof(f236,plain,(
% 0.22/0.55    spl7_27 <=> ! [X0] : ~r2_hidden(X0,sK2)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).
% 0.22/0.55  fof(f244,plain,(
% 0.22/0.55    k1_xboole_0 = sK2 | ~spl7_27),
% 0.22/0.55    inference(resolution,[],[f237,f39])).
% 0.22/0.55  fof(f237,plain,(
% 0.22/0.55    ( ! [X0] : (~r2_hidden(X0,sK2)) ) | ~spl7_27),
% 0.22/0.55    inference(avatar_component_clause,[],[f236])).
% 0.22/0.55  fof(f243,plain,(
% 0.22/0.55    spl7_28 | ~spl7_26),
% 0.22/0.55    inference(avatar_split_clause,[],[f228,f224,f241])).
% 0.22/0.55  fof(f224,plain,(
% 0.22/0.55    spl7_26 <=> sP5(sK3)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).
% 0.22/0.55  fof(f228,plain,(
% 0.22/0.55    ( ! [X0] : (~r2_hidden(X0,sK3)) ) | ~spl7_26),
% 0.22/0.55    inference(resolution,[],[f226,f54])).
% 0.22/0.55  fof(f54,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~sP5(X1) | ~r2_hidden(X0,X1)) )),
% 0.22/0.55    inference(general_splitting,[],[f49,f53_D])).
% 0.22/0.55  fof(f53,plain,(
% 0.22/0.55    ( ! [X2,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | sP5(X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f53_D])).
% 0.22/0.55  fof(f53_D,plain,(
% 0.22/0.55    ( ! [X1] : (( ! [X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2))) ) <=> ~sP5(X1)) )),
% 0.22/0.55    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP5])])).
% 0.22/0.55  fof(f49,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f19])).
% 0.22/0.55  fof(f19,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.22/0.55    inference(ennf_transformation,[],[f4])).
% 0.22/0.55  fof(f4,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 0.22/0.55  fof(f226,plain,(
% 0.22/0.55    sP5(sK3) | ~spl7_26),
% 0.22/0.55    inference(avatar_component_clause,[],[f224])).
% 0.22/0.55  fof(f238,plain,(
% 0.22/0.55    spl7_27 | ~spl7_24),
% 0.22/0.55    inference(avatar_split_clause,[],[f217,f210,f236])).
% 0.22/0.55  fof(f210,plain,(
% 0.22/0.55    spl7_24 <=> sP5(sK2)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).
% 0.22/0.55  fof(f217,plain,(
% 0.22/0.55    ( ! [X0] : (~r2_hidden(X0,sK2)) ) | ~spl7_24),
% 0.22/0.55    inference(resolution,[],[f212,f54])).
% 0.22/0.55  fof(f212,plain,(
% 0.22/0.55    sP5(sK2) | ~spl7_24),
% 0.22/0.55    inference(avatar_component_clause,[],[f210])).
% 0.22/0.55  fof(f227,plain,(
% 0.22/0.55    spl7_26 | ~spl7_13 | ~spl7_22),
% 0.22/0.55    inference(avatar_split_clause,[],[f216,f196,f121,f224])).
% 0.22/0.55  fof(f121,plain,(
% 0.22/0.55    spl7_13 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | sP5(X0))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 0.22/0.55  fof(f196,plain,(
% 0.22/0.55    spl7_22 <=> m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).
% 0.22/0.55  fof(f216,plain,(
% 0.22/0.55    sP5(sK3) | (~spl7_13 | ~spl7_22)),
% 0.22/0.55    inference(resolution,[],[f198,f122])).
% 0.22/0.55  fof(f122,plain,(
% 0.22/0.55    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | sP5(X0)) ) | ~spl7_13),
% 0.22/0.55    inference(avatar_component_clause,[],[f121])).
% 0.22/0.55  fof(f198,plain,(
% 0.22/0.55    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | ~spl7_22),
% 0.22/0.55    inference(avatar_component_clause,[],[f196])).
% 0.22/0.55  fof(f213,plain,(
% 0.22/0.55    spl7_24 | ~spl7_13 | ~spl7_21),
% 0.22/0.55    inference(avatar_split_clause,[],[f208,f191,f121,f210])).
% 0.22/0.55  fof(f191,plain,(
% 0.22/0.55    spl7_21 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).
% 0.22/0.55  fof(f208,plain,(
% 0.22/0.55    sP5(sK2) | (~spl7_13 | ~spl7_21)),
% 0.22/0.55    inference(resolution,[],[f193,f122])).
% 0.22/0.55  fof(f193,plain,(
% 0.22/0.55    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~spl7_21),
% 0.22/0.55    inference(avatar_component_clause,[],[f191])).
% 0.22/0.55  fof(f199,plain,(
% 0.22/0.55    spl7_22 | ~spl7_9 | ~spl7_11),
% 0.22/0.55    inference(avatar_split_clause,[],[f181,f107,f98,f196])).
% 0.22/0.55  fof(f107,plain,(
% 0.22/0.55    spl7_11 <=> k1_xboole_0 = sK0),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 0.22/0.55  fof(f181,plain,(
% 0.22/0.55    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | (~spl7_9 | ~spl7_11)),
% 0.22/0.55    inference(forward_demodulation,[],[f177,f52])).
% 0.22/0.55  fof(f52,plain,(
% 0.22/0.55    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.22/0.55    inference(equality_resolution,[],[f45])).
% 0.22/0.55  fof(f45,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 0.22/0.55    inference(cnf_transformation,[],[f28])).
% 0.22/0.55  fof(f28,plain,(
% 0.22/0.55    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.22/0.55    inference(flattening,[],[f27])).
% 0.22/0.55  fof(f27,plain,(
% 0.22/0.55    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.22/0.55    inference(nnf_transformation,[],[f3])).
% 0.22/0.55  fof(f3,axiom,(
% 0.22/0.55    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.22/0.55  fof(f177,plain,(
% 0.22/0.55    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) | (~spl7_9 | ~spl7_11)),
% 0.22/0.55    inference(backward_demodulation,[],[f100,f109])).
% 0.22/0.55  fof(f109,plain,(
% 0.22/0.55    k1_xboole_0 = sK0 | ~spl7_11),
% 0.22/0.55    inference(avatar_component_clause,[],[f107])).
% 0.22/0.55  fof(f194,plain,(
% 0.22/0.55    spl7_21 | ~spl7_8 | ~spl7_11),
% 0.22/0.55    inference(avatar_split_clause,[],[f180,f107,f93,f191])).
% 0.22/0.55  fof(f180,plain,(
% 0.22/0.55    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | (~spl7_8 | ~spl7_11)),
% 0.22/0.55    inference(forward_demodulation,[],[f176,f52])).
% 0.22/0.55  fof(f176,plain,(
% 0.22/0.55    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) | (~spl7_8 | ~spl7_11)),
% 0.22/0.55    inference(backward_demodulation,[],[f95,f109])).
% 0.22/0.55  fof(f188,plain,(
% 0.22/0.55    spl7_10 | ~spl7_12 | ~spl7_18),
% 0.22/0.55    inference(avatar_split_clause,[],[f165,f154,f114,f103])).
% 0.22/0.55  fof(f103,plain,(
% 0.22/0.55    spl7_10 <=> k1_xboole_0 = sK1),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 0.22/0.55  fof(f114,plain,(
% 0.22/0.55    spl7_12 <=> ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 0.22/0.55  fof(f165,plain,(
% 0.22/0.55    k1_xboole_0 = sK1 | (~spl7_12 | ~spl7_18)),
% 0.22/0.55    inference(resolution,[],[f156,f115])).
% 0.22/0.55  fof(f115,plain,(
% 0.22/0.55    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) ) | ~spl7_12),
% 0.22/0.55    inference(avatar_component_clause,[],[f114])).
% 0.22/0.55  fof(f156,plain,(
% 0.22/0.55    v1_xboole_0(sK1) | ~spl7_18),
% 0.22/0.55    inference(avatar_component_clause,[],[f154])).
% 0.22/0.55  fof(f161,plain,(
% 0.22/0.55    spl7_18 | spl7_19 | ~spl7_5 | ~spl7_8 | ~spl7_16),
% 0.22/0.55    inference(avatar_split_clause,[],[f150,f142,f93,f78,f158,f154])).
% 0.22/0.55  fof(f78,plain,(
% 0.22/0.55    spl7_5 <=> v1_funct_2(sK2,sK0,sK1)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.22/0.55  fof(f142,plain,(
% 0.22/0.55    spl7_16 <=> ! [X1,X0] : (~v1_funct_2(sK2,X0,X1) | v1_partfun1(sK2,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).
% 0.22/0.55  fof(f150,plain,(
% 0.22/0.55    v1_partfun1(sK2,sK0) | v1_xboole_0(sK1) | (~spl7_5 | ~spl7_8 | ~spl7_16)),
% 0.22/0.55    inference(subsumption_resolution,[],[f149,f95])).
% 0.22/0.55  fof(f149,plain,(
% 0.22/0.55    v1_partfun1(sK2,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | v1_xboole_0(sK1) | (~spl7_5 | ~spl7_16)),
% 0.22/0.55    inference(resolution,[],[f143,f80])).
% 0.22/0.55  fof(f80,plain,(
% 0.22/0.55    v1_funct_2(sK2,sK0,sK1) | ~spl7_5),
% 0.22/0.55    inference(avatar_component_clause,[],[f78])).
% 0.22/0.55  fof(f143,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~v1_funct_2(sK2,X0,X1) | v1_partfun1(sK2,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) ) | ~spl7_16),
% 0.22/0.55    inference(avatar_component_clause,[],[f142])).
% 0.22/0.55  fof(f148,plain,(
% 0.22/0.55    spl7_17 | ~spl7_2),
% 0.22/0.55    inference(avatar_split_clause,[],[f135,f63,f146])).
% 0.22/0.55  fof(f135,plain,(
% 0.22/0.55    ( ! [X2,X3] : (~v1_funct_2(sK3,X2,X3) | v1_partfun1(sK3,X2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | v1_xboole_0(X3)) ) | ~spl7_2),
% 0.22/0.55    inference(resolution,[],[f43,f65])).
% 0.22/0.55  fof(f43,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f15])).
% 0.22/0.55  fof(f15,plain,(
% 0.22/0.55    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.22/0.55    inference(flattening,[],[f14])).
% 0.22/0.55  fof(f14,plain,(
% 0.22/0.55    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.22/0.55    inference(ennf_transformation,[],[f7])).
% 0.22/0.55  fof(f7,axiom,(
% 0.22/0.55    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).
% 0.22/0.55  fof(f144,plain,(
% 0.22/0.55    spl7_16 | ~spl7_1),
% 0.22/0.55    inference(avatar_split_clause,[],[f134,f58,f142])).
% 0.22/0.55  fof(f134,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~v1_funct_2(sK2,X0,X1) | v1_partfun1(sK2,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) ) | ~spl7_1),
% 0.22/0.55    inference(resolution,[],[f43,f60])).
% 0.22/0.55  fof(f140,plain,(
% 0.22/0.55    spl7_15 | ~spl7_9),
% 0.22/0.55    inference(avatar_split_clause,[],[f126,f98,f137])).
% 0.22/0.55  fof(f137,plain,(
% 0.22/0.55    spl7_15 <=> r2_relset_1(sK0,sK1,sK3,sK3)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 0.22/0.55  fof(f126,plain,(
% 0.22/0.55    r2_relset_1(sK0,sK1,sK3,sK3) | ~spl7_9),
% 0.22/0.55    inference(resolution,[],[f124,f100])).
% 0.22/0.55  fof(f124,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X2,X2)) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f55,f56])).
% 0.22/0.55  fof(f56,plain,(
% 0.22/0.55    ( ! [X0,X3,X1] : (~sP6(X1,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.55    inference(general_splitting,[],[f50,f55_D])).
% 0.22/0.55  fof(f50,plain,(
% 0.22/0.55    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f21])).
% 0.22/0.55  fof(f21,plain,(
% 0.22/0.55    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.55    inference(flattening,[],[f20])).
% 0.22/0.55  fof(f20,plain,(
% 0.22/0.55    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.22/0.55    inference(ennf_transformation,[],[f5])).
% 0.22/0.55  fof(f5,axiom,(
% 0.22/0.55    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => r2_relset_1(X0,X1,X2,X2))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).
% 0.22/0.55  fof(f55,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP6(X1,X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f55_D])).
% 0.22/0.55  fof(f55_D,plain,(
% 0.22/0.55    ( ! [X0,X1] : (( ! [X2] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) <=> ~sP6(X1,X0)) )),
% 0.22/0.55    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP6])])).
% 0.22/0.55  fof(f123,plain,(
% 0.22/0.55    spl7_13 | ~spl7_3),
% 0.22/0.55    inference(avatar_split_clause,[],[f112,f68,f121])).
% 0.22/0.55  fof(f68,plain,(
% 0.22/0.55    spl7_3 <=> v1_xboole_0(k1_xboole_0)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.22/0.55  fof(f112,plain,(
% 0.22/0.55    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | sP5(X0)) ) | ~spl7_3),
% 0.22/0.55    inference(resolution,[],[f53,f70])).
% 0.22/0.55  fof(f70,plain,(
% 0.22/0.55    v1_xboole_0(k1_xboole_0) | ~spl7_3),
% 0.22/0.55    inference(avatar_component_clause,[],[f68])).
% 0.22/0.55  fof(f116,plain,(
% 0.22/0.55    spl7_12 | ~spl7_3),
% 0.22/0.55    inference(avatar_split_clause,[],[f111,f68,f114])).
% 0.22/0.55  fof(f111,plain,(
% 0.22/0.55    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) ) | ~spl7_3),
% 0.22/0.55    inference(resolution,[],[f47,f70])).
% 0.22/0.55  fof(f47,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~v1_xboole_0(X0) | X0 = X1 | ~v1_xboole_0(X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f16])).
% 0.22/0.55  fof(f16,plain,(
% 0.22/0.55    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 0.22/0.55    inference(ennf_transformation,[],[f2])).
% 0.22/0.55  fof(f2,axiom,(
% 0.22/0.55    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).
% 0.22/0.55  fof(f110,plain,(
% 0.22/0.55    ~spl7_10 | spl7_11),
% 0.22/0.55    inference(avatar_split_clause,[],[f36,f107,f103])).
% 0.22/0.55  fof(f36,plain,(
% 0.22/0.55    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 0.22/0.55    inference(cnf_transformation,[],[f24])).
% 0.22/0.55  fof(f24,plain,(
% 0.22/0.55    (~r2_relset_1(sK0,sK1,sK2,sK3) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_partfun1(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 0.22/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f12,f23,f22])).
% 0.22/0.55  fof(f22,plain,(
% 0.22/0.55    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_partfun1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (~r2_relset_1(sK0,sK1,sK2,X3) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_partfun1(sK2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(X3,sK0,sK1) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 0.22/0.55    introduced(choice_axiom,[])).
% 0.22/0.55  fof(f23,plain,(
% 0.22/0.55    ? [X3] : (~r2_relset_1(sK0,sK1,sK2,X3) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_partfun1(sK2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(X3,sK0,sK1) & v1_funct_1(X3)) => (~r2_relset_1(sK0,sK1,sK2,sK3) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_partfun1(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 0.22/0.55    introduced(choice_axiom,[])).
% 0.22/0.55  fof(f12,plain,(
% 0.22/0.55    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_partfun1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.22/0.55    inference(flattening,[],[f11])).
% 0.22/0.55  fof(f11,plain,(
% 0.22/0.55    ? [X0,X1,X2] : (? [X3] : (((~r2_relset_1(X0,X1,X2,X3) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_partfun1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.22/0.55    inference(ennf_transformation,[],[f10])).
% 0.22/0.55  fof(f10,negated_conjecture,(
% 0.22/0.55    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_partfun1(X2,X3) => (r2_relset_1(X0,X1,X2,X3) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)))))),
% 0.22/0.55    inference(negated_conjecture,[],[f9])).
% 0.22/0.55  fof(f9,conjecture,(
% 0.22/0.55    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_partfun1(X2,X3) => (r2_relset_1(X0,X1,X2,X3) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)))))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_2)).
% 0.22/0.55  fof(f101,plain,(
% 0.22/0.55    spl7_9),
% 0.22/0.55    inference(avatar_split_clause,[],[f34,f98])).
% 0.22/0.55  fof(f34,plain,(
% 0.22/0.55    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.55    inference(cnf_transformation,[],[f24])).
% 0.22/0.55  fof(f96,plain,(
% 0.22/0.55    spl7_8),
% 0.22/0.55    inference(avatar_split_clause,[],[f31,f93])).
% 0.22/0.55  fof(f31,plain,(
% 0.22/0.55    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.55    inference(cnf_transformation,[],[f24])).
% 0.22/0.55  fof(f91,plain,(
% 0.22/0.55    ~spl7_7),
% 0.22/0.55    inference(avatar_split_clause,[],[f37,f88])).
% 0.22/0.55  fof(f88,plain,(
% 0.22/0.55    spl7_7 <=> r2_relset_1(sK0,sK1,sK2,sK3)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.22/0.55  fof(f37,plain,(
% 0.22/0.55    ~r2_relset_1(sK0,sK1,sK2,sK3)),
% 0.22/0.55    inference(cnf_transformation,[],[f24])).
% 0.22/0.55  fof(f86,plain,(
% 0.22/0.55    spl7_6),
% 0.22/0.55    inference(avatar_split_clause,[],[f33,f83])).
% 0.22/0.55  fof(f33,plain,(
% 0.22/0.55    v1_funct_2(sK3,sK0,sK1)),
% 0.22/0.55    inference(cnf_transformation,[],[f24])).
% 0.22/0.55  fof(f81,plain,(
% 0.22/0.55    spl7_5),
% 0.22/0.55    inference(avatar_split_clause,[],[f30,f78])).
% 0.22/0.55  fof(f30,plain,(
% 0.22/0.55    v1_funct_2(sK2,sK0,sK1)),
% 0.22/0.55    inference(cnf_transformation,[],[f24])).
% 0.22/0.55  fof(f76,plain,(
% 0.22/0.55    spl7_4),
% 0.22/0.55    inference(avatar_split_clause,[],[f35,f73])).
% 0.22/0.55  fof(f35,plain,(
% 0.22/0.55    r1_partfun1(sK2,sK3)),
% 0.22/0.55    inference(cnf_transformation,[],[f24])).
% 0.22/0.55  fof(f71,plain,(
% 0.22/0.55    spl7_3),
% 0.22/0.55    inference(avatar_split_clause,[],[f38,f68])).
% 0.22/0.55  fof(f38,plain,(
% 0.22/0.55    v1_xboole_0(k1_xboole_0)),
% 0.22/0.55    inference(cnf_transformation,[],[f1])).
% 0.22/0.55  fof(f1,axiom,(
% 0.22/0.55    v1_xboole_0(k1_xboole_0)),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.55  fof(f66,plain,(
% 0.22/0.55    spl7_2),
% 0.22/0.55    inference(avatar_split_clause,[],[f32,f63])).
% 0.22/0.55  fof(f32,plain,(
% 0.22/0.55    v1_funct_1(sK3)),
% 0.22/0.55    inference(cnf_transformation,[],[f24])).
% 0.22/0.55  fof(f61,plain,(
% 0.22/0.55    spl7_1),
% 0.22/0.55    inference(avatar_split_clause,[],[f29,f58])).
% 0.22/0.55  fof(f29,plain,(
% 0.22/0.55    v1_funct_1(sK2)),
% 0.22/0.55    inference(cnf_transformation,[],[f24])).
% 0.22/0.55  % SZS output end Proof for theBenchmark
% 0.22/0.55  % (3846)------------------------------
% 0.22/0.55  % (3846)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (3846)Termination reason: Refutation
% 0.22/0.55  
% 0.22/0.55  % (3846)Memory used [KB]: 6396
% 0.22/0.55  % (3846)Time elapsed: 0.096 s
% 0.22/0.55  % (3846)------------------------------
% 0.22/0.55  % (3846)------------------------------
% 0.22/0.56  % (3839)Success in time 0.188 s
%------------------------------------------------------------------------------
