%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:12 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  220 (1176 expanded)
%              Number of leaves         :   30 ( 304 expanded)
%              Depth                    :   27
%              Number of atoms          :  764 (5543 expanded)
%              Number of equality atoms :  117 ( 808 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2181,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f112,f120,f882,f892,f943,f1314,f1493,f1503,f2076,f2085,f2180])).

fof(f2180,plain,
    ( ~ spl7_7
    | spl7_15
    | ~ spl7_17 ),
    inference(avatar_contradiction_clause,[],[f2179])).

fof(f2179,plain,
    ( $false
    | ~ spl7_7
    | spl7_15
    | ~ spl7_17 ),
    inference(subsumption_resolution,[],[f2175,f99])).

fof(f99,plain,(
    ! [X1] : ~ sP1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP1(X0,X1) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP1(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f2175,plain,
    ( sP1(k1_xboole_0,k1_xboole_0)
    | ~ spl7_7
    | spl7_15
    | ~ spl7_17 ),
    inference(backward_demodulation,[],[f1022,f2115])).

fof(f2115,plain,
    ( k1_xboole_0 = sK4
    | ~ spl7_7
    | spl7_15 ),
    inference(subsumption_resolution,[],[f2114,f901])).

fof(f901,plain,
    ( k1_xboole_0 != sK6
    | spl7_15 ),
    inference(avatar_component_clause,[],[f900])).

fof(f900,plain,
    ( spl7_15
  <=> k1_xboole_0 = sK6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f2114,plain,
    ( k1_xboole_0 = sK4
    | k1_xboole_0 = sK6
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f2113,f1533])).

fof(f1533,plain,
    ( v1_funct_2(sK6,sK4,k1_xboole_0)
    | ~ spl7_7 ),
    inference(backward_demodulation,[],[f57,f356])).

fof(f356,plain,
    ( k1_xboole_0 = sK5
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f354])).

fof(f354,plain,
    ( spl7_7
  <=> k1_xboole_0 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f57,plain,(
    v1_funct_2(sK6,sK4,sK5) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
      | ~ v1_funct_2(k2_funct_1(sK6),sK5,sK4)
      | ~ v1_funct_1(k2_funct_1(sK6)) )
    & sK5 = k2_relset_1(sK4,sK5,sK6)
    & v2_funct_1(sK6)
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    & v1_funct_2(sK6,sK4,sK5)
    & v1_funct_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f19,f44])).

fof(f44,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
          | ~ v1_funct_1(k2_funct_1(X2)) )
        & k2_relset_1(X0,X1,X2) = X1
        & v2_funct_1(X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ( ~ m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
        | ~ v1_funct_2(k2_funct_1(sK6),sK5,sK4)
        | ~ v1_funct_1(k2_funct_1(sK6)) )
      & sK5 = k2_relset_1(sK4,sK5,sK6)
      & v2_funct_1(sK6)
      & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
      & v1_funct_2(sK6,sK4,sK5)
      & v1_funct_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

fof(f2113,plain,
    ( ~ v1_funct_2(sK6,sK4,k1_xboole_0)
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK6
    | ~ spl7_7 ),
    inference(resolution,[],[f1542,f98])).

fof(f98,plain,(
    ! [X2,X0] :
      ( ~ sP3(X0,k1_xboole_0,X2)
      | ~ v1_funct_2(X0,X2,k1_xboole_0)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | ~ v1_funct_2(X0,X2,X1)
      | k1_xboole_0 = X2
      | k1_xboole_0 != X1
      | ~ sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X0,X2,X1)
          | k1_xboole_0 != X0 )
        & ( k1_xboole_0 = X0
          | ~ v1_funct_2(X0,X2,X1) ) )
      | k1_xboole_0 = X2
      | k1_xboole_0 != X1
      | ~ sP3(X0,X1,X2) ) ),
    inference(rectify,[],[f51])).

fof(f51,plain,(
    ! [X2,X1,X0] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_xboole_0 != X2 )
        & ( k1_xboole_0 = X2
          | ~ v1_funct_2(X2,X0,X1) ) )
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ sP3(X2,X1,X0) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X2,X1,X0] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_xboole_0 = X2 )
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ sP3(X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f1542,plain,
    ( sP3(sK6,k1_xboole_0,sK4)
    | ~ spl7_7 ),
    inference(backward_demodulation,[],[f187,f356])).

fof(f187,plain,(
    sP3(sK6,sK5,sK4) ),
    inference(resolution,[],[f93,f58])).

fof(f58,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f45])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP3(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( sP3(X2,X1,X0)
        & sP2(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f37,f42,f41,f40])).

fof(f41,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | sP1(X0,X1)
      | ~ sP2(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f36,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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

% (16474)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
fof(f1022,plain,
    ( sP1(sK4,k1_xboole_0)
    | ~ spl7_7
    | ~ spl7_17 ),
    inference(backward_demodulation,[],[f918,f356])).

fof(f918,plain,
    ( sP1(sK4,sK5)
    | ~ spl7_17 ),
    inference(avatar_component_clause,[],[f916])).

fof(f916,plain,
    ( spl7_17
  <=> sP1(sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f2085,plain,
    ( ~ spl7_7
    | spl7_11
    | ~ spl7_15 ),
    inference(avatar_contradiction_clause,[],[f2084])).

fof(f2084,plain,
    ( $false
    | ~ spl7_7
    | spl7_11
    | ~ spl7_15 ),
    inference(subsumption_resolution,[],[f2083,f122])).

fof(f122,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f118,f62])).

fof(f62,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
      | v1_relat_1(X0) ) ),
    inference(resolution,[],[f81,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f2083,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ spl7_7
    | spl7_11
    | ~ spl7_15 ),
    inference(subsumption_resolution,[],[f2082,f1555])).

fof(f1555,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl7_15 ),
    inference(backward_demodulation,[],[f56,f902])).

fof(f902,plain,
    ( k1_xboole_0 = sK6
    | ~ spl7_15 ),
    inference(avatar_component_clause,[],[f900])).

fof(f56,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f45])).

fof(f2082,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl7_7
    | spl7_11
    | ~ spl7_15 ),
    inference(subsumption_resolution,[],[f2081,f1556])).

fof(f1556,plain,
    ( v2_funct_1(k1_xboole_0)
    | ~ spl7_15 ),
    inference(backward_demodulation,[],[f59,f902])).

fof(f59,plain,(
    v2_funct_1(sK6) ),
    inference(cnf_transformation,[],[f45])).

fof(f2081,plain,
    ( ~ v2_funct_1(k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl7_7
    | spl7_11
    | ~ spl7_15 ),
    inference(subsumption_resolution,[],[f2069,f1560])).

fof(f1560,plain,
    ( ~ v5_relat_1(k2_funct_1(k1_xboole_0),k1_xboole_0)
    | spl7_11
    | ~ spl7_15 ),
    inference(backward_demodulation,[],[f877,f902])).

fof(f877,plain,
    ( ~ v5_relat_1(k2_funct_1(sK6),k1_xboole_0)
    | spl7_11 ),
    inference(avatar_component_clause,[],[f875])).

fof(f875,plain,
    ( spl7_11
  <=> v5_relat_1(k2_funct_1(sK6),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f2069,plain,
    ( v5_relat_1(k2_funct_1(k1_xboole_0),k1_xboole_0)
    | ~ v2_funct_1(k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl7_7
    | ~ spl7_15 ),
    inference(superposition,[],[f277,f2051])).

fof(f2051,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl7_7
    | ~ spl7_15 ),
    inference(resolution,[],[f2045,f94])).

fof(f94,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f2045,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_relat_1(k1_xboole_0))
        | k1_xboole_0 = X0 )
    | ~ spl7_7
    | ~ spl7_15 ),
    inference(resolution,[],[f2023,f62])).

fof(f2023,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X1,k1_relat_1(k1_xboole_0))
        | X0 = X1
        | ~ r1_tarski(X0,k1_relat_1(k1_xboole_0)) )
    | ~ spl7_7
    | ~ spl7_15 ),
    inference(superposition,[],[f2021,f2021])).

fof(f2021,plain,
    ( ! [X0] :
        ( k10_relat_1(k1_xboole_0,k1_xboole_0) = X0
        | ~ r1_tarski(X0,k1_relat_1(k1_xboole_0)) )
    | ~ spl7_7
    | ~ spl7_15 ),
    inference(subsumption_resolution,[],[f2020,f122])).

fof(f2020,plain,
    ( ! [X0] :
        ( k10_relat_1(k1_xboole_0,k1_xboole_0) = X0
        | ~ r1_tarski(X0,k1_relat_1(k1_xboole_0))
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl7_7
    | ~ spl7_15 ),
    inference(subsumption_resolution,[],[f2019,f1555])).

fof(f2019,plain,
    ( ! [X0] :
        ( k10_relat_1(k1_xboole_0,k1_xboole_0) = X0
        | ~ r1_tarski(X0,k1_relat_1(k1_xboole_0))
        | ~ v1_funct_1(k1_xboole_0)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl7_7
    | ~ spl7_15 ),
    inference(subsumption_resolution,[],[f2011,f1556])).

fof(f2011,plain,
    ( ! [X0] :
        ( k10_relat_1(k1_xboole_0,k1_xboole_0) = X0
        | ~ v2_funct_1(k1_xboole_0)
        | ~ r1_tarski(X0,k1_relat_1(k1_xboole_0))
        | ~ v1_funct_1(k1_xboole_0)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl7_7
    | ~ spl7_15 ),
    inference(superposition,[],[f74,f2001])).

fof(f2001,plain,
    ( ! [X1] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X1)
    | ~ spl7_7
    | ~ spl7_15 ),
    inference(resolution,[],[f1998,f128])).

fof(f128,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f78,f62])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f1998,plain,
    ( ! [X2] : r1_tarski(k9_relat_1(k1_xboole_0,X2),k1_xboole_0)
    | ~ spl7_7
    | ~ spl7_15 ),
    inference(subsumption_resolution,[],[f1997,f147])).

fof(f147,plain,(
    ! [X0] : v4_relat_1(k1_xboole_0,X0) ),
    inference(resolution,[],[f145,f62])).

fof(f145,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
      | v4_relat_1(X0,X1) ) ),
    inference(resolution,[],[f84,f80])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f1997,plain,
    ( ! [X2] :
        ( r1_tarski(k9_relat_1(k1_xboole_0,X2),k1_xboole_0)
        | ~ v4_relat_1(k1_xboole_0,X2) )
    | ~ spl7_7
    | ~ spl7_15 ),
    inference(subsumption_resolution,[],[f1989,f122])).

fof(f1989,plain,
    ( ! [X2] :
        ( r1_tarski(k9_relat_1(k1_xboole_0,X2),k1_xboole_0)
        | ~ v1_relat_1(k1_xboole_0)
        | ~ v4_relat_1(k1_xboole_0,X2) )
    | ~ spl7_7
    | ~ spl7_15 ),
    inference(superposition,[],[f1978,f1572])).

fof(f1572,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl7_7
    | ~ spl7_15 ),
    inference(forward_demodulation,[],[f1543,f902])).

fof(f1543,plain,
    ( k1_xboole_0 = k2_relat_1(sK6)
    | ~ spl7_7 ),
    inference(backward_demodulation,[],[f338,f356])).

fof(f338,plain,(
    sK5 = k2_relat_1(sK6) ),
    inference(subsumption_resolution,[],[f336,f58])).

fof(f336,plain,
    ( sK5 = k2_relat_1(sK6)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(superposition,[],[f83,f60])).

fof(f60,plain,(
    sK5 = k2_relset_1(sK4,sK5,sK6) ),
    inference(cnf_transformation,[],[f45])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f1978,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | ~ v4_relat_1(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f1973])).

fof(f1973,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v4_relat_1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f812,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(f812,plain,(
    ! [X4,X3] :
      ( r1_tarski(k9_relat_1(X3,X4),k2_relat_1(k7_relat_1(X3,X4)))
      | ~ v1_relat_1(k7_relat_1(X3,X4))
      | ~ v1_relat_1(X3) ) ),
    inference(duplicate_literal_removal,[],[f807])).

fof(f807,plain,(
    ! [X4,X3] :
      ( r1_tarski(k9_relat_1(X3,X4),k2_relat_1(k7_relat_1(X3,X4)))
      | ~ v1_relat_1(k7_relat_1(X3,X4))
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(k7_relat_1(X3,X4)) ) ),
    inference(resolution,[],[f167,f125])).

fof(f125,plain,(
    ! [X0] :
      ( v5_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f69,f94])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f25])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f167,plain,(
    ! [X8,X7,X9] :
      ( ~ v5_relat_1(k7_relat_1(X7,X8),X9)
      | r1_tarski(k9_relat_1(X7,X8),X9)
      | ~ v1_relat_1(k7_relat_1(X7,X8))
      | ~ v1_relat_1(X7) ) ),
    inference(superposition,[],[f68,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( v2_funct_1(X1)
          & r1_tarski(X0,k1_relat_1(X1)) )
       => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t164_funct_1)).

fof(f277,plain,(
    ! [X6] :
      ( v5_relat_1(k2_funct_1(X6),k1_relat_1(X6))
      | ~ v2_funct_1(X6)
      | ~ v1_funct_1(X6)
      | ~ v1_relat_1(X6) ) ),
    inference(subsumption_resolution,[],[f268,f63])).

fof(f63,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f268,plain,(
    ! [X6] :
      ( v5_relat_1(k2_funct_1(X6),k1_relat_1(X6))
      | ~ v1_relat_1(k2_funct_1(X6))
      | ~ v2_funct_1(X6)
      | ~ v1_funct_1(X6)
      | ~ v1_relat_1(X6) ) ),
    inference(superposition,[],[f125,f66])).

fof(f66,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f2076,plain,
    ( spl7_3
    | ~ spl7_7
    | ~ spl7_15 ),
    inference(avatar_contradiction_clause,[],[f2075])).

fof(f2075,plain,
    ( $false
    | spl7_3
    | ~ spl7_7
    | ~ spl7_15 ),
    inference(subsumption_resolution,[],[f2057,f62])).

fof(f2057,plain,
    ( ~ r1_tarski(k1_xboole_0,sK4)
    | spl7_3
    | ~ spl7_7
    | ~ spl7_15 ),
    inference(backward_demodulation,[],[f1777,f2051])).

fof(f1777,plain,
    ( ~ r1_tarski(k1_relat_1(k1_xboole_0),sK4)
    | spl7_3
    | ~ spl7_15 ),
    inference(subsumption_resolution,[],[f1776,f122])).

fof(f1776,plain,
    ( ~ r1_tarski(k1_relat_1(k1_xboole_0),sK4)
    | ~ v1_relat_1(k1_xboole_0)
    | spl7_3
    | ~ spl7_15 ),
    inference(subsumption_resolution,[],[f1775,f1555])).

fof(f1775,plain,
    ( ~ r1_tarski(k1_relat_1(k1_xboole_0),sK4)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | spl7_3
    | ~ spl7_15 ),
    inference(subsumption_resolution,[],[f1772,f1556])).

fof(f1772,plain,
    ( ~ r1_tarski(k1_relat_1(k1_xboole_0),sK4)
    | ~ v2_funct_1(k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | spl7_3
    | ~ spl7_15 ),
    inference(resolution,[],[f1581,f276])).

fof(f276,plain,(
    ! [X4,X5] :
      ( sP0(X5,k2_funct_1(X4))
      | ~ r1_tarski(k1_relat_1(X4),X5)
      | ~ v2_funct_1(X4)
      | ~ v1_funct_1(X4)
      | ~ v1_relat_1(X4) ) ),
    inference(subsumption_resolution,[],[f275,f63])).

fof(f275,plain,(
    ! [X4,X5] :
      ( ~ r1_tarski(k1_relat_1(X4),X5)
      | sP0(X5,k2_funct_1(X4))
      | ~ v1_relat_1(k2_funct_1(X4))
      | ~ v2_funct_1(X4)
      | ~ v1_funct_1(X4)
      | ~ v1_relat_1(X4) ) ),
    inference(subsumption_resolution,[],[f267,f64])).

fof(f64,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f267,plain,(
    ! [X4,X5] :
      ( ~ r1_tarski(k1_relat_1(X4),X5)
      | sP0(X5,k2_funct_1(X4))
      | ~ v1_funct_1(k2_funct_1(X4))
      | ~ v1_relat_1(k2_funct_1(X4))
      | ~ v2_funct_1(X4)
      | ~ v1_funct_1(X4)
      | ~ v1_relat_1(X4) ) ),
    inference(superposition,[],[f73,f66])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | sP0(X0,X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_folding,[],[f27,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ sP0(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

fof(f1581,plain,
    ( ~ sP0(sK4,k2_funct_1(k1_xboole_0))
    | spl7_3
    | ~ spl7_15 ),
    inference(forward_demodulation,[],[f1304,f902])).

fof(f1304,plain,
    ( ~ sP0(sK4,k2_funct_1(sK6))
    | spl7_3 ),
    inference(resolution,[],[f1272,f111])).

fof(f111,plain,
    ( ~ m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
    | spl7_3 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl7_3
  <=> m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f1272,plain,(
    ! [X8] :
      ( m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,X8)))
      | ~ sP0(X8,k2_funct_1(sK6)) ) ),
    inference(subsumption_resolution,[],[f1271,f117])).

fof(f117,plain,(
    v1_relat_1(sK6) ),
    inference(resolution,[],[f81,f58])).

fof(f1271,plain,(
    ! [X8] :
      ( m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,X8)))
      | ~ sP0(X8,k2_funct_1(sK6))
      | ~ v1_relat_1(sK6) ) ),
    inference(subsumption_resolution,[],[f1270,f56])).

fof(f1270,plain,(
    ! [X8] :
      ( m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,X8)))
      | ~ sP0(X8,k2_funct_1(sK6))
      | ~ v1_funct_1(sK6)
      | ~ v1_relat_1(sK6) ) ),
    inference(subsumption_resolution,[],[f1266,f59])).

fof(f1266,plain,(
    ! [X8] :
      ( m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,X8)))
      | ~ sP0(X8,k2_funct_1(sK6))
      | ~ v2_funct_1(sK6)
      | ~ v1_funct_1(sK6)
      | ~ v1_relat_1(sK6) ) ),
    inference(superposition,[],[f241,f338])).

fof(f241,plain,(
    ! [X8,X9] :
      ( m1_subset_1(k2_funct_1(X8),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X8),X9)))
      | ~ sP0(X9,k2_funct_1(X8))
      | ~ v2_funct_1(X8)
      | ~ v1_funct_1(X8)
      | ~ v1_relat_1(X8) ) ),
    inference(superposition,[],[f72,f65])).

fof(f65,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f72,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ sP0(X0,X1) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f1503,plain,
    ( spl7_7
    | ~ spl7_17 ),
    inference(avatar_split_clause,[],[f1502,f916,f354])).

fof(f1502,plain,
    ( k1_xboole_0 = sK5
    | ~ spl7_17 ),
    inference(resolution,[],[f918,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f55])).

fof(f1493,plain,
    ( spl7_16
    | spl7_17 ),
    inference(avatar_split_clause,[],[f1077,f916,f912])).

fof(f912,plain,
    ( spl7_16
  <=> sK4 = k1_relat_1(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f1077,plain,
    ( sP1(sK4,sK5)
    | sK4 = k1_relat_1(sK6) ),
    inference(subsumption_resolution,[],[f1070,f57])).

fof(f1070,plain,
    ( ~ v1_funct_2(sK6,sK4,sK5)
    | sP1(sK4,sK5)
    | sK4 = k1_relat_1(sK6) ),
    inference(resolution,[],[f58,f471])).

fof(f471,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_2(X5,X3,X4)
      | sP1(X3,X4)
      | k1_relat_1(X5) = X3 ) ),
    inference(subsumption_resolution,[],[f469,f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP2(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f469,plain,(
    ! [X4,X5,X3] :
      ( k1_relat_1(X5) = X3
      | ~ v1_funct_2(X5,X3,X4)
      | sP1(X3,X4)
      | ~ sP2(X3,X5,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ) ),
    inference(superposition,[],[f88,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X2,X1) = X0
      | ~ v1_funct_2(X1,X0,X2)
      | sP1(X0,X2)
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | sP1(X0,X2)
      | ~ sP2(X0,X1,X2) ) ),
    inference(rectify,[],[f53])).

fof(f53,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | sP1(X0,X1)
      | ~ sP2(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f1314,plain,
    ( spl7_3
    | ~ spl7_16 ),
    inference(avatar_contradiction_clause,[],[f1313])).

fof(f1313,plain,
    ( $false
    | spl7_3
    | ~ spl7_16 ),
    inference(subsumption_resolution,[],[f1304,f949])).

fof(f949,plain,
    ( sP0(sK4,k2_funct_1(sK6))
    | ~ spl7_16 ),
    inference(subsumption_resolution,[],[f948,f117])).

fof(f948,plain,
    ( sP0(sK4,k2_funct_1(sK6))
    | ~ v1_relat_1(sK6)
    | ~ spl7_16 ),
    inference(subsumption_resolution,[],[f947,f56])).

fof(f947,plain,
    ( sP0(sK4,k2_funct_1(sK6))
    | ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6)
    | ~ spl7_16 ),
    inference(subsumption_resolution,[],[f929,f59])).

fof(f929,plain,
    ( sP0(sK4,k2_funct_1(sK6))
    | ~ v2_funct_1(sK6)
    | ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6)
    | ~ spl7_16 ),
    inference(superposition,[],[f280,f914])).

fof(f914,plain,
    ( sK4 = k1_relat_1(sK6)
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f912])).

fof(f280,plain,(
    ! [X8] :
      ( sP0(k1_relat_1(X8),k2_funct_1(X8))
      | ~ v2_funct_1(X8)
      | ~ v1_funct_1(X8)
      | ~ v1_relat_1(X8) ) ),
    inference(subsumption_resolution,[],[f279,f63])).

fof(f279,plain,(
    ! [X8] :
      ( sP0(k1_relat_1(X8),k2_funct_1(X8))
      | ~ v1_relat_1(k2_funct_1(X8))
      | ~ v2_funct_1(X8)
      | ~ v1_funct_1(X8)
      | ~ v1_relat_1(X8) ) ),
    inference(subsumption_resolution,[],[f270,f64])).

fof(f270,plain,(
    ! [X8] :
      ( sP0(k1_relat_1(X8),k2_funct_1(X8))
      | ~ v1_funct_1(k2_funct_1(X8))
      | ~ v1_relat_1(k2_funct_1(X8))
      | ~ v2_funct_1(X8)
      | ~ v1_funct_1(X8)
      | ~ v1_relat_1(X8) ) ),
    inference(superposition,[],[f201,f66])).

fof(f201,plain,(
    ! [X0] :
      ( sP0(k2_relat_1(X0),X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f73,f94])).

fof(f943,plain,
    ( spl7_2
    | ~ spl7_16 ),
    inference(avatar_contradiction_clause,[],[f942])).

fof(f942,plain,
    ( $false
    | spl7_2
    | ~ spl7_16 ),
    inference(subsumption_resolution,[],[f941,f117])).

fof(f941,plain,
    ( ~ v1_relat_1(sK6)
    | spl7_2
    | ~ spl7_16 ),
    inference(subsumption_resolution,[],[f940,f56])).

fof(f940,plain,
    ( ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6)
    | spl7_2
    | ~ spl7_16 ),
    inference(subsumption_resolution,[],[f939,f59])).

fof(f939,plain,
    ( ~ v2_funct_1(sK6)
    | ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6)
    | spl7_2
    | ~ spl7_16 ),
    inference(subsumption_resolution,[],[f929,f866])).

fof(f866,plain,
    ( ~ sP0(sK4,k2_funct_1(sK6))
    | spl7_2 ),
    inference(resolution,[],[f865,f107])).

fof(f107,plain,
    ( ~ v1_funct_2(k2_funct_1(sK6),sK5,sK4)
    | spl7_2 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl7_2
  <=> v1_funct_2(k2_funct_1(sK6),sK5,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f865,plain,(
    ! [X7] :
      ( v1_funct_2(k2_funct_1(sK6),sK5,X7)
      | ~ sP0(X7,k2_funct_1(sK6)) ) ),
    inference(subsumption_resolution,[],[f864,f117])).

fof(f864,plain,(
    ! [X7] :
      ( v1_funct_2(k2_funct_1(sK6),sK5,X7)
      | ~ sP0(X7,k2_funct_1(sK6))
      | ~ v1_relat_1(sK6) ) ),
    inference(subsumption_resolution,[],[f863,f56])).

fof(f863,plain,(
    ! [X7] :
      ( v1_funct_2(k2_funct_1(sK6),sK5,X7)
      | ~ sP0(X7,k2_funct_1(sK6))
      | ~ v1_funct_1(sK6)
      | ~ v1_relat_1(sK6) ) ),
    inference(subsumption_resolution,[],[f859,f59])).

fof(f859,plain,(
    ! [X7] :
      ( v1_funct_2(k2_funct_1(sK6),sK5,X7)
      | ~ sP0(X7,k2_funct_1(sK6))
      | ~ v2_funct_1(sK6)
      | ~ v1_funct_1(sK6)
      | ~ v1_relat_1(sK6) ) ),
    inference(superposition,[],[f242,f338])).

fof(f242,plain,(
    ! [X10,X11] :
      ( v1_funct_2(k2_funct_1(X10),k2_relat_1(X10),X11)
      | ~ sP0(X11,k2_funct_1(X10))
      | ~ v2_funct_1(X10)
      | ~ v1_funct_1(X10)
      | ~ v1_relat_1(X10) ) ),
    inference(superposition,[],[f71,f65])).

fof(f71,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f892,plain,(
    spl7_12 ),
    inference(avatar_contradiction_clause,[],[f891])).

fof(f891,plain,
    ( $false
    | spl7_12 ),
    inference(subsumption_resolution,[],[f890,f117])).

fof(f890,plain,
    ( ~ v1_relat_1(sK6)
    | spl7_12 ),
    inference(subsumption_resolution,[],[f889,f56])).

fof(f889,plain,
    ( ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6)
    | spl7_12 ),
    inference(resolution,[],[f881,f63])).

fof(f881,plain,
    ( ~ v1_relat_1(k2_funct_1(sK6))
    | spl7_12 ),
    inference(avatar_component_clause,[],[f879])).

fof(f879,plain,
    ( spl7_12
  <=> v1_relat_1(k2_funct_1(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f882,plain,
    ( ~ spl7_11
    | ~ spl7_12
    | ~ spl7_1
    | spl7_2 ),
    inference(avatar_split_clause,[],[f873,f105,f101,f879,f875])).

fof(f101,plain,
    ( spl7_1
  <=> v1_funct_1(k2_funct_1(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f873,plain,
    ( ~ v1_relat_1(k2_funct_1(sK6))
    | ~ v5_relat_1(k2_funct_1(sK6),k1_xboole_0)
    | ~ spl7_1
    | spl7_2 ),
    inference(subsumption_resolution,[],[f868,f102])).

fof(f102,plain,
    ( v1_funct_1(k2_funct_1(sK6))
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f101])).

fof(f868,plain,
    ( ~ v1_funct_1(k2_funct_1(sK6))
    | ~ v1_relat_1(k2_funct_1(sK6))
    | ~ v5_relat_1(k2_funct_1(sK6),k1_xboole_0)
    | spl7_2 ),
    inference(resolution,[],[f866,f208])).

fof(f208,plain,(
    ! [X0,X1] :
      ( sP0(X1,X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v5_relat_1(X0,k1_xboole_0) ) ),
    inference(subsumption_resolution,[],[f206,f62])).

fof(f206,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_xboole_0,X1)
      | sP0(X1,X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v5_relat_1(X0,k1_xboole_0) ) ),
    inference(duplicate_literal_removal,[],[f204])).

fof(f204,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_xboole_0,X1)
      | sP0(X1,X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v5_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f73,f143])).

fof(f143,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_relat_1(X0)
      | ~ v5_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f128,f68])).

fof(f120,plain,(
    spl7_1 ),
    inference(avatar_contradiction_clause,[],[f119])).

fof(f119,plain,
    ( $false
    | spl7_1 ),
    inference(subsumption_resolution,[],[f117,f114])).

fof(f114,plain,
    ( ~ v1_relat_1(sK6)
    | spl7_1 ),
    inference(subsumption_resolution,[],[f113,f56])).

fof(f113,plain,
    ( ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6)
    | spl7_1 ),
    inference(resolution,[],[f64,f103])).

fof(f103,plain,
    ( ~ v1_funct_1(k2_funct_1(sK6))
    | spl7_1 ),
    inference(avatar_component_clause,[],[f101])).

fof(f112,plain,
    ( ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f61,f109,f105,f101])).

fof(f61,plain,
    ( ~ m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
    | ~ v1_funct_2(k2_funct_1(sK6),sK5,sK4)
    | ~ v1_funct_1(k2_funct_1(sK6)) ),
    inference(cnf_transformation,[],[f45])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:22:29 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.45  % (16460)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.47  % (16459)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.48  % (16481)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.48  % (16467)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.49  % (16466)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.50  % (16464)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.50  % (16458)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.50  % (16455)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.51  % (16479)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.51  % (16465)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.51  % (16475)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.51  % (16470)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.51  % (16477)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.52  % (16457)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.52  % (16473)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.52  % (16462)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.52  % (16463)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.53  % (16456)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (16459)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % (16480)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.53  % (16476)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.53  % (16469)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.53  % (16471)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.53  % (16461)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.54  % (16468)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f2181,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(avatar_sat_refutation,[],[f112,f120,f882,f892,f943,f1314,f1493,f1503,f2076,f2085,f2180])).
% 0.21/0.54  fof(f2180,plain,(
% 0.21/0.54    ~spl7_7 | spl7_15 | ~spl7_17),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f2179])).
% 0.21/0.54  fof(f2179,plain,(
% 0.21/0.54    $false | (~spl7_7 | spl7_15 | ~spl7_17)),
% 0.21/0.54    inference(subsumption_resolution,[],[f2175,f99])).
% 0.21/0.54  fof(f99,plain,(
% 0.21/0.54    ( ! [X1] : (~sP1(k1_xboole_0,X1)) )),
% 0.21/0.54    inference(equality_resolution,[],[f91])).
% 0.21/0.54  fof(f91,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k1_xboole_0 != X0 | ~sP1(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f55])).
% 0.21/0.54  fof(f55,plain,(
% 0.21/0.54    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP1(X0,X1))),
% 0.21/0.54    inference(nnf_transformation,[],[f40])).
% 0.21/0.54  fof(f40,plain,(
% 0.21/0.54    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP1(X0,X1))),
% 0.21/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.54  fof(f2175,plain,(
% 0.21/0.54    sP1(k1_xboole_0,k1_xboole_0) | (~spl7_7 | spl7_15 | ~spl7_17)),
% 0.21/0.54    inference(backward_demodulation,[],[f1022,f2115])).
% 0.21/0.54  fof(f2115,plain,(
% 0.21/0.54    k1_xboole_0 = sK4 | (~spl7_7 | spl7_15)),
% 0.21/0.54    inference(subsumption_resolution,[],[f2114,f901])).
% 0.21/0.54  fof(f901,plain,(
% 0.21/0.54    k1_xboole_0 != sK6 | spl7_15),
% 0.21/0.54    inference(avatar_component_clause,[],[f900])).
% 0.21/0.54  fof(f900,plain,(
% 0.21/0.54    spl7_15 <=> k1_xboole_0 = sK6),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 0.21/0.54  fof(f2114,plain,(
% 0.21/0.54    k1_xboole_0 = sK4 | k1_xboole_0 = sK6 | ~spl7_7),
% 0.21/0.54    inference(subsumption_resolution,[],[f2113,f1533])).
% 0.21/0.54  fof(f1533,plain,(
% 0.21/0.54    v1_funct_2(sK6,sK4,k1_xboole_0) | ~spl7_7),
% 0.21/0.54    inference(backward_demodulation,[],[f57,f356])).
% 0.21/0.54  fof(f356,plain,(
% 0.21/0.54    k1_xboole_0 = sK5 | ~spl7_7),
% 0.21/0.54    inference(avatar_component_clause,[],[f354])).
% 0.21/0.54  fof(f354,plain,(
% 0.21/0.54    spl7_7 <=> k1_xboole_0 = sK5),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.21/0.54  fof(f57,plain,(
% 0.21/0.54    v1_funct_2(sK6,sK4,sK5)),
% 0.21/0.54    inference(cnf_transformation,[],[f45])).
% 0.21/0.54  fof(f45,plain,(
% 0.21/0.54    (~m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) | ~v1_funct_2(k2_funct_1(sK6),sK5,sK4) | ~v1_funct_1(k2_funct_1(sK6))) & sK5 = k2_relset_1(sK4,sK5,sK6) & v2_funct_1(sK6) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(sK6,sK4,sK5) & v1_funct_1(sK6)),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f19,f44])).
% 0.21/0.54  fof(f44,plain,(
% 0.21/0.54    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) | ~v1_funct_2(k2_funct_1(sK6),sK5,sK4) | ~v1_funct_1(k2_funct_1(sK6))) & sK5 = k2_relset_1(sK4,sK5,sK6) & v2_funct_1(sK6) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(sK6,sK4,sK5) & v1_funct_1(sK6))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f19,plain,(
% 0.21/0.54    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.21/0.54    inference(flattening,[],[f18])).
% 0.21/0.54  fof(f18,plain,(
% 0.21/0.54    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.21/0.54    inference(ennf_transformation,[],[f17])).
% 0.21/0.54  fof(f17,negated_conjecture,(
% 0.21/0.54    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.21/0.54    inference(negated_conjecture,[],[f16])).
% 0.21/0.54  fof(f16,conjecture,(
% 0.21/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).
% 0.21/0.54  fof(f2113,plain,(
% 0.21/0.54    ~v1_funct_2(sK6,sK4,k1_xboole_0) | k1_xboole_0 = sK4 | k1_xboole_0 = sK6 | ~spl7_7),
% 0.21/0.54    inference(resolution,[],[f1542,f98])).
% 0.21/0.54  fof(f98,plain,(
% 0.21/0.54    ( ! [X2,X0] : (~sP3(X0,k1_xboole_0,X2) | ~v1_funct_2(X0,X2,k1_xboole_0) | k1_xboole_0 = X2 | k1_xboole_0 = X0) )),
% 0.21/0.54    inference(equality_resolution,[],[f86])).
% 0.21/0.54  fof(f86,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (k1_xboole_0 = X0 | ~v1_funct_2(X0,X2,X1) | k1_xboole_0 = X2 | k1_xboole_0 != X1 | ~sP3(X0,X1,X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f52])).
% 0.21/0.54  fof(f52,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (((v1_funct_2(X0,X2,X1) | k1_xboole_0 != X0) & (k1_xboole_0 = X0 | ~v1_funct_2(X0,X2,X1))) | k1_xboole_0 = X2 | k1_xboole_0 != X1 | ~sP3(X0,X1,X2))),
% 0.21/0.54    inference(rectify,[],[f51])).
% 0.21/0.54  fof(f51,plain,(
% 0.21/0.54    ! [X2,X1,X0] : (((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~sP3(X2,X1,X0))),
% 0.21/0.54    inference(nnf_transformation,[],[f42])).
% 0.21/0.54  fof(f42,plain,(
% 0.21/0.54    ! [X2,X1,X0] : ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~sP3(X2,X1,X0))),
% 0.21/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 0.21/0.54  fof(f1542,plain,(
% 0.21/0.54    sP3(sK6,k1_xboole_0,sK4) | ~spl7_7),
% 0.21/0.54    inference(backward_demodulation,[],[f187,f356])).
% 0.21/0.54  fof(f187,plain,(
% 0.21/0.54    sP3(sK6,sK5,sK4)),
% 0.21/0.54    inference(resolution,[],[f93,f58])).
% 0.21/0.54  fof(f58,plain,(
% 0.21/0.54    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))),
% 0.21/0.54    inference(cnf_transformation,[],[f45])).
% 0.21/0.54  fof(f93,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP3(X2,X1,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f43])).
% 0.21/0.54  fof(f43,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((sP3(X2,X1,X0) & sP2(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.54    inference(definition_folding,[],[f37,f42,f41,f40])).
% 0.21/0.54  fof(f41,plain,(
% 0.21/0.54    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | sP1(X0,X1) | ~sP2(X0,X2,X1))),
% 0.21/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.21/0.54  fof(f37,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.54    inference(flattening,[],[f36])).
% 0.21/0.54  fof(f36,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.54    inference(ennf_transformation,[],[f14])).
% 0.21/0.54  fof(f14,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.54  % (16474)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.54  fof(f1022,plain,(
% 0.21/0.54    sP1(sK4,k1_xboole_0) | (~spl7_7 | ~spl7_17)),
% 0.21/0.54    inference(backward_demodulation,[],[f918,f356])).
% 0.21/0.54  fof(f918,plain,(
% 0.21/0.54    sP1(sK4,sK5) | ~spl7_17),
% 0.21/0.54    inference(avatar_component_clause,[],[f916])).
% 0.21/0.54  fof(f916,plain,(
% 0.21/0.54    spl7_17 <=> sP1(sK4,sK5)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).
% 0.21/0.54  fof(f2085,plain,(
% 0.21/0.54    ~spl7_7 | spl7_11 | ~spl7_15),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f2084])).
% 0.21/0.54  fof(f2084,plain,(
% 0.21/0.54    $false | (~spl7_7 | spl7_11 | ~spl7_15)),
% 0.21/0.54    inference(subsumption_resolution,[],[f2083,f122])).
% 0.21/0.54  fof(f122,plain,(
% 0.21/0.54    v1_relat_1(k1_xboole_0)),
% 0.21/0.54    inference(resolution,[],[f118,f62])).
% 0.21/0.54  fof(f62,plain,(
% 0.21/0.54    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f2])).
% 0.21/0.54  fof(f2,axiom,(
% 0.21/0.54    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.54  fof(f118,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_zfmisc_1(X1,X2)) | v1_relat_1(X0)) )),
% 0.21/0.54    inference(resolution,[],[f81,f80])).
% 0.21/0.54  fof(f80,plain,(
% 0.21/0.54    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f50])).
% 0.21/0.54  fof(f50,plain,(
% 0.21/0.54    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.54    inference(nnf_transformation,[],[f3])).
% 0.21/0.54  fof(f3,axiom,(
% 0.21/0.54    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.54  fof(f81,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f32])).
% 0.21/0.54  fof(f32,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.54    inference(ennf_transformation,[],[f10])).
% 0.21/0.54  fof(f10,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.54  fof(f2083,plain,(
% 0.21/0.54    ~v1_relat_1(k1_xboole_0) | (~spl7_7 | spl7_11 | ~spl7_15)),
% 0.21/0.54    inference(subsumption_resolution,[],[f2082,f1555])).
% 0.21/0.54  fof(f1555,plain,(
% 0.21/0.54    v1_funct_1(k1_xboole_0) | ~spl7_15),
% 0.21/0.54    inference(backward_demodulation,[],[f56,f902])).
% 0.21/0.54  fof(f902,plain,(
% 0.21/0.54    k1_xboole_0 = sK6 | ~spl7_15),
% 0.21/0.54    inference(avatar_component_clause,[],[f900])).
% 0.21/0.54  fof(f56,plain,(
% 0.21/0.54    v1_funct_1(sK6)),
% 0.21/0.54    inference(cnf_transformation,[],[f45])).
% 0.21/0.54  fof(f2082,plain,(
% 0.21/0.54    ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | (~spl7_7 | spl7_11 | ~spl7_15)),
% 0.21/0.54    inference(subsumption_resolution,[],[f2081,f1556])).
% 0.21/0.54  fof(f1556,plain,(
% 0.21/0.54    v2_funct_1(k1_xboole_0) | ~spl7_15),
% 0.21/0.54    inference(backward_demodulation,[],[f59,f902])).
% 0.21/0.54  fof(f59,plain,(
% 0.21/0.54    v2_funct_1(sK6)),
% 0.21/0.54    inference(cnf_transformation,[],[f45])).
% 0.21/0.54  fof(f2081,plain,(
% 0.21/0.54    ~v2_funct_1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | (~spl7_7 | spl7_11 | ~spl7_15)),
% 0.21/0.54    inference(subsumption_resolution,[],[f2069,f1560])).
% 0.21/0.54  fof(f1560,plain,(
% 0.21/0.54    ~v5_relat_1(k2_funct_1(k1_xboole_0),k1_xboole_0) | (spl7_11 | ~spl7_15)),
% 0.21/0.54    inference(backward_demodulation,[],[f877,f902])).
% 0.21/0.54  fof(f877,plain,(
% 0.21/0.54    ~v5_relat_1(k2_funct_1(sK6),k1_xboole_0) | spl7_11),
% 0.21/0.54    inference(avatar_component_clause,[],[f875])).
% 0.21/0.54  fof(f875,plain,(
% 0.21/0.54    spl7_11 <=> v5_relat_1(k2_funct_1(sK6),k1_xboole_0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 0.21/0.54  fof(f2069,plain,(
% 0.21/0.54    v5_relat_1(k2_funct_1(k1_xboole_0),k1_xboole_0) | ~v2_funct_1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | (~spl7_7 | ~spl7_15)),
% 0.21/0.54    inference(superposition,[],[f277,f2051])).
% 0.21/0.54  fof(f2051,plain,(
% 0.21/0.54    k1_xboole_0 = k1_relat_1(k1_xboole_0) | (~spl7_7 | ~spl7_15)),
% 0.21/0.54    inference(resolution,[],[f2045,f94])).
% 0.21/0.54  fof(f94,plain,(
% 0.21/0.54    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.54    inference(equality_resolution,[],[f77])).
% 0.21/0.54  fof(f77,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.54    inference(cnf_transformation,[],[f49])).
% 0.21/0.54  fof(f49,plain,(
% 0.21/0.54    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.54    inference(flattening,[],[f48])).
% 0.21/0.54  fof(f48,plain,(
% 0.21/0.54    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.54    inference(nnf_transformation,[],[f1])).
% 0.21/0.54  fof(f1,axiom,(
% 0.21/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.54  fof(f2045,plain,(
% 0.21/0.54    ( ! [X0] : (~r1_tarski(X0,k1_relat_1(k1_xboole_0)) | k1_xboole_0 = X0) ) | (~spl7_7 | ~spl7_15)),
% 0.21/0.54    inference(resolution,[],[f2023,f62])).
% 0.21/0.54  fof(f2023,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r1_tarski(X1,k1_relat_1(k1_xboole_0)) | X0 = X1 | ~r1_tarski(X0,k1_relat_1(k1_xboole_0))) ) | (~spl7_7 | ~spl7_15)),
% 0.21/0.54    inference(superposition,[],[f2021,f2021])).
% 0.21/0.54  fof(f2021,plain,(
% 0.21/0.54    ( ! [X0] : (k10_relat_1(k1_xboole_0,k1_xboole_0) = X0 | ~r1_tarski(X0,k1_relat_1(k1_xboole_0))) ) | (~spl7_7 | ~spl7_15)),
% 0.21/0.54    inference(subsumption_resolution,[],[f2020,f122])).
% 0.21/0.54  fof(f2020,plain,(
% 0.21/0.54    ( ! [X0] : (k10_relat_1(k1_xboole_0,k1_xboole_0) = X0 | ~r1_tarski(X0,k1_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0)) ) | (~spl7_7 | ~spl7_15)),
% 0.21/0.54    inference(subsumption_resolution,[],[f2019,f1555])).
% 0.21/0.54  fof(f2019,plain,(
% 0.21/0.54    ( ! [X0] : (k10_relat_1(k1_xboole_0,k1_xboole_0) = X0 | ~r1_tarski(X0,k1_relat_1(k1_xboole_0)) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)) ) | (~spl7_7 | ~spl7_15)),
% 0.21/0.54    inference(subsumption_resolution,[],[f2011,f1556])).
% 0.21/0.54  fof(f2011,plain,(
% 0.21/0.54    ( ! [X0] : (k10_relat_1(k1_xboole_0,k1_xboole_0) = X0 | ~v2_funct_1(k1_xboole_0) | ~r1_tarski(X0,k1_relat_1(k1_xboole_0)) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)) ) | (~spl7_7 | ~spl7_15)),
% 0.21/0.54    inference(superposition,[],[f74,f2001])).
% 0.21/0.54  fof(f2001,plain,(
% 0.21/0.54    ( ! [X1] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X1)) ) | (~spl7_7 | ~spl7_15)),
% 0.21/0.54    inference(resolution,[],[f1998,f128])).
% 0.21/0.54  fof(f128,plain,(
% 0.21/0.54    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.21/0.54    inference(resolution,[],[f78,f62])).
% 0.21/0.54  fof(f78,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f49])).
% 0.21/0.54  fof(f1998,plain,(
% 0.21/0.54    ( ! [X2] : (r1_tarski(k9_relat_1(k1_xboole_0,X2),k1_xboole_0)) ) | (~spl7_7 | ~spl7_15)),
% 0.21/0.54    inference(subsumption_resolution,[],[f1997,f147])).
% 0.21/0.54  fof(f147,plain,(
% 0.21/0.54    ( ! [X0] : (v4_relat_1(k1_xboole_0,X0)) )),
% 0.21/0.54    inference(resolution,[],[f145,f62])).
% 0.21/0.54  fof(f145,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_zfmisc_1(X1,X2)) | v4_relat_1(X0,X1)) )),
% 0.21/0.54    inference(resolution,[],[f84,f80])).
% 0.21/0.54  fof(f84,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f35])).
% 0.21/0.54  fof(f35,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.54    inference(ennf_transformation,[],[f11])).
% 0.21/0.54  fof(f11,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.54  fof(f1997,plain,(
% 0.21/0.54    ( ! [X2] : (r1_tarski(k9_relat_1(k1_xboole_0,X2),k1_xboole_0) | ~v4_relat_1(k1_xboole_0,X2)) ) | (~spl7_7 | ~spl7_15)),
% 0.21/0.54    inference(subsumption_resolution,[],[f1989,f122])).
% 0.21/0.54  fof(f1989,plain,(
% 0.21/0.54    ( ! [X2] : (r1_tarski(k9_relat_1(k1_xboole_0,X2),k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v4_relat_1(k1_xboole_0,X2)) ) | (~spl7_7 | ~spl7_15)),
% 0.21/0.54    inference(superposition,[],[f1978,f1572])).
% 0.21/0.54  fof(f1572,plain,(
% 0.21/0.54    k1_xboole_0 = k2_relat_1(k1_xboole_0) | (~spl7_7 | ~spl7_15)),
% 0.21/0.54    inference(forward_demodulation,[],[f1543,f902])).
% 0.21/0.54  fof(f1543,plain,(
% 0.21/0.54    k1_xboole_0 = k2_relat_1(sK6) | ~spl7_7),
% 0.21/0.54    inference(backward_demodulation,[],[f338,f356])).
% 0.21/0.54  fof(f338,plain,(
% 0.21/0.54    sK5 = k2_relat_1(sK6)),
% 0.21/0.54    inference(subsumption_resolution,[],[f336,f58])).
% 0.21/0.54  fof(f336,plain,(
% 0.21/0.54    sK5 = k2_relat_1(sK6) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))),
% 0.21/0.54    inference(superposition,[],[f83,f60])).
% 0.21/0.54  fof(f60,plain,(
% 0.21/0.54    sK5 = k2_relset_1(sK4,sK5,sK6)),
% 0.21/0.54    inference(cnf_transformation,[],[f45])).
% 0.21/0.54  fof(f83,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f34])).
% 0.21/0.54  fof(f34,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.54    inference(ennf_transformation,[],[f13])).
% 0.21/0.54  fof(f13,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.54  fof(f1978,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0)) | ~v1_relat_1(X0) | ~v4_relat_1(X0,X1)) )),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f1973])).
% 0.21/0.54  fof(f1973,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0)) | ~v1_relat_1(X0) | ~v1_relat_1(X0) | ~v4_relat_1(X0,X1) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(superposition,[],[f812,f75])).
% 0.21/0.54  fof(f75,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f31])).
% 0.21/0.54  fof(f31,plain,(
% 0.21/0.54    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.54    inference(flattening,[],[f30])).
% 0.21/0.54  fof(f30,plain,(
% 0.21/0.54    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.54    inference(ennf_transformation,[],[f6])).
% 0.21/0.54  fof(f6,axiom,(
% 0.21/0.54    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).
% 0.21/0.54  fof(f812,plain,(
% 0.21/0.54    ( ! [X4,X3] : (r1_tarski(k9_relat_1(X3,X4),k2_relat_1(k7_relat_1(X3,X4))) | ~v1_relat_1(k7_relat_1(X3,X4)) | ~v1_relat_1(X3)) )),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f807])).
% 0.21/0.54  fof(f807,plain,(
% 0.21/0.54    ( ! [X4,X3] : (r1_tarski(k9_relat_1(X3,X4),k2_relat_1(k7_relat_1(X3,X4))) | ~v1_relat_1(k7_relat_1(X3,X4)) | ~v1_relat_1(X3) | ~v1_relat_1(k7_relat_1(X3,X4))) )),
% 0.21/0.54    inference(resolution,[],[f167,f125])).
% 0.21/0.54  fof(f125,plain,(
% 0.21/0.54    ( ! [X0] : (v5_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(resolution,[],[f69,f94])).
% 0.21/0.54  fof(f69,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f46])).
% 0.21/0.54  fof(f46,plain,(
% 0.21/0.54    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.21/0.54    inference(nnf_transformation,[],[f25])).
% 0.21/0.54  fof(f25,plain,(
% 0.21/0.54    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f4])).
% 0.21/0.54  fof(f4,axiom,(
% 0.21/0.54    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 0.21/0.54  fof(f167,plain,(
% 0.21/0.54    ( ! [X8,X7,X9] : (~v5_relat_1(k7_relat_1(X7,X8),X9) | r1_tarski(k9_relat_1(X7,X8),X9) | ~v1_relat_1(k7_relat_1(X7,X8)) | ~v1_relat_1(X7)) )),
% 0.21/0.54    inference(superposition,[],[f68,f67])).
% 0.21/0.54  fof(f67,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f24])).
% 0.21/0.54  fof(f24,plain,(
% 0.21/0.54    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f5])).
% 0.21/0.54  fof(f5,axiom,(
% 0.21/0.54    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 0.21/0.54  fof(f68,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f46])).
% 0.21/0.54  fof(f74,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f29])).
% 0.21/0.54  fof(f29,plain,(
% 0.21/0.54    ! [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.54    inference(flattening,[],[f28])).
% 0.21/0.54  fof(f28,plain,(
% 0.21/0.54    ! [X0,X1] : ((k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | (~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.54    inference(ennf_transformation,[],[f8])).
% 0.21/0.54  fof(f8,axiom,(
% 0.21/0.54    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t164_funct_1)).
% 0.21/0.54  fof(f277,plain,(
% 0.21/0.54    ( ! [X6] : (v5_relat_1(k2_funct_1(X6),k1_relat_1(X6)) | ~v2_funct_1(X6) | ~v1_funct_1(X6) | ~v1_relat_1(X6)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f268,f63])).
% 0.21/0.54  fof(f63,plain,(
% 0.21/0.54    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f21])).
% 0.21/0.54  fof(f21,plain,(
% 0.21/0.54    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(flattening,[],[f20])).
% 0.21/0.54  fof(f20,plain,(
% 0.21/0.54    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f7])).
% 0.21/0.54  fof(f7,axiom,(
% 0.21/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.21/0.54  fof(f268,plain,(
% 0.21/0.54    ( ! [X6] : (v5_relat_1(k2_funct_1(X6),k1_relat_1(X6)) | ~v1_relat_1(k2_funct_1(X6)) | ~v2_funct_1(X6) | ~v1_funct_1(X6) | ~v1_relat_1(X6)) )),
% 0.21/0.54    inference(superposition,[],[f125,f66])).
% 0.21/0.54  fof(f66,plain,(
% 0.21/0.54    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f23])).
% 0.21/0.54  fof(f23,plain,(
% 0.21/0.54    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(flattening,[],[f22])).
% 0.21/0.54  fof(f22,plain,(
% 0.21/0.54    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f9])).
% 0.21/0.54  fof(f9,axiom,(
% 0.21/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 0.21/0.54  fof(f2076,plain,(
% 0.21/0.54    spl7_3 | ~spl7_7 | ~spl7_15),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f2075])).
% 0.21/0.54  fof(f2075,plain,(
% 0.21/0.54    $false | (spl7_3 | ~spl7_7 | ~spl7_15)),
% 0.21/0.54    inference(subsumption_resolution,[],[f2057,f62])).
% 0.21/0.54  fof(f2057,plain,(
% 0.21/0.54    ~r1_tarski(k1_xboole_0,sK4) | (spl7_3 | ~spl7_7 | ~spl7_15)),
% 0.21/0.54    inference(backward_demodulation,[],[f1777,f2051])).
% 0.21/0.54  fof(f1777,plain,(
% 0.21/0.54    ~r1_tarski(k1_relat_1(k1_xboole_0),sK4) | (spl7_3 | ~spl7_15)),
% 0.21/0.54    inference(subsumption_resolution,[],[f1776,f122])).
% 0.21/0.54  fof(f1776,plain,(
% 0.21/0.54    ~r1_tarski(k1_relat_1(k1_xboole_0),sK4) | ~v1_relat_1(k1_xboole_0) | (spl7_3 | ~spl7_15)),
% 0.21/0.54    inference(subsumption_resolution,[],[f1775,f1555])).
% 0.21/0.54  fof(f1775,plain,(
% 0.21/0.54    ~r1_tarski(k1_relat_1(k1_xboole_0),sK4) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | (spl7_3 | ~spl7_15)),
% 0.21/0.54    inference(subsumption_resolution,[],[f1772,f1556])).
% 0.21/0.54  fof(f1772,plain,(
% 0.21/0.54    ~r1_tarski(k1_relat_1(k1_xboole_0),sK4) | ~v2_funct_1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | (spl7_3 | ~spl7_15)),
% 0.21/0.54    inference(resolution,[],[f1581,f276])).
% 0.21/0.54  fof(f276,plain,(
% 0.21/0.54    ( ! [X4,X5] : (sP0(X5,k2_funct_1(X4)) | ~r1_tarski(k1_relat_1(X4),X5) | ~v2_funct_1(X4) | ~v1_funct_1(X4) | ~v1_relat_1(X4)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f275,f63])).
% 0.21/0.54  fof(f275,plain,(
% 0.21/0.54    ( ! [X4,X5] : (~r1_tarski(k1_relat_1(X4),X5) | sP0(X5,k2_funct_1(X4)) | ~v1_relat_1(k2_funct_1(X4)) | ~v2_funct_1(X4) | ~v1_funct_1(X4) | ~v1_relat_1(X4)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f267,f64])).
% 0.21/0.54  fof(f64,plain,(
% 0.21/0.54    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f21])).
% 0.21/0.54  fof(f267,plain,(
% 0.21/0.54    ( ! [X4,X5] : (~r1_tarski(k1_relat_1(X4),X5) | sP0(X5,k2_funct_1(X4)) | ~v1_funct_1(k2_funct_1(X4)) | ~v1_relat_1(k2_funct_1(X4)) | ~v2_funct_1(X4) | ~v1_funct_1(X4) | ~v1_relat_1(X4)) )),
% 0.21/0.54    inference(superposition,[],[f73,f66])).
% 0.21/0.54  fof(f73,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | sP0(X0,X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f39])).
% 0.21/0.54  fof(f39,plain,(
% 0.21/0.54    ! [X0,X1] : (sP0(X0,X1) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.54    inference(definition_folding,[],[f27,f38])).
% 0.21/0.54  fof(f38,plain,(
% 0.21/0.54    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~sP0(X0,X1))),
% 0.21/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.54  fof(f27,plain,(
% 0.21/0.54    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.54    inference(flattening,[],[f26])).
% 0.21/0.54  fof(f26,plain,(
% 0.21/0.54    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.54    inference(ennf_transformation,[],[f15])).
% 0.21/0.54  fof(f15,axiom,(
% 0.21/0.54    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).
% 0.21/0.54  fof(f1581,plain,(
% 0.21/0.54    ~sP0(sK4,k2_funct_1(k1_xboole_0)) | (spl7_3 | ~spl7_15)),
% 0.21/0.54    inference(forward_demodulation,[],[f1304,f902])).
% 0.21/0.54  fof(f1304,plain,(
% 0.21/0.54    ~sP0(sK4,k2_funct_1(sK6)) | spl7_3),
% 0.21/0.54    inference(resolution,[],[f1272,f111])).
% 0.21/0.54  fof(f111,plain,(
% 0.21/0.54    ~m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) | spl7_3),
% 0.21/0.54    inference(avatar_component_clause,[],[f109])).
% 0.21/0.54  fof(f109,plain,(
% 0.21/0.54    spl7_3 <=> m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.21/0.54  fof(f1272,plain,(
% 0.21/0.54    ( ! [X8] : (m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,X8))) | ~sP0(X8,k2_funct_1(sK6))) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f1271,f117])).
% 0.21/0.54  fof(f117,plain,(
% 0.21/0.54    v1_relat_1(sK6)),
% 0.21/0.54    inference(resolution,[],[f81,f58])).
% 0.21/0.54  fof(f1271,plain,(
% 0.21/0.54    ( ! [X8] : (m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,X8))) | ~sP0(X8,k2_funct_1(sK6)) | ~v1_relat_1(sK6)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f1270,f56])).
% 0.21/0.54  fof(f1270,plain,(
% 0.21/0.54    ( ! [X8] : (m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,X8))) | ~sP0(X8,k2_funct_1(sK6)) | ~v1_funct_1(sK6) | ~v1_relat_1(sK6)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f1266,f59])).
% 0.21/0.54  fof(f1266,plain,(
% 0.21/0.54    ( ! [X8] : (m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,X8))) | ~sP0(X8,k2_funct_1(sK6)) | ~v2_funct_1(sK6) | ~v1_funct_1(sK6) | ~v1_relat_1(sK6)) )),
% 0.21/0.54    inference(superposition,[],[f241,f338])).
% 0.21/0.54  fof(f241,plain,(
% 0.21/0.54    ( ! [X8,X9] : (m1_subset_1(k2_funct_1(X8),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X8),X9))) | ~sP0(X9,k2_funct_1(X8)) | ~v2_funct_1(X8) | ~v1_funct_1(X8) | ~v1_relat_1(X8)) )),
% 0.21/0.54    inference(superposition,[],[f72,f65])).
% 0.21/0.54  fof(f65,plain,(
% 0.21/0.54    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f23])).
% 0.21/0.54  fof(f72,plain,(
% 0.21/0.54    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~sP0(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f47])).
% 0.21/0.54  fof(f47,plain,(
% 0.21/0.54    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~sP0(X0,X1))),
% 0.21/0.54    inference(nnf_transformation,[],[f38])).
% 0.21/0.54  fof(f1503,plain,(
% 0.21/0.54    spl7_7 | ~spl7_17),
% 0.21/0.54    inference(avatar_split_clause,[],[f1502,f916,f354])).
% 0.21/0.54  fof(f1502,plain,(
% 0.21/0.54    k1_xboole_0 = sK5 | ~spl7_17),
% 0.21/0.54    inference(resolution,[],[f918,f90])).
% 0.21/0.54  fof(f90,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~sP1(X0,X1) | k1_xboole_0 = X1) )),
% 0.21/0.54    inference(cnf_transformation,[],[f55])).
% 0.21/0.54  fof(f1493,plain,(
% 0.21/0.54    spl7_16 | spl7_17),
% 0.21/0.54    inference(avatar_split_clause,[],[f1077,f916,f912])).
% 0.21/0.54  fof(f912,plain,(
% 0.21/0.54    spl7_16 <=> sK4 = k1_relat_1(sK6)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).
% 0.21/0.54  fof(f1077,plain,(
% 0.21/0.54    sP1(sK4,sK5) | sK4 = k1_relat_1(sK6)),
% 0.21/0.54    inference(subsumption_resolution,[],[f1070,f57])).
% 0.21/0.54  fof(f1070,plain,(
% 0.21/0.54    ~v1_funct_2(sK6,sK4,sK5) | sP1(sK4,sK5) | sK4 = k1_relat_1(sK6)),
% 0.21/0.54    inference(resolution,[],[f58,f471])).
% 0.21/0.54  fof(f471,plain,(
% 0.21/0.54    ( ! [X4,X5,X3] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_2(X5,X3,X4) | sP1(X3,X4) | k1_relat_1(X5) = X3) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f469,f92])).
% 0.21/0.54  fof(f92,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP2(X0,X2,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f43])).
% 0.21/0.54  fof(f469,plain,(
% 0.21/0.54    ( ! [X4,X5,X3] : (k1_relat_1(X5) = X3 | ~v1_funct_2(X5,X3,X4) | sP1(X3,X4) | ~sP2(X3,X5,X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) )),
% 0.21/0.54    inference(superposition,[],[f88,f82])).
% 0.21/0.54  fof(f82,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f33])).
% 0.21/0.54  fof(f33,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.54    inference(ennf_transformation,[],[f12])).
% 0.21/0.54  fof(f12,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.54  fof(f88,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2) | sP1(X0,X2) | ~sP2(X0,X1,X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f54])).
% 0.21/0.54  fof(f54,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | sP1(X0,X2) | ~sP2(X0,X1,X2))),
% 0.21/0.54    inference(rectify,[],[f53])).
% 0.21/0.54  fof(f53,plain,(
% 0.21/0.54    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | sP1(X0,X1) | ~sP2(X0,X2,X1))),
% 0.21/0.54    inference(nnf_transformation,[],[f41])).
% 0.21/0.54  fof(f1314,plain,(
% 0.21/0.54    spl7_3 | ~spl7_16),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f1313])).
% 0.21/0.54  fof(f1313,plain,(
% 0.21/0.54    $false | (spl7_3 | ~spl7_16)),
% 0.21/0.54    inference(subsumption_resolution,[],[f1304,f949])).
% 0.21/0.54  fof(f949,plain,(
% 0.21/0.54    sP0(sK4,k2_funct_1(sK6)) | ~spl7_16),
% 0.21/0.54    inference(subsumption_resolution,[],[f948,f117])).
% 0.21/0.54  fof(f948,plain,(
% 0.21/0.54    sP0(sK4,k2_funct_1(sK6)) | ~v1_relat_1(sK6) | ~spl7_16),
% 0.21/0.54    inference(subsumption_resolution,[],[f947,f56])).
% 0.21/0.54  fof(f947,plain,(
% 0.21/0.54    sP0(sK4,k2_funct_1(sK6)) | ~v1_funct_1(sK6) | ~v1_relat_1(sK6) | ~spl7_16),
% 0.21/0.54    inference(subsumption_resolution,[],[f929,f59])).
% 0.21/0.54  fof(f929,plain,(
% 0.21/0.54    sP0(sK4,k2_funct_1(sK6)) | ~v2_funct_1(sK6) | ~v1_funct_1(sK6) | ~v1_relat_1(sK6) | ~spl7_16),
% 0.21/0.54    inference(superposition,[],[f280,f914])).
% 0.21/0.54  fof(f914,plain,(
% 0.21/0.54    sK4 = k1_relat_1(sK6) | ~spl7_16),
% 0.21/0.54    inference(avatar_component_clause,[],[f912])).
% 0.21/0.54  fof(f280,plain,(
% 0.21/0.54    ( ! [X8] : (sP0(k1_relat_1(X8),k2_funct_1(X8)) | ~v2_funct_1(X8) | ~v1_funct_1(X8) | ~v1_relat_1(X8)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f279,f63])).
% 0.21/0.54  fof(f279,plain,(
% 0.21/0.54    ( ! [X8] : (sP0(k1_relat_1(X8),k2_funct_1(X8)) | ~v1_relat_1(k2_funct_1(X8)) | ~v2_funct_1(X8) | ~v1_funct_1(X8) | ~v1_relat_1(X8)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f270,f64])).
% 0.21/0.54  fof(f270,plain,(
% 0.21/0.54    ( ! [X8] : (sP0(k1_relat_1(X8),k2_funct_1(X8)) | ~v1_funct_1(k2_funct_1(X8)) | ~v1_relat_1(k2_funct_1(X8)) | ~v2_funct_1(X8) | ~v1_funct_1(X8) | ~v1_relat_1(X8)) )),
% 0.21/0.54    inference(superposition,[],[f201,f66])).
% 0.21/0.54  fof(f201,plain,(
% 0.21/0.54    ( ! [X0] : (sP0(k2_relat_1(X0),X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(resolution,[],[f73,f94])).
% 0.21/0.54  fof(f943,plain,(
% 0.21/0.54    spl7_2 | ~spl7_16),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f942])).
% 0.21/0.54  fof(f942,plain,(
% 0.21/0.54    $false | (spl7_2 | ~spl7_16)),
% 0.21/0.54    inference(subsumption_resolution,[],[f941,f117])).
% 0.21/0.54  fof(f941,plain,(
% 0.21/0.54    ~v1_relat_1(sK6) | (spl7_2 | ~spl7_16)),
% 0.21/0.54    inference(subsumption_resolution,[],[f940,f56])).
% 0.21/0.54  fof(f940,plain,(
% 0.21/0.54    ~v1_funct_1(sK6) | ~v1_relat_1(sK6) | (spl7_2 | ~spl7_16)),
% 0.21/0.54    inference(subsumption_resolution,[],[f939,f59])).
% 0.21/0.54  fof(f939,plain,(
% 0.21/0.54    ~v2_funct_1(sK6) | ~v1_funct_1(sK6) | ~v1_relat_1(sK6) | (spl7_2 | ~spl7_16)),
% 0.21/0.54    inference(subsumption_resolution,[],[f929,f866])).
% 0.21/0.54  fof(f866,plain,(
% 0.21/0.54    ~sP0(sK4,k2_funct_1(sK6)) | spl7_2),
% 0.21/0.54    inference(resolution,[],[f865,f107])).
% 0.21/0.54  fof(f107,plain,(
% 0.21/0.54    ~v1_funct_2(k2_funct_1(sK6),sK5,sK4) | spl7_2),
% 0.21/0.54    inference(avatar_component_clause,[],[f105])).
% 0.21/0.54  fof(f105,plain,(
% 0.21/0.54    spl7_2 <=> v1_funct_2(k2_funct_1(sK6),sK5,sK4)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.21/0.54  fof(f865,plain,(
% 0.21/0.54    ( ! [X7] : (v1_funct_2(k2_funct_1(sK6),sK5,X7) | ~sP0(X7,k2_funct_1(sK6))) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f864,f117])).
% 0.21/0.54  fof(f864,plain,(
% 0.21/0.54    ( ! [X7] : (v1_funct_2(k2_funct_1(sK6),sK5,X7) | ~sP0(X7,k2_funct_1(sK6)) | ~v1_relat_1(sK6)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f863,f56])).
% 0.21/0.54  fof(f863,plain,(
% 0.21/0.54    ( ! [X7] : (v1_funct_2(k2_funct_1(sK6),sK5,X7) | ~sP0(X7,k2_funct_1(sK6)) | ~v1_funct_1(sK6) | ~v1_relat_1(sK6)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f859,f59])).
% 0.21/0.54  fof(f859,plain,(
% 0.21/0.54    ( ! [X7] : (v1_funct_2(k2_funct_1(sK6),sK5,X7) | ~sP0(X7,k2_funct_1(sK6)) | ~v2_funct_1(sK6) | ~v1_funct_1(sK6) | ~v1_relat_1(sK6)) )),
% 0.21/0.54    inference(superposition,[],[f242,f338])).
% 0.21/0.54  fof(f242,plain,(
% 0.21/0.54    ( ! [X10,X11] : (v1_funct_2(k2_funct_1(X10),k2_relat_1(X10),X11) | ~sP0(X11,k2_funct_1(X10)) | ~v2_funct_1(X10) | ~v1_funct_1(X10) | ~v1_relat_1(X10)) )),
% 0.21/0.54    inference(superposition,[],[f71,f65])).
% 0.21/0.54  fof(f71,plain,(
% 0.21/0.54    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~sP0(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f47])).
% 0.21/0.54  fof(f892,plain,(
% 0.21/0.54    spl7_12),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f891])).
% 0.21/0.54  fof(f891,plain,(
% 0.21/0.54    $false | spl7_12),
% 0.21/0.54    inference(subsumption_resolution,[],[f890,f117])).
% 0.21/0.54  fof(f890,plain,(
% 0.21/0.54    ~v1_relat_1(sK6) | spl7_12),
% 0.21/0.54    inference(subsumption_resolution,[],[f889,f56])).
% 0.21/0.54  fof(f889,plain,(
% 0.21/0.54    ~v1_funct_1(sK6) | ~v1_relat_1(sK6) | spl7_12),
% 0.21/0.54    inference(resolution,[],[f881,f63])).
% 0.21/0.54  fof(f881,plain,(
% 0.21/0.54    ~v1_relat_1(k2_funct_1(sK6)) | spl7_12),
% 0.21/0.54    inference(avatar_component_clause,[],[f879])).
% 0.21/0.54  fof(f879,plain,(
% 0.21/0.54    spl7_12 <=> v1_relat_1(k2_funct_1(sK6))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 0.21/0.54  fof(f882,plain,(
% 0.21/0.54    ~spl7_11 | ~spl7_12 | ~spl7_1 | spl7_2),
% 0.21/0.54    inference(avatar_split_clause,[],[f873,f105,f101,f879,f875])).
% 0.21/0.54  fof(f101,plain,(
% 0.21/0.54    spl7_1 <=> v1_funct_1(k2_funct_1(sK6))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.21/0.54  fof(f873,plain,(
% 0.21/0.54    ~v1_relat_1(k2_funct_1(sK6)) | ~v5_relat_1(k2_funct_1(sK6),k1_xboole_0) | (~spl7_1 | spl7_2)),
% 0.21/0.54    inference(subsumption_resolution,[],[f868,f102])).
% 0.21/0.54  fof(f102,plain,(
% 0.21/0.54    v1_funct_1(k2_funct_1(sK6)) | ~spl7_1),
% 0.21/0.54    inference(avatar_component_clause,[],[f101])).
% 0.21/0.54  fof(f868,plain,(
% 0.21/0.54    ~v1_funct_1(k2_funct_1(sK6)) | ~v1_relat_1(k2_funct_1(sK6)) | ~v5_relat_1(k2_funct_1(sK6),k1_xboole_0) | spl7_2),
% 0.21/0.54    inference(resolution,[],[f866,f208])).
% 0.21/0.54  fof(f208,plain,(
% 0.21/0.54    ( ! [X0,X1] : (sP0(X1,X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v5_relat_1(X0,k1_xboole_0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f206,f62])).
% 0.21/0.54  fof(f206,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r1_tarski(k1_xboole_0,X1) | sP0(X1,X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v5_relat_1(X0,k1_xboole_0)) )),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f204])).
% 0.21/0.54  fof(f204,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r1_tarski(k1_xboole_0,X1) | sP0(X1,X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v5_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(superposition,[],[f73,f143])).
% 0.21/0.54  fof(f143,plain,(
% 0.21/0.54    ( ! [X0] : (k1_xboole_0 = k2_relat_1(X0) | ~v5_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(resolution,[],[f128,f68])).
% 0.21/0.54  fof(f120,plain,(
% 0.21/0.54    spl7_1),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f119])).
% 0.21/0.54  fof(f119,plain,(
% 0.21/0.54    $false | spl7_1),
% 0.21/0.54    inference(subsumption_resolution,[],[f117,f114])).
% 0.21/0.54  fof(f114,plain,(
% 0.21/0.54    ~v1_relat_1(sK6) | spl7_1),
% 0.21/0.54    inference(subsumption_resolution,[],[f113,f56])).
% 0.21/0.54  fof(f113,plain,(
% 0.21/0.54    ~v1_funct_1(sK6) | ~v1_relat_1(sK6) | spl7_1),
% 0.21/0.54    inference(resolution,[],[f64,f103])).
% 0.21/0.54  fof(f103,plain,(
% 0.21/0.54    ~v1_funct_1(k2_funct_1(sK6)) | spl7_1),
% 0.21/0.54    inference(avatar_component_clause,[],[f101])).
% 0.21/0.54  fof(f112,plain,(
% 0.21/0.54    ~spl7_1 | ~spl7_2 | ~spl7_3),
% 0.21/0.54    inference(avatar_split_clause,[],[f61,f109,f105,f101])).
% 0.21/0.54  fof(f61,plain,(
% 0.21/0.54    ~m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) | ~v1_funct_2(k2_funct_1(sK6),sK5,sK4) | ~v1_funct_1(k2_funct_1(sK6))),
% 0.21/0.54    inference(cnf_transformation,[],[f45])).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (16459)------------------------------
% 0.21/0.54  % (16459)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (16459)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (16459)Memory used [KB]: 6780
% 0.21/0.54  % (16459)Time elapsed: 0.119 s
% 0.21/0.54  % (16459)------------------------------
% 0.21/0.54  % (16459)------------------------------
% 0.21/0.54  % (16452)Success in time 0.185 s
%------------------------------------------------------------------------------
