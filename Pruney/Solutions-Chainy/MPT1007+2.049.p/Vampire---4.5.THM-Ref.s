%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:03:58 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  168 ( 300 expanded)
%              Number of leaves         :   43 ( 125 expanded)
%              Depth                    :    8
%              Number of atoms          :  479 ( 826 expanded)
%              Number of equality atoms :   93 ( 180 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (8740)Termination reason: Refutation not found, incomplete strategy

% (8740)Memory used [KB]: 1663
% (8740)Time elapsed: 0.153 s
% (8740)------------------------------
% (8740)------------------------------
fof(f548,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f114,f119,f124,f130,f135,f151,f156,f166,f179,f200,f214,f223,f232,f237,f288,f329,f334,f422,f424,f431,f475,f502,f508,f547])).

fof(f547,plain,
    ( ~ spl13_31
    | ~ spl13_34 ),
    inference(avatar_contradiction_clause,[],[f541])).

fof(f541,plain,
    ( $false
    | ~ spl13_31
    | ~ spl13_34 ),
    inference(unit_resulting_resolution,[],[f59,f90,f514,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f514,plain,
    ( ! [X0] : ~ r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl13_31
    | ~ spl13_34 ),
    inference(resolution,[],[f509,f430])).

fof(f430,plain,
    ( sP11(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl13_31 ),
    inference(avatar_component_clause,[],[f428])).

fof(f428,plain,
    ( spl13_31
  <=> sP11(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_31])])).

fof(f509,plain,
    ( ! [X0,X1] :
        ( ~ sP11(k1_xboole_0,X1)
        | ~ r2_hidden(X0,X1) )
    | ~ spl13_34 ),
    inference(resolution,[],[f501,f107])).

fof(f107,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(k4_tarski(X3,sK7(X2,X3)),X2)
      | ~ r2_hidden(X3,X1)
      | ~ sP11(X2,X1) ) ),
    inference(general_splitting,[],[f81,f106_D])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k1_relset_1(X1,X0,X2) != X1
      | sP11(X2,X1) ) ),
    inference(cnf_transformation,[],[f106_D])).

fof(f106_D,plain,(
    ! [X1,X2] :
      ( ! [X0] :
          ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | k1_relset_1(X1,X0,X2) != X1 )
    <=> ~ sP11(X2,X1) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP11])])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k1_relset_1(X1,X0,X2) != X1
      | ~ r2_hidden(X3,X1)
      | r2_hidden(k4_tarski(X3,sK7(X2,X3)),X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relset_1)).

fof(f501,plain,
    ( ! [X1] : ~ r2_hidden(X1,k1_xboole_0)
    | ~ spl13_34 ),
    inference(avatar_component_clause,[],[f500])).

fof(f500,plain,
    ( spl13_34
  <=> ! [X1] : ~ r2_hidden(X1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_34])])).

fof(f90,plain,(
    ! [X0] : ~ v1_xboole_0(k2_enumset1(X0,X0,X0,X0)) ),
    inference(definition_unfolding,[],[f50,f87])).

fof(f87,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f53,f86])).

fof(f86,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f60,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f60,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f53,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f50,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).

fof(f59,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f508,plain,(
    ~ spl13_33 ),
    inference(avatar_contradiction_clause,[],[f504])).

fof(f504,plain,
    ( $false
    | ~ spl13_33 ),
    inference(unit_resulting_resolution,[],[f52,f498,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f498,plain,
    ( ! [X0] : ~ v1_relat_1(X0)
    | ~ spl13_33 ),
    inference(avatar_component_clause,[],[f497])).

fof(f497,plain,
    ( spl13_33
  <=> ! [X0] : ~ v1_relat_1(X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_33])])).

fof(f52,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f502,plain,
    ( spl13_33
    | spl13_34
    | ~ spl13_32 ),
    inference(avatar_split_clause,[],[f495,f473,f500,f497])).

fof(f473,plain,
    ( spl13_32
  <=> ! [X5,X4] :
        ( ~ v1_relat_1(X5)
        | ~ r2_hidden(X4,k10_relat_1(X5,k1_xboole_0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_32])])).

fof(f495,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,k1_xboole_0)
        | ~ v1_relat_1(X0) )
    | ~ spl13_32 ),
    inference(duplicate_literal_removal,[],[f488])).

fof(f488,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,k1_xboole_0)
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl13_32 ),
    inference(superposition,[],[f474,f481])).

fof(f481,plain,
    ( ! [X12] :
        ( k1_xboole_0 = k10_relat_1(X12,k1_xboole_0)
        | ~ v1_relat_1(X12) )
    | ~ spl13_32 ),
    inference(resolution,[],[f474,f58])).

fof(f58,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5,X6] :
              ( r1_xboole_0(X2,X0)
              | ~ r2_hidden(X6,X1)
              | ~ r2_hidden(X5,X6)
              | ~ r2_hidden(X4,X5)
              | ~ r2_hidden(X3,X4)
              | ~ r2_hidden(X2,X3) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5,X6] :
              ( r1_xboole_0(X2,X0)
              | ~ r2_hidden(X6,X1)
              | ~ r2_hidden(X5,X6)
              | ~ r2_hidden(X4,X5)
              | ~ r2_hidden(X3,X4)
              | ~ r2_hidden(X2,X3) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4,X5,X6] :
                  ( ( r2_hidden(X6,X1)
                    & r2_hidden(X5,X6)
                    & r2_hidden(X4,X5)
                    & r2_hidden(X3,X4)
                    & r2_hidden(X2,X3) )
                 => r1_xboole_0(X2,X0) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_mcart_1)).

fof(f474,plain,
    ( ! [X4,X5] :
        ( ~ r2_hidden(X4,k10_relat_1(X5,k1_xboole_0))
        | ~ v1_relat_1(X5) )
    | ~ spl13_32 ),
    inference(avatar_component_clause,[],[f473])).

fof(f475,plain,
    ( spl13_32
    | spl13_16
    | ~ spl13_13
    | ~ spl13_19
    | ~ spl13_25 ),
    inference(avatar_split_clause,[],[f469,f326,f234,f198,f220,f473])).

fof(f220,plain,
    ( spl13_16
  <=> r2_hidden(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_16])])).

fof(f198,plain,
    ( spl13_13
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK2))
        | sK0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_13])])).

fof(f234,plain,
    ( spl13_19
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_19])])).

fof(f326,plain,
    ( spl13_25
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_25])])).

fof(f469,plain,
    ( ! [X4,X5] :
        ( r2_hidden(sK0,k1_xboole_0)
        | ~ v1_relat_1(X5)
        | ~ r2_hidden(X4,k10_relat_1(X5,k1_xboole_0)) )
    | ~ spl13_13
    | ~ spl13_19
    | ~ spl13_25 ),
    inference(duplicate_literal_removal,[],[f464])).

fof(f464,plain,
    ( ! [X4,X5] :
        ( r2_hidden(sK0,k1_xboole_0)
        | ~ v1_relat_1(X5)
        | ~ r2_hidden(X4,k10_relat_1(X5,k1_xboole_0))
        | ~ v1_relat_1(X5)
        | ~ r2_hidden(X4,k10_relat_1(X5,k1_xboole_0)) )
    | ~ spl13_13
    | ~ spl13_19
    | ~ spl13_25 ),
    inference(superposition,[],[f68,f358])).

fof(f358,plain,
    ( ! [X6,X7] :
        ( sK0 = sK5(X6,k1_xboole_0,X7)
        | ~ v1_relat_1(X7)
        | ~ r2_hidden(X6,k10_relat_1(X7,k1_xboole_0)) )
    | ~ spl13_13
    | ~ spl13_19
    | ~ spl13_25 ),
    inference(resolution,[],[f353,f68])).

fof(f353,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_xboole_0)
        | sK0 = X0 )
    | ~ spl13_13
    | ~ spl13_19
    | ~ spl13_25 ),
    inference(forward_demodulation,[],[f300,f328])).

fof(f328,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl13_25 ),
    inference(avatar_component_clause,[],[f326])).

fof(f300,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(k1_xboole_0))
        | sK0 = X0 )
    | ~ spl13_13
    | ~ spl13_19 ),
    inference(backward_demodulation,[],[f199,f236])).

fof(f236,plain,
    ( k1_xboole_0 = sK2
    | ~ spl13_19 ),
    inference(avatar_component_clause,[],[f234])).

fof(f199,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK2))
        | sK0 = X0 )
    | ~ spl13_13 ),
    inference(avatar_component_clause,[],[f198])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X2),X1)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

fof(f431,plain,
    ( spl13_31
    | ~ spl13_17
    | ~ spl13_19 ),
    inference(avatar_split_clause,[],[f426,f234,f225,f428])).

fof(f225,plain,
    ( spl13_17
  <=> sP11(sK2,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_17])])).

fof(f426,plain,
    ( sP11(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl13_17
    | ~ spl13_19 ),
    inference(forward_demodulation,[],[f227,f236])).

fof(f227,plain,
    ( sP11(sK2,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl13_17 ),
    inference(avatar_component_clause,[],[f225])).

fof(f424,plain,
    ( spl13_2
    | ~ spl13_26
    | spl13_30 ),
    inference(avatar_contradiction_clause,[],[f423])).

fof(f423,plain,
    ( $false
    | spl13_2
    | ~ spl13_26
    | spl13_30 ),
    inference(unit_resulting_resolution,[],[f118,f333,f52,f421,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

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
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
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

fof(f421,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) != k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k1_xboole_0)
    | spl13_30 ),
    inference(avatar_component_clause,[],[f419])).

fof(f419,plain,
    ( spl13_30
  <=> k2_enumset1(sK0,sK0,sK0,sK0) = k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_30])])).

fof(f333,plain,
    ( v1_funct_2(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0),sK1)
    | ~ spl13_26 ),
    inference(avatar_component_clause,[],[f331])).

fof(f331,plain,
    ( spl13_26
  <=> v1_funct_2(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_26])])).

fof(f118,plain,
    ( k1_xboole_0 != sK1
    | spl13_2 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl13_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_2])])).

fof(f422,plain,
    ( ~ spl13_30
    | spl13_18
    | ~ spl13_19 ),
    inference(avatar_split_clause,[],[f406,f234,f229,f419])).

fof(f229,plain,
    ( spl13_18
  <=> k2_enumset1(sK0,sK0,sK0,sK0) = k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_18])])).

fof(f406,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) != k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k1_xboole_0)
    | spl13_18
    | ~ spl13_19 ),
    inference(forward_demodulation,[],[f231,f236])).

fof(f231,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) != k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2)
    | spl13_18 ),
    inference(avatar_component_clause,[],[f229])).

fof(f334,plain,
    ( spl13_26
    | ~ spl13_4
    | ~ spl13_19 ),
    inference(avatar_split_clause,[],[f291,f234,f127,f331])).

fof(f127,plain,
    ( spl13_4
  <=> v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_4])])).

fof(f291,plain,
    ( v1_funct_2(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0),sK1)
    | ~ spl13_4
    | ~ spl13_19 ),
    inference(backward_demodulation,[],[f129,f236])).

fof(f129,plain,
    ( v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1)
    | ~ spl13_4 ),
    inference(avatar_component_clause,[],[f127])).

fof(f329,plain,
    ( spl13_25
    | ~ spl13_14
    | ~ spl13_19 ),
    inference(avatar_split_clause,[],[f317,f234,f207,f326])).

fof(f207,plain,
    ( spl13_14
  <=> k1_xboole_0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_14])])).

fof(f317,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl13_14
    | ~ spl13_19 ),
    inference(forward_demodulation,[],[f209,f236])).

fof(f209,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ spl13_14 ),
    inference(avatar_component_clause,[],[f207])).

fof(f288,plain,
    ( spl13_14
    | spl13_9
    | ~ spl13_15 ),
    inference(avatar_split_clause,[],[f258,f211,f163,f207])).

fof(f163,plain,
    ( spl13_9
  <=> r2_hidden(sK0,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_9])])).

fof(f211,plain,
    ( spl13_15
  <=> sK0 = sK3(k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_15])])).

fof(f258,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | k1_xboole_0 = k1_relat_1(sK2)
    | ~ spl13_15 ),
    inference(superposition,[],[f58,f213])).

fof(f213,plain,
    ( sK0 = sK3(k1_relat_1(sK2))
    | ~ spl13_15 ),
    inference(avatar_component_clause,[],[f211])).

fof(f237,plain,
    ( spl13_19
    | ~ spl13_6
    | ~ spl13_14 ),
    inference(avatar_split_clause,[],[f218,f207,f148,f234])).

fof(f148,plain,
    ( spl13_6
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_6])])).

fof(f218,plain,
    ( ~ v1_relat_1(sK2)
    | k1_xboole_0 = sK2
    | ~ spl13_14 ),
    inference(trivial_inequality_removal,[],[f217])).

fof(f217,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ v1_relat_1(sK2)
    | k1_xboole_0 = sK2
    | ~ spl13_14 ),
    inference(superposition,[],[f55,f209])).

fof(f55,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(f232,plain,
    ( spl13_17
    | ~ spl13_18
    | ~ spl13_5 ),
    inference(avatar_split_clause,[],[f142,f132,f229,f225])).

fof(f132,plain,
    ( spl13_5
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_5])])).

fof(f142,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) != k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2)
    | sP11(sK2,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl13_5 ),
    inference(resolution,[],[f134,f106])).

fof(f134,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
    | ~ spl13_5 ),
    inference(avatar_component_clause,[],[f132])).

fof(f223,plain,
    ( ~ spl13_16
    | spl13_9
    | ~ spl13_14 ),
    inference(avatar_split_clause,[],[f216,f207,f163,f220])).

fof(f216,plain,
    ( ~ r2_hidden(sK0,k1_xboole_0)
    | spl13_9
    | ~ spl13_14 ),
    inference(backward_demodulation,[],[f165,f209])).

fof(f165,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK2))
    | spl13_9 ),
    inference(avatar_component_clause,[],[f163])).

fof(f214,plain,
    ( spl13_14
    | spl13_15
    | ~ spl13_13 ),
    inference(avatar_split_clause,[],[f204,f198,f211,f207])).

fof(f204,plain,
    ( sK0 = sK3(k1_relat_1(sK2))
    | k1_xboole_0 = k1_relat_1(sK2)
    | ~ spl13_13 ),
    inference(resolution,[],[f199,f58])).

fof(f200,plain,
    ( ~ spl13_6
    | spl13_13
    | ~ spl13_10 ),
    inference(avatar_split_clause,[],[f186,f177,f198,f148])).

fof(f177,plain,
    ( spl13_10
  <=> ! [X3,X2] :
        ( sK0 = X2
        | ~ r2_hidden(X2,k10_relat_1(sK2,X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_10])])).

fof(f186,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK2))
        | sK0 = X0
        | ~ v1_relat_1(sK2) )
    | ~ spl13_10 ),
    inference(superposition,[],[f178,f54])).

fof(f54,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(f178,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(X2,k10_relat_1(sK2,X3))
        | sK0 = X2 )
    | ~ spl13_10 ),
    inference(avatar_component_clause,[],[f177])).

fof(f179,plain,
    ( ~ spl13_6
    | spl13_10
    | ~ spl13_5 ),
    inference(avatar_split_clause,[],[f173,f132,f177,f148])).

fof(f173,plain,
    ( ! [X2,X3] :
        ( sK0 = X2
        | ~ v1_relat_1(sK2)
        | ~ r2_hidden(X2,k10_relat_1(sK2,X3)) )
    | ~ spl13_5 ),
    inference(resolution,[],[f169,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,sK5(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f169,plain,
    ( ! [X2,X1] :
        ( ~ r2_hidden(k4_tarski(X1,X2),sK2)
        | sK0 = X1 )
    | ~ spl13_5 ),
    inference(resolution,[],[f145,f93])).

fof(f93,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),X3))
      | X0 = X2 ) ),
    inference(definition_unfolding,[],[f83,f87])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))
    <=> ( r2_hidden(X1,X3)
        & X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t128_zfmisc_1)).

fof(f145,plain,
    ( ! [X1] :
        ( r2_hidden(X1,k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))
        | ~ r2_hidden(X1,sK2) )
    | ~ spl13_5 ),
    inference(resolution,[],[f134,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f166,plain,
    ( ~ spl13_6
    | ~ spl13_9
    | ~ spl13_1
    | ~ spl13_7
    | spl13_3 ),
    inference(avatar_split_clause,[],[f125,f121,f153,f111,f163,f148])).

fof(f111,plain,
    ( spl13_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1])])).

fof(f153,plain,
    ( spl13_7
  <=> v5_relat_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_7])])).

fof(f121,plain,
    ( spl13_3
  <=> r2_hidden(k1_funct_1(sK2,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_3])])).

fof(f125,plain,
    ( ~ v5_relat_1(sK2,sK1)
    | ~ v1_funct_1(sK2)
    | ~ r2_hidden(sK0,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | spl13_3 ),
    inference(resolution,[],[f123,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X2),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(k1_funct_1(X1,X2),X0)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_funct_1)).

fof(f123,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK0),sK1)
    | spl13_3 ),
    inference(avatar_component_clause,[],[f121])).

fof(f156,plain,
    ( spl13_7
    | ~ spl13_5 ),
    inference(avatar_split_clause,[],[f138,f132,f153])).

fof(f138,plain,
    ( v5_relat_1(sK2,sK1)
    | ~ spl13_5 ),
    inference(resolution,[],[f134,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f151,plain,
    ( spl13_6
    | ~ spl13_5 ),
    inference(avatar_split_clause,[],[f136,f132,f148])).

fof(f136,plain,
    ( v1_relat_1(sK2)
    | ~ spl13_5 ),
    inference(resolution,[],[f134,f70])).

fof(f135,plain,(
    spl13_5 ),
    inference(avatar_split_clause,[],[f88,f132])).

fof(f88,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f47,f87])).

fof(f47,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_2)).

fof(f130,plain,(
    spl13_4 ),
    inference(avatar_split_clause,[],[f89,f127])).

fof(f89,plain,(
    v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    inference(definition_unfolding,[],[f46,f87])).

fof(f46,plain,(
    v1_funct_2(sK2,k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f124,plain,(
    ~ spl13_3 ),
    inference(avatar_split_clause,[],[f49,f121])).

fof(f49,plain,(
    ~ r2_hidden(k1_funct_1(sK2,sK0),sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f119,plain,(
    ~ spl13_2 ),
    inference(avatar_split_clause,[],[f48,f116])).

fof(f48,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f25])).

fof(f114,plain,(
    spl13_1 ),
    inference(avatar_split_clause,[],[f45,f111])).

fof(f45,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:14:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.52  % (8717)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.52  % (8711)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.52  % (8727)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.52  % (8713)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.52  % (8730)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.53  % (8710)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.53  % (8739)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.53  % (8732)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.53  % (8712)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.53  % (8736)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.53  % (8733)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.53  % (8714)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.53  % (8738)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.53  % (8715)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.53  % (8726)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.53  % (8721)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.53  % (8718)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.53  % (8740)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.54  % (8724)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.54  % (8731)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.54  % (8728)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.54  % (8722)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.54  % (8723)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.55  % (8729)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.55  % (8734)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.55  % (8720)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.55  % (8728)Refutation not found, incomplete strategy% (8728)------------------------------
% 0.21/0.55  % (8728)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (8719)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.55  % (8727)Refutation not found, incomplete strategy% (8727)------------------------------
% 0.21/0.55  % (8727)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (8735)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.55  % (8716)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.55  % (8737)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.56  % (8739)Refutation found. Thanks to Tanya!
% 0.21/0.56  % SZS status Theorem for theBenchmark
% 0.21/0.56  % (8740)Refutation not found, incomplete strategy% (8740)------------------------------
% 0.21/0.56  % (8740)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % SZS output start Proof for theBenchmark
% 0.21/0.56  % (8740)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (8740)Memory used [KB]: 1663
% 0.21/0.56  % (8740)Time elapsed: 0.153 s
% 0.21/0.56  % (8740)------------------------------
% 0.21/0.56  % (8740)------------------------------
% 0.21/0.56  fof(f548,plain,(
% 0.21/0.56    $false),
% 0.21/0.56    inference(avatar_sat_refutation,[],[f114,f119,f124,f130,f135,f151,f156,f166,f179,f200,f214,f223,f232,f237,f288,f329,f334,f422,f424,f431,f475,f502,f508,f547])).
% 0.21/0.56  fof(f547,plain,(
% 0.21/0.56    ~spl13_31 | ~spl13_34),
% 0.21/0.56    inference(avatar_contradiction_clause,[],[f541])).
% 0.21/0.56  fof(f541,plain,(
% 0.21/0.56    $false | (~spl13_31 | ~spl13_34)),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f59,f90,f514,f61])).
% 0.21/0.56  fof(f61,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f32])).
% 0.21/0.56  fof(f32,plain,(
% 0.21/0.56    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.21/0.56    inference(flattening,[],[f31])).
% 0.21/0.56  fof(f31,plain,(
% 0.21/0.56    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.21/0.56    inference(ennf_transformation,[],[f10])).
% 0.21/0.56  fof(f10,axiom,(
% 0.21/0.56    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.21/0.56  fof(f514,plain,(
% 0.21/0.56    ( ! [X0] : (~r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0))) ) | (~spl13_31 | ~spl13_34)),
% 0.21/0.56    inference(resolution,[],[f509,f430])).
% 0.21/0.56  fof(f430,plain,(
% 0.21/0.56    sP11(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl13_31),
% 0.21/0.56    inference(avatar_component_clause,[],[f428])).
% 0.21/0.56  fof(f428,plain,(
% 0.21/0.56    spl13_31 <=> sP11(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl13_31])])).
% 0.21/0.56  fof(f509,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~sP11(k1_xboole_0,X1) | ~r2_hidden(X0,X1)) ) | ~spl13_34),
% 0.21/0.56    inference(resolution,[],[f501,f107])).
% 0.21/0.56  fof(f107,plain,(
% 0.21/0.56    ( ! [X2,X3,X1] : (r2_hidden(k4_tarski(X3,sK7(X2,X3)),X2) | ~r2_hidden(X3,X1) | ~sP11(X2,X1)) )),
% 0.21/0.56    inference(general_splitting,[],[f81,f106_D])).
% 0.21/0.56  fof(f106,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k1_relset_1(X1,X0,X2) != X1 | sP11(X2,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f106_D])).
% 0.21/0.56  fof(f106_D,plain,(
% 0.21/0.56    ( ! [X1,X2] : (( ! [X0] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k1_relset_1(X1,X0,X2) != X1) ) <=> ~sP11(X2,X1)) )),
% 0.21/0.56    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP11])])).
% 0.21/0.56  fof(f81,plain,(
% 0.21/0.56    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k1_relset_1(X1,X0,X2) != X1 | ~r2_hidden(X3,X1) | r2_hidden(k4_tarski(X3,sK7(X2,X3)),X2)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f42])).
% 0.21/0.56  fof(f42,plain,(
% 0.21/0.56    ! [X0,X1,X2] : ((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.21/0.56    inference(ennf_transformation,[],[f19])).
% 0.21/0.56  fof(f19,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (! [X3] : ~(! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relset_1)).
% 0.21/0.56  fof(f501,plain,(
% 0.21/0.56    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0)) ) | ~spl13_34),
% 0.21/0.56    inference(avatar_component_clause,[],[f500])).
% 0.21/0.56  fof(f500,plain,(
% 0.21/0.56    spl13_34 <=> ! [X1] : ~r2_hidden(X1,k1_xboole_0)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl13_34])])).
% 0.21/0.56  fof(f90,plain,(
% 0.21/0.56    ( ! [X0] : (~v1_xboole_0(k2_enumset1(X0,X0,X0,X0))) )),
% 0.21/0.56    inference(definition_unfolding,[],[f50,f87])).
% 0.21/0.56  fof(f87,plain,(
% 0.21/0.56    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.21/0.56    inference(definition_unfolding,[],[f53,f86])).
% 0.21/0.56  fof(f86,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.21/0.56    inference(definition_unfolding,[],[f60,f65])).
% 0.21/0.56  fof(f65,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f4])).
% 0.21/0.56  fof(f4,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.56  fof(f60,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f3])).
% 0.21/0.56  fof(f3,axiom,(
% 0.21/0.56    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.56  fof(f53,plain,(
% 0.21/0.56    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f2])).
% 0.21/0.56  fof(f2,axiom,(
% 0.21/0.56    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.56  fof(f50,plain,(
% 0.21/0.56    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f5])).
% 0.21/0.56  fof(f5,axiom,(
% 0.21/0.56    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).
% 0.21/0.56  fof(f59,plain,(
% 0.21/0.56    ( ! [X0] : (m1_subset_1(sK4(X0),X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f7])).
% 0.21/0.56  fof(f7,axiom,(
% 0.21/0.56    ! [X0] : ? [X1] : m1_subset_1(X1,X0)),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).
% 0.21/0.56  fof(f508,plain,(
% 0.21/0.56    ~spl13_33),
% 0.21/0.56    inference(avatar_contradiction_clause,[],[f504])).
% 0.21/0.56  fof(f504,plain,(
% 0.21/0.56    $false | ~spl13_33),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f52,f498,f70])).
% 0.21/0.56  fof(f70,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f38])).
% 0.21/0.56  fof(f38,plain,(
% 0.21/0.56    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.56    inference(ennf_transformation,[],[f17])).
% 0.21/0.56  fof(f17,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.56  fof(f498,plain,(
% 0.21/0.56    ( ! [X0] : (~v1_relat_1(X0)) ) | ~spl13_33),
% 0.21/0.56    inference(avatar_component_clause,[],[f497])).
% 0.21/0.56  fof(f497,plain,(
% 0.21/0.56    spl13_33 <=> ! [X0] : ~v1_relat_1(X0)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl13_33])])).
% 0.21/0.56  fof(f52,plain,(
% 0.21/0.56    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f9])).
% 0.21/0.56  fof(f9,axiom,(
% 0.21/0.56    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.21/0.56  fof(f502,plain,(
% 0.21/0.56    spl13_33 | spl13_34 | ~spl13_32),
% 0.21/0.56    inference(avatar_split_clause,[],[f495,f473,f500,f497])).
% 0.21/0.56  fof(f473,plain,(
% 0.21/0.56    spl13_32 <=> ! [X5,X4] : (~v1_relat_1(X5) | ~r2_hidden(X4,k10_relat_1(X5,k1_xboole_0)))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl13_32])])).
% 0.21/0.56  fof(f495,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~r2_hidden(X1,k1_xboole_0) | ~v1_relat_1(X0)) ) | ~spl13_32),
% 0.21/0.56    inference(duplicate_literal_removal,[],[f488])).
% 0.21/0.56  fof(f488,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~r2_hidden(X1,k1_xboole_0) | ~v1_relat_1(X0) | ~v1_relat_1(X0)) ) | ~spl13_32),
% 0.21/0.56    inference(superposition,[],[f474,f481])).
% 0.21/0.56  fof(f481,plain,(
% 0.21/0.56    ( ! [X12] : (k1_xboole_0 = k10_relat_1(X12,k1_xboole_0) | ~v1_relat_1(X12)) ) | ~spl13_32),
% 0.21/0.56    inference(resolution,[],[f474,f58])).
% 0.21/0.56  fof(f58,plain,(
% 0.21/0.56    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.56    inference(cnf_transformation,[],[f30])).
% 0.21/0.56  fof(f30,plain,(
% 0.21/0.56    ! [X0] : (? [X1] : (! [X2,X3,X4,X5,X6] : (r1_xboole_0(X2,X0) | ~r2_hidden(X6,X1) | ~r2_hidden(X5,X6) | ~r2_hidden(X4,X5) | ~r2_hidden(X3,X4) | ~r2_hidden(X2,X3)) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.21/0.56    inference(flattening,[],[f29])).
% 0.21/0.56  fof(f29,plain,(
% 0.21/0.56    ! [X0] : (? [X1] : (! [X2,X3,X4,X5,X6] : (r1_xboole_0(X2,X0) | (~r2_hidden(X6,X1) | ~r2_hidden(X5,X6) | ~r2_hidden(X4,X5) | ~r2_hidden(X3,X4) | ~r2_hidden(X2,X3))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.21/0.56    inference(ennf_transformation,[],[f20])).
% 0.21/0.56  fof(f20,axiom,(
% 0.21/0.56    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4,X5,X6] : ((r2_hidden(X6,X1) & r2_hidden(X5,X6) & r2_hidden(X4,X5) & r2_hidden(X3,X4) & r2_hidden(X2,X3)) => r1_xboole_0(X2,X0)) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_mcart_1)).
% 0.21/0.56  fof(f474,plain,(
% 0.21/0.56    ( ! [X4,X5] : (~r2_hidden(X4,k10_relat_1(X5,k1_xboole_0)) | ~v1_relat_1(X5)) ) | ~spl13_32),
% 0.21/0.56    inference(avatar_component_clause,[],[f473])).
% 0.21/0.56  fof(f475,plain,(
% 0.21/0.56    spl13_32 | spl13_16 | ~spl13_13 | ~spl13_19 | ~spl13_25),
% 0.21/0.56    inference(avatar_split_clause,[],[f469,f326,f234,f198,f220,f473])).
% 0.21/0.56  fof(f220,plain,(
% 0.21/0.56    spl13_16 <=> r2_hidden(sK0,k1_xboole_0)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl13_16])])).
% 0.21/0.56  fof(f198,plain,(
% 0.21/0.56    spl13_13 <=> ! [X0] : (~r2_hidden(X0,k1_relat_1(sK2)) | sK0 = X0)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl13_13])])).
% 0.21/0.56  fof(f234,plain,(
% 0.21/0.56    spl13_19 <=> k1_xboole_0 = sK2),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl13_19])])).
% 0.21/0.56  fof(f326,plain,(
% 0.21/0.56    spl13_25 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl13_25])])).
% 0.21/0.56  fof(f469,plain,(
% 0.21/0.56    ( ! [X4,X5] : (r2_hidden(sK0,k1_xboole_0) | ~v1_relat_1(X5) | ~r2_hidden(X4,k10_relat_1(X5,k1_xboole_0))) ) | (~spl13_13 | ~spl13_19 | ~spl13_25)),
% 0.21/0.56    inference(duplicate_literal_removal,[],[f464])).
% 0.21/0.56  fof(f464,plain,(
% 0.21/0.56    ( ! [X4,X5] : (r2_hidden(sK0,k1_xboole_0) | ~v1_relat_1(X5) | ~r2_hidden(X4,k10_relat_1(X5,k1_xboole_0)) | ~v1_relat_1(X5) | ~r2_hidden(X4,k10_relat_1(X5,k1_xboole_0))) ) | (~spl13_13 | ~spl13_19 | ~spl13_25)),
% 0.21/0.56    inference(superposition,[],[f68,f358])).
% 0.21/0.56  fof(f358,plain,(
% 0.21/0.56    ( ! [X6,X7] : (sK0 = sK5(X6,k1_xboole_0,X7) | ~v1_relat_1(X7) | ~r2_hidden(X6,k10_relat_1(X7,k1_xboole_0))) ) | (~spl13_13 | ~spl13_19 | ~spl13_25)),
% 0.21/0.56    inference(resolution,[],[f353,f68])).
% 0.21/0.56  fof(f353,plain,(
% 0.21/0.56    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0) | sK0 = X0) ) | (~spl13_13 | ~spl13_19 | ~spl13_25)),
% 0.21/0.56    inference(forward_demodulation,[],[f300,f328])).
% 0.21/0.56  fof(f328,plain,(
% 0.21/0.56    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl13_25),
% 0.21/0.56    inference(avatar_component_clause,[],[f326])).
% 0.21/0.56  fof(f300,plain,(
% 0.21/0.56    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(k1_xboole_0)) | sK0 = X0) ) | (~spl13_13 | ~spl13_19)),
% 0.21/0.56    inference(backward_demodulation,[],[f199,f236])).
% 0.21/0.56  fof(f236,plain,(
% 0.21/0.56    k1_xboole_0 = sK2 | ~spl13_19),
% 0.21/0.56    inference(avatar_component_clause,[],[f234])).
% 0.21/0.56  fof(f199,plain,(
% 0.21/0.56    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK2)) | sK0 = X0) ) | ~spl13_13),
% 0.21/0.56    inference(avatar_component_clause,[],[f198])).
% 0.21/0.56  fof(f68,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (r2_hidden(sK5(X0,X1,X2),X1) | ~v1_relat_1(X2) | ~r2_hidden(X0,k10_relat_1(X2,X1))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f37])).
% 0.21/0.56  fof(f37,plain,(
% 0.21/0.56    ! [X0,X1,X2] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.21/0.56    inference(ennf_transformation,[],[f12])).
% 0.21/0.56  fof(f12,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).
% 0.21/0.56  fof(f431,plain,(
% 0.21/0.56    spl13_31 | ~spl13_17 | ~spl13_19),
% 0.21/0.56    inference(avatar_split_clause,[],[f426,f234,f225,f428])).
% 0.21/0.56  fof(f225,plain,(
% 0.21/0.56    spl13_17 <=> sP11(sK2,k2_enumset1(sK0,sK0,sK0,sK0))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl13_17])])).
% 0.21/0.56  fof(f426,plain,(
% 0.21/0.56    sP11(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0)) | (~spl13_17 | ~spl13_19)),
% 0.21/0.56    inference(forward_demodulation,[],[f227,f236])).
% 0.21/0.56  fof(f227,plain,(
% 0.21/0.56    sP11(sK2,k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl13_17),
% 0.21/0.56    inference(avatar_component_clause,[],[f225])).
% 0.21/0.56  fof(f424,plain,(
% 0.21/0.56    spl13_2 | ~spl13_26 | spl13_30),
% 0.21/0.56    inference(avatar_contradiction_clause,[],[f423])).
% 0.21/0.56  fof(f423,plain,(
% 0.21/0.56    $false | (spl13_2 | ~spl13_26 | spl13_30)),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f118,f333,f52,f421,f78])).
% 0.21/0.56  fof(f78,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f41])).
% 0.21/0.56  fof(f41,plain,(
% 0.21/0.56    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.56    inference(flattening,[],[f40])).
% 0.21/0.56  fof(f40,plain,(
% 0.21/0.56    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.56    inference(ennf_transformation,[],[f21])).
% 0.21/0.56  fof(f21,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.56  fof(f421,plain,(
% 0.21/0.56    k2_enumset1(sK0,sK0,sK0,sK0) != k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k1_xboole_0) | spl13_30),
% 0.21/0.56    inference(avatar_component_clause,[],[f419])).
% 0.21/0.56  fof(f419,plain,(
% 0.21/0.56    spl13_30 <=> k2_enumset1(sK0,sK0,sK0,sK0) = k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k1_xboole_0)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl13_30])])).
% 0.21/0.56  fof(f333,plain,(
% 0.21/0.56    v1_funct_2(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0),sK1) | ~spl13_26),
% 0.21/0.56    inference(avatar_component_clause,[],[f331])).
% 0.21/0.56  fof(f331,plain,(
% 0.21/0.56    spl13_26 <=> v1_funct_2(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl13_26])])).
% 0.21/0.56  fof(f118,plain,(
% 0.21/0.56    k1_xboole_0 != sK1 | spl13_2),
% 0.21/0.56    inference(avatar_component_clause,[],[f116])).
% 0.21/0.56  fof(f116,plain,(
% 0.21/0.56    spl13_2 <=> k1_xboole_0 = sK1),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl13_2])])).
% 0.21/0.56  fof(f422,plain,(
% 0.21/0.56    ~spl13_30 | spl13_18 | ~spl13_19),
% 0.21/0.56    inference(avatar_split_clause,[],[f406,f234,f229,f419])).
% 0.21/0.56  fof(f229,plain,(
% 0.21/0.56    spl13_18 <=> k2_enumset1(sK0,sK0,sK0,sK0) = k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl13_18])])).
% 0.21/0.56  fof(f406,plain,(
% 0.21/0.56    k2_enumset1(sK0,sK0,sK0,sK0) != k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k1_xboole_0) | (spl13_18 | ~spl13_19)),
% 0.21/0.56    inference(forward_demodulation,[],[f231,f236])).
% 0.21/0.56  fof(f231,plain,(
% 0.21/0.56    k2_enumset1(sK0,sK0,sK0,sK0) != k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) | spl13_18),
% 0.21/0.56    inference(avatar_component_clause,[],[f229])).
% 0.21/0.56  fof(f334,plain,(
% 0.21/0.56    spl13_26 | ~spl13_4 | ~spl13_19),
% 0.21/0.56    inference(avatar_split_clause,[],[f291,f234,f127,f331])).
% 0.21/0.56  fof(f127,plain,(
% 0.21/0.56    spl13_4 <=> v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl13_4])])).
% 0.21/0.56  fof(f291,plain,(
% 0.21/0.56    v1_funct_2(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0),sK1) | (~spl13_4 | ~spl13_19)),
% 0.21/0.56    inference(backward_demodulation,[],[f129,f236])).
% 0.21/0.56  fof(f129,plain,(
% 0.21/0.56    v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1) | ~spl13_4),
% 0.21/0.56    inference(avatar_component_clause,[],[f127])).
% 0.21/0.56  fof(f329,plain,(
% 0.21/0.56    spl13_25 | ~spl13_14 | ~spl13_19),
% 0.21/0.56    inference(avatar_split_clause,[],[f317,f234,f207,f326])).
% 0.21/0.56  fof(f207,plain,(
% 0.21/0.56    spl13_14 <=> k1_xboole_0 = k1_relat_1(sK2)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl13_14])])).
% 0.21/0.56  fof(f317,plain,(
% 0.21/0.56    k1_xboole_0 = k1_relat_1(k1_xboole_0) | (~spl13_14 | ~spl13_19)),
% 0.21/0.56    inference(forward_demodulation,[],[f209,f236])).
% 0.21/0.56  fof(f209,plain,(
% 0.21/0.56    k1_xboole_0 = k1_relat_1(sK2) | ~spl13_14),
% 0.21/0.56    inference(avatar_component_clause,[],[f207])).
% 0.21/0.56  fof(f288,plain,(
% 0.21/0.56    spl13_14 | spl13_9 | ~spl13_15),
% 0.21/0.56    inference(avatar_split_clause,[],[f258,f211,f163,f207])).
% 0.21/0.56  fof(f163,plain,(
% 0.21/0.56    spl13_9 <=> r2_hidden(sK0,k1_relat_1(sK2))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl13_9])])).
% 0.21/0.56  fof(f211,plain,(
% 0.21/0.56    spl13_15 <=> sK0 = sK3(k1_relat_1(sK2))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl13_15])])).
% 0.21/0.56  fof(f258,plain,(
% 0.21/0.56    r2_hidden(sK0,k1_relat_1(sK2)) | k1_xboole_0 = k1_relat_1(sK2) | ~spl13_15),
% 0.21/0.56    inference(superposition,[],[f58,f213])).
% 0.21/0.56  fof(f213,plain,(
% 0.21/0.56    sK0 = sK3(k1_relat_1(sK2)) | ~spl13_15),
% 0.21/0.56    inference(avatar_component_clause,[],[f211])).
% 0.21/0.56  fof(f237,plain,(
% 0.21/0.56    spl13_19 | ~spl13_6 | ~spl13_14),
% 0.21/0.56    inference(avatar_split_clause,[],[f218,f207,f148,f234])).
% 0.21/0.56  fof(f148,plain,(
% 0.21/0.56    spl13_6 <=> v1_relat_1(sK2)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl13_6])])).
% 0.21/0.56  fof(f218,plain,(
% 0.21/0.56    ~v1_relat_1(sK2) | k1_xboole_0 = sK2 | ~spl13_14),
% 0.21/0.56    inference(trivial_inequality_removal,[],[f217])).
% 0.21/0.56  fof(f217,plain,(
% 0.21/0.56    k1_xboole_0 != k1_xboole_0 | ~v1_relat_1(sK2) | k1_xboole_0 = sK2 | ~spl13_14),
% 0.21/0.56    inference(superposition,[],[f55,f209])).
% 0.21/0.56  fof(f55,plain,(
% 0.21/0.56    ( ! [X0] : (k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0) | k1_xboole_0 = X0) )),
% 0.21/0.56    inference(cnf_transformation,[],[f28])).
% 0.21/0.56  fof(f28,plain,(
% 0.21/0.56    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.56    inference(flattening,[],[f27])).
% 0.21/0.56  fof(f27,plain,(
% 0.21/0.56    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.56    inference(ennf_transformation,[],[f14])).
% 0.21/0.56  fof(f14,axiom,(
% 0.21/0.56    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).
% 0.21/0.56  fof(f232,plain,(
% 0.21/0.56    spl13_17 | ~spl13_18 | ~spl13_5),
% 0.21/0.56    inference(avatar_split_clause,[],[f142,f132,f229,f225])).
% 0.21/0.56  fof(f132,plain,(
% 0.21/0.56    spl13_5 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl13_5])])).
% 0.21/0.56  fof(f142,plain,(
% 0.21/0.56    k2_enumset1(sK0,sK0,sK0,sK0) != k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) | sP11(sK2,k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl13_5),
% 0.21/0.56    inference(resolution,[],[f134,f106])).
% 0.21/0.56  fof(f134,plain,(
% 0.21/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) | ~spl13_5),
% 0.21/0.56    inference(avatar_component_clause,[],[f132])).
% 0.21/0.56  fof(f223,plain,(
% 0.21/0.56    ~spl13_16 | spl13_9 | ~spl13_14),
% 0.21/0.56    inference(avatar_split_clause,[],[f216,f207,f163,f220])).
% 0.21/0.56  fof(f216,plain,(
% 0.21/0.56    ~r2_hidden(sK0,k1_xboole_0) | (spl13_9 | ~spl13_14)),
% 0.21/0.56    inference(backward_demodulation,[],[f165,f209])).
% 0.21/0.56  fof(f165,plain,(
% 0.21/0.56    ~r2_hidden(sK0,k1_relat_1(sK2)) | spl13_9),
% 0.21/0.56    inference(avatar_component_clause,[],[f163])).
% 0.21/0.56  fof(f214,plain,(
% 0.21/0.56    spl13_14 | spl13_15 | ~spl13_13),
% 0.21/0.56    inference(avatar_split_clause,[],[f204,f198,f211,f207])).
% 0.21/0.56  fof(f204,plain,(
% 0.21/0.56    sK0 = sK3(k1_relat_1(sK2)) | k1_xboole_0 = k1_relat_1(sK2) | ~spl13_13),
% 0.21/0.56    inference(resolution,[],[f199,f58])).
% 0.21/0.56  fof(f200,plain,(
% 0.21/0.56    ~spl13_6 | spl13_13 | ~spl13_10),
% 0.21/0.56    inference(avatar_split_clause,[],[f186,f177,f198,f148])).
% 0.21/0.56  fof(f177,plain,(
% 0.21/0.56    spl13_10 <=> ! [X3,X2] : (sK0 = X2 | ~r2_hidden(X2,k10_relat_1(sK2,X3)))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl13_10])])).
% 0.21/0.56  fof(f186,plain,(
% 0.21/0.56    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK2)) | sK0 = X0 | ~v1_relat_1(sK2)) ) | ~spl13_10),
% 0.21/0.56    inference(superposition,[],[f178,f54])).
% 0.21/0.56  fof(f54,plain,(
% 0.21/0.56    ( ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f26])).
% 0.21/0.56  fof(f26,plain,(
% 0.21/0.56    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.56    inference(ennf_transformation,[],[f13])).
% 0.21/0.56  fof(f13,axiom,(
% 0.21/0.56    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).
% 0.21/0.56  fof(f178,plain,(
% 0.21/0.56    ( ! [X2,X3] : (~r2_hidden(X2,k10_relat_1(sK2,X3)) | sK0 = X2) ) | ~spl13_10),
% 0.21/0.56    inference(avatar_component_clause,[],[f177])).
% 0.21/0.56  fof(f179,plain,(
% 0.21/0.56    ~spl13_6 | spl13_10 | ~spl13_5),
% 0.21/0.56    inference(avatar_split_clause,[],[f173,f132,f177,f148])).
% 0.21/0.56  fof(f173,plain,(
% 0.21/0.56    ( ! [X2,X3] : (sK0 = X2 | ~v1_relat_1(sK2) | ~r2_hidden(X2,k10_relat_1(sK2,X3))) ) | ~spl13_5),
% 0.21/0.56    inference(resolution,[],[f169,f67])).
% 0.21/0.56  fof(f67,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,sK5(X0,X1,X2)),X2) | ~v1_relat_1(X2) | ~r2_hidden(X0,k10_relat_1(X2,X1))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f37])).
% 0.21/0.56  fof(f169,plain,(
% 0.21/0.56    ( ! [X2,X1] : (~r2_hidden(k4_tarski(X1,X2),sK2) | sK0 = X1) ) | ~spl13_5),
% 0.21/0.56    inference(resolution,[],[f145,f93])).
% 0.21/0.56  fof(f93,plain,(
% 0.21/0.56    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),X3)) | X0 = X2) )),
% 0.21/0.56    inference(definition_unfolding,[],[f83,f87])).
% 0.21/0.56  fof(f83,plain,(
% 0.21/0.56    ( ! [X2,X0,X3,X1] : (X0 = X2 | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f6])).
% 0.21/0.56  fof(f6,axiom,(
% 0.21/0.56    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) <=> (r2_hidden(X1,X3) & X0 = X2))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t128_zfmisc_1)).
% 0.21/0.56  fof(f145,plain,(
% 0.21/0.56    ( ! [X1] : (r2_hidden(X1,k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) | ~r2_hidden(X1,sK2)) ) | ~spl13_5),
% 0.21/0.56    inference(resolution,[],[f134,f62])).
% 0.21/0.56  fof(f62,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f33])).
% 0.21/0.56  fof(f33,plain,(
% 0.21/0.56    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.56    inference(ennf_transformation,[],[f8])).
% 0.21/0.56  fof(f8,axiom,(
% 0.21/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 0.21/0.56  fof(f166,plain,(
% 0.21/0.56    ~spl13_6 | ~spl13_9 | ~spl13_1 | ~spl13_7 | spl13_3),
% 0.21/0.56    inference(avatar_split_clause,[],[f125,f121,f153,f111,f163,f148])).
% 0.21/0.56  fof(f111,plain,(
% 0.21/0.56    spl13_1 <=> v1_funct_1(sK2)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl13_1])])).
% 0.21/0.56  fof(f153,plain,(
% 0.21/0.56    spl13_7 <=> v5_relat_1(sK2,sK1)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl13_7])])).
% 0.21/0.56  fof(f121,plain,(
% 0.21/0.56    spl13_3 <=> r2_hidden(k1_funct_1(sK2,sK0),sK1)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl13_3])])).
% 0.21/0.56  fof(f125,plain,(
% 0.21/0.56    ~v5_relat_1(sK2,sK1) | ~v1_funct_1(sK2) | ~r2_hidden(sK0,k1_relat_1(sK2)) | ~v1_relat_1(sK2) | spl13_3),
% 0.21/0.56    inference(resolution,[],[f123,f63])).
% 0.21/0.56  fof(f63,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~v5_relat_1(X1,X0) | ~v1_funct_1(X1) | ~r2_hidden(X2,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f35])).
% 0.21/0.56  fof(f35,plain,(
% 0.21/0.56    ! [X0,X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.56    inference(flattening,[],[f34])).
% 0.21/0.56  fof(f34,plain,(
% 0.21/0.56    ! [X0,X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.56    inference(ennf_transformation,[],[f15])).
% 0.21/0.56  fof(f15,axiom,(
% 0.21/0.56    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X2),X0)))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_funct_1)).
% 0.21/0.56  fof(f123,plain,(
% 0.21/0.56    ~r2_hidden(k1_funct_1(sK2,sK0),sK1) | spl13_3),
% 0.21/0.56    inference(avatar_component_clause,[],[f121])).
% 0.21/0.56  fof(f156,plain,(
% 0.21/0.56    spl13_7 | ~spl13_5),
% 0.21/0.56    inference(avatar_split_clause,[],[f138,f132,f153])).
% 0.21/0.56  fof(f138,plain,(
% 0.21/0.56    v5_relat_1(sK2,sK1) | ~spl13_5),
% 0.21/0.56    inference(resolution,[],[f134,f72])).
% 0.21/0.56  fof(f72,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f39])).
% 0.21/0.56  fof(f39,plain,(
% 0.21/0.56    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.56    inference(ennf_transformation,[],[f18])).
% 0.21/0.56  fof(f18,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.56  fof(f151,plain,(
% 0.21/0.56    spl13_6 | ~spl13_5),
% 0.21/0.56    inference(avatar_split_clause,[],[f136,f132,f148])).
% 0.21/0.56  fof(f136,plain,(
% 0.21/0.56    v1_relat_1(sK2) | ~spl13_5),
% 0.21/0.56    inference(resolution,[],[f134,f70])).
% 0.21/0.56  fof(f135,plain,(
% 0.21/0.56    spl13_5),
% 0.21/0.56    inference(avatar_split_clause,[],[f88,f132])).
% 0.21/0.56  fof(f88,plain,(
% 0.21/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 0.21/0.56    inference(definition_unfolding,[],[f47,f87])).
% 0.21/0.56  fof(f47,plain,(
% 0.21/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 0.21/0.56    inference(cnf_transformation,[],[f25])).
% 0.21/0.56  fof(f25,plain,(
% 0.21/0.56    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 0.21/0.56    inference(flattening,[],[f24])).
% 0.21/0.56  fof(f24,plain,(
% 0.21/0.56    ? [X0,X1,X2] : ((~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 0.21/0.56    inference(ennf_transformation,[],[f23])).
% 0.21/0.56  fof(f23,negated_conjecture,(
% 0.21/0.56    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 0.21/0.56    inference(negated_conjecture,[],[f22])).
% 0.21/0.56  fof(f22,conjecture,(
% 0.21/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_2)).
% 0.21/0.56  fof(f130,plain,(
% 0.21/0.56    spl13_4),
% 0.21/0.56    inference(avatar_split_clause,[],[f89,f127])).
% 0.21/0.56  fof(f89,plain,(
% 0.21/0.56    v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 0.21/0.56    inference(definition_unfolding,[],[f46,f87])).
% 0.21/0.56  fof(f46,plain,(
% 0.21/0.56    v1_funct_2(sK2,k1_tarski(sK0),sK1)),
% 0.21/0.56    inference(cnf_transformation,[],[f25])).
% 0.21/0.56  fof(f124,plain,(
% 0.21/0.56    ~spl13_3),
% 0.21/0.56    inference(avatar_split_clause,[],[f49,f121])).
% 0.21/0.56  fof(f49,plain,(
% 0.21/0.56    ~r2_hidden(k1_funct_1(sK2,sK0),sK1)),
% 0.21/0.56    inference(cnf_transformation,[],[f25])).
% 0.21/0.56  fof(f119,plain,(
% 0.21/0.56    ~spl13_2),
% 0.21/0.56    inference(avatar_split_clause,[],[f48,f116])).
% 0.21/0.56  fof(f48,plain,(
% 0.21/0.56    k1_xboole_0 != sK1),
% 0.21/0.56    inference(cnf_transformation,[],[f25])).
% 0.21/0.56  fof(f114,plain,(
% 0.21/0.56    spl13_1),
% 0.21/0.56    inference(avatar_split_clause,[],[f45,f111])).
% 0.21/0.56  fof(f45,plain,(
% 0.21/0.56    v1_funct_1(sK2)),
% 0.21/0.56    inference(cnf_transformation,[],[f25])).
% 0.21/0.56  % SZS output end Proof for theBenchmark
% 0.21/0.56  % (8739)------------------------------
% 0.21/0.56  % (8739)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (8739)Termination reason: Refutation
% 0.21/0.56  
% 0.21/0.56  % (8739)Memory used [KB]: 11001
% 0.21/0.56  % (8739)Time elapsed: 0.138 s
% 0.21/0.56  % (8739)------------------------------
% 0.21/0.56  % (8739)------------------------------
% 0.21/0.56  % (8700)Success in time 0.201 s
%------------------------------------------------------------------------------
