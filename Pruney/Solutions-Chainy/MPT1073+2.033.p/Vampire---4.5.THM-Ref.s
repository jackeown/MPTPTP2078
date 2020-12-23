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
% DateTime   : Thu Dec  3 13:08:00 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  184 ( 290 expanded)
%              Number of leaves         :   48 ( 124 expanded)
%              Depth                    :    9
%              Number of atoms          :  541 ( 895 expanded)
%              Number of equality atoms :   85 ( 138 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1092,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f101,f106,f111,f116,f124,f161,f167,f296,f351,f363,f381,f408,f425,f461,f466,f507,f509,f528,f529,f643,f651,f677,f849,f1026,f1091])).

fof(f1091,plain,
    ( ~ spl13_39
    | ~ spl13_102 ),
    inference(avatar_contradiction_clause,[],[f1090])).

fof(f1090,plain,
    ( $false
    | ~ spl13_39
    | ~ spl13_102 ),
    inference(subsumption_resolution,[],[f1088,f460])).

fof(f460,plain,
    ( sK6 = k1_funct_1(sK9,sK11(sK6,sK9))
    | ~ spl13_39 ),
    inference(avatar_component_clause,[],[f458])).

fof(f458,plain,
    ( spl13_39
  <=> sK6 = k1_funct_1(sK9,sK11(sK6,sK9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_39])])).

fof(f1088,plain,
    ( sK6 != k1_funct_1(sK9,sK11(sK6,sK9))
    | ~ spl13_102 ),
    inference(unit_resulting_resolution,[],[f1025,f60])).

fof(f60,plain,(
    ! [X4] :
      ( sK6 != k1_funct_1(sK9,X4)
      | ~ m1_subset_1(X4,sK7) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,
    ( ! [X4] :
        ( sK6 != k1_funct_1(sK9,X4)
        | ~ m1_subset_1(X4,sK7) )
    & r2_hidden(sK6,k2_relset_1(sK7,sK8,sK9))
    & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
    & v1_funct_2(sK9,sK7,sK8)
    & v1_funct_1(sK9) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9])],[f16,f40])).

fof(f40,plain,
    ( ? [X0,X1,X2,X3] :
        ( ! [X4] :
            ( k1_funct_1(X3,X4) != X0
            | ~ m1_subset_1(X4,X1) )
        & r2_hidden(X0,k2_relset_1(X1,X2,X3))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(X3,X1,X2)
        & v1_funct_1(X3) )
   => ( ! [X4] :
          ( sK6 != k1_funct_1(sK9,X4)
          | ~ m1_subset_1(X4,sK7) )
      & r2_hidden(sK6,k2_relset_1(sK7,sK8,sK9))
      & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
      & v1_funct_2(sK9,sK7,sK8)
      & v1_funct_1(sK9) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(X3,X4) != X0
          | ~ m1_subset_1(X4,X1) )
      & r2_hidden(X0,k2_relset_1(X1,X2,X3))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & v1_funct_2(X3,X1,X2)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(X3,X4) != X0
          | ~ m1_subset_1(X4,X1) )
      & r2_hidden(X0,k2_relset_1(X1,X2,X3))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & v1_funct_2(X3,X1,X2)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
       => ~ ( ! [X4] :
                ( m1_subset_1(X4,X1)
               => k1_funct_1(X3,X4) != X0 )
            & r2_hidden(X0,k2_relset_1(X1,X2,X3)) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(X3,X1,X2)
        & v1_funct_1(X3) )
     => ~ ( ! [X4] :
              ( m1_subset_1(X4,X1)
             => k1_funct_1(X3,X4) != X0 )
          & r2_hidden(X0,k2_relset_1(X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t190_funct_2)).

fof(f1025,plain,
    ( m1_subset_1(sK11(sK6,sK9),sK7)
    | ~ spl13_102 ),
    inference(avatar_component_clause,[],[f1023])).

fof(f1023,plain,
    ( spl13_102
  <=> m1_subset_1(sK11(sK6,sK9),sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_102])])).

fof(f1026,plain,
    ( spl13_102
    | ~ spl13_63 ),
    inference(avatar_split_clause,[],[f1018,f674,f1023])).

fof(f674,plain,
    ( spl13_63
  <=> r2_hidden(sK11(sK6,sK9),sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_63])])).

fof(f1018,plain,
    ( m1_subset_1(sK11(sK6,sK9),sK7)
    | ~ spl13_63 ),
    inference(unit_resulting_resolution,[],[f676,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f676,plain,
    ( r2_hidden(sK11(sK6,sK9),sK7)
    | ~ spl13_63 ),
    inference(avatar_component_clause,[],[f674])).

fof(f849,plain,
    ( ~ spl13_48
    | ~ spl13_59 ),
    inference(avatar_contradiction_clause,[],[f848])).

fof(f848,plain,
    ( $false
    | ~ spl13_48
    | ~ spl13_59 ),
    inference(subsumption_resolution,[],[f719,f131])).

fof(f131,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f61,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f61,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f719,plain,
    ( r2_hidden(sK6,k1_xboole_0)
    | ~ spl13_48
    | ~ spl13_59 ),
    inference(backward_demodulation,[],[f525,f649])).

fof(f649,plain,
    ( k1_xboole_0 = sK8
    | ~ spl13_59 ),
    inference(avatar_component_clause,[],[f647])).

fof(f647,plain,
    ( spl13_59
  <=> k1_xboole_0 = sK8 ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_59])])).

fof(f525,plain,
    ( r2_hidden(sK6,sK8)
    | ~ spl13_48 ),
    inference(avatar_component_clause,[],[f523])).

fof(f523,plain,
    ( spl13_48
  <=> r2_hidden(sK6,sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_48])])).

fof(f677,plain,
    ( spl13_63
    | ~ spl13_40
    | ~ spl13_58 ),
    inference(avatar_split_clause,[],[f655,f637,f463,f674])).

fof(f463,plain,
    ( spl13_40
  <=> r2_hidden(sK11(sK6,sK9),k1_relat_1(sK9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_40])])).

fof(f637,plain,
    ( spl13_58
  <=> sK7 = k1_relat_1(sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_58])])).

fof(f655,plain,
    ( r2_hidden(sK11(sK6,sK9),sK7)
    | ~ spl13_40
    | ~ spl13_58 ),
    inference(backward_demodulation,[],[f465,f639])).

fof(f639,plain,
    ( sK7 = k1_relat_1(sK9)
    | ~ spl13_58 ),
    inference(avatar_component_clause,[],[f637])).

fof(f465,plain,
    ( r2_hidden(sK11(sK6,sK9),k1_relat_1(sK9))
    | ~ spl13_40 ),
    inference(avatar_component_clause,[],[f463])).

fof(f651,plain,
    ( spl13_59
    | ~ spl13_57 ),
    inference(avatar_split_clause,[],[f645,f633,f647])).

fof(f633,plain,
    ( spl13_57
  <=> sP3(sK7,sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_57])])).

fof(f645,plain,
    ( k1_xboole_0 = sK8
    | ~ spl13_57 ),
    inference(resolution,[],[f635,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ sP3(X0,X1)
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP3(X0,X1) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP3(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f635,plain,
    ( sP3(sK7,sK8)
    | ~ spl13_57 ),
    inference(avatar_component_clause,[],[f633])).

fof(f643,plain,
    ( spl13_57
    | spl13_58
    | ~ spl13_3
    | ~ spl13_23
    | ~ spl13_29 ),
    inference(avatar_split_clause,[],[f642,f348,f292,f108,f637,f633])).

fof(f108,plain,
    ( spl13_3
  <=> v1_funct_2(sK9,sK7,sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_3])])).

fof(f292,plain,
    ( spl13_23
  <=> sP4(sK7,sK9,sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_23])])).

fof(f348,plain,
    ( spl13_29
  <=> k1_relset_1(sK7,sK8,sK9) = k1_relat_1(sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_29])])).

fof(f642,plain,
    ( sK7 = k1_relat_1(sK9)
    | sP3(sK7,sK8)
    | ~ spl13_3
    | ~ spl13_23
    | ~ spl13_29 ),
    inference(subsumption_resolution,[],[f641,f294])).

fof(f294,plain,
    ( sP4(sK7,sK9,sK8)
    | ~ spl13_23 ),
    inference(avatar_component_clause,[],[f292])).

fof(f641,plain,
    ( sK7 = k1_relat_1(sK9)
    | sP3(sK7,sK8)
    | ~ sP4(sK7,sK9,sK8)
    | ~ spl13_3
    | ~ spl13_29 ),
    inference(subsumption_resolution,[],[f628,f110])).

fof(f110,plain,
    ( v1_funct_2(sK9,sK7,sK8)
    | ~ spl13_3 ),
    inference(avatar_component_clause,[],[f108])).

fof(f628,plain,
    ( sK7 = k1_relat_1(sK9)
    | ~ v1_funct_2(sK9,sK7,sK8)
    | sP3(sK7,sK8)
    | ~ sP4(sK7,sK9,sK8)
    | ~ spl13_29 ),
    inference(superposition,[],[f350,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X2,X1) = X0
      | ~ v1_funct_2(X1,X0,X2)
      | sP3(X0,X2)
      | ~ sP4(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | sP3(X0,X2)
      | ~ sP4(X0,X1,X2) ) ),
    inference(rectify,[],[f53])).

fof(f53,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | sP3(X0,X1)
      | ~ sP4(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | sP3(X0,X1)
      | ~ sP4(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f350,plain,
    ( k1_relset_1(sK7,sK8,sK9) = k1_relat_1(sK9)
    | ~ spl13_29 ),
    inference(avatar_component_clause,[],[f348])).

fof(f529,plain,
    ( k2_relset_1(sK7,sK8,sK9) != k2_relat_1(sK9)
    | ~ sP12(k2_relat_1(sK9))
    | sP12(k2_relset_1(sK7,sK8,sK9)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f528,plain,
    ( spl13_48
    | spl13_44
    | ~ spl13_45 ),
    inference(avatar_split_clause,[],[f527,f504,f499,f523])).

fof(f499,plain,
    ( spl13_44
  <=> v1_xboole_0(sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_44])])).

fof(f504,plain,
    ( spl13_45
  <=> m1_subset_1(sK6,sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_45])])).

fof(f527,plain,
    ( r2_hidden(sK6,sK8)
    | spl13_44
    | ~ spl13_45 ),
    inference(subsumption_resolution,[],[f521,f501])).

fof(f501,plain,
    ( ~ v1_xboole_0(sK8)
    | spl13_44 ),
    inference(avatar_component_clause,[],[f499])).

fof(f521,plain,
    ( v1_xboole_0(sK8)
    | r2_hidden(sK6,sK8)
    | ~ spl13_45 ),
    inference(resolution,[],[f506,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f506,plain,
    ( m1_subset_1(sK6,sK8)
    | ~ spl13_45 ),
    inference(avatar_component_clause,[],[f504])).

fof(f509,plain,
    ( ~ spl13_44
    | spl13_19
    | ~ spl13_35 ),
    inference(avatar_split_clause,[],[f508,f422,f232,f499])).

fof(f232,plain,
    ( spl13_19
  <=> sP12(k2_relat_1(sK9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_19])])).

fof(f422,plain,
    ( spl13_35
  <=> m1_subset_1(k2_relat_1(sK9),k1_zfmisc_1(sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_35])])).

fof(f508,plain,
    ( ~ v1_xboole_0(sK8)
    | spl13_19
    | ~ spl13_35 ),
    inference(subsumption_resolution,[],[f495,f234])).

fof(f234,plain,
    ( ~ sP12(k2_relat_1(sK9))
    | spl13_19 ),
    inference(avatar_component_clause,[],[f232])).

fof(f495,plain,
    ( ~ v1_xboole_0(sK8)
    | sP12(k2_relat_1(sK9))
    | ~ spl13_35 ),
    inference(resolution,[],[f424,f95])).

fof(f95,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | sP12(X1) ) ),
    inference(cnf_transformation,[],[f95_D])).

fof(f95_D,plain,(
    ! [X1] :
      ( ! [X2] :
          ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
          | ~ v1_xboole_0(X2) )
    <=> ~ sP12(X1) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP12])])).

fof(f424,plain,
    ( m1_subset_1(k2_relat_1(sK9),k1_zfmisc_1(sK8))
    | ~ spl13_35 ),
    inference(avatar_component_clause,[],[f422])).

fof(f507,plain,
    ( spl13_45
    | ~ spl13_33
    | ~ spl13_35 ),
    inference(avatar_split_clause,[],[f492,f422,f378,f504])).

fof(f378,plain,
    ( spl13_33
  <=> r2_hidden(sK6,k2_relat_1(sK9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_33])])).

fof(f492,plain,
    ( m1_subset_1(sK6,sK8)
    | ~ spl13_33
    | ~ spl13_35 ),
    inference(unit_resulting_resolution,[],[f380,f424,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f380,plain,
    ( r2_hidden(sK6,k2_relat_1(sK9))
    | ~ spl13_33 ),
    inference(avatar_component_clause,[],[f378])).

fof(f466,plain,
    ( spl13_40
    | ~ spl13_34 ),
    inference(avatar_split_clause,[],[f432,f400,f463])).

fof(f400,plain,
    ( spl13_34
  <=> sP0(sK6,sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_34])])).

fof(f432,plain,
    ( r2_hidden(sK11(sK6,sK9),k1_relat_1(sK9))
    | ~ spl13_34 ),
    inference(unit_resulting_resolution,[],[f402,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK11(X0,X1),k1_relat_1(X1))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ! [X2] :
            ( k1_funct_1(X1,X2) != X0
            | ~ r2_hidden(X2,k1_relat_1(X1)) ) )
      & ( ( k1_funct_1(X1,sK11(X0,X1)) = X0
          & r2_hidden(sK11(X0,X1),k1_relat_1(X1)) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f48,f49])).

fof(f49,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( k1_funct_1(X1,X3) = X0
          & r2_hidden(X3,k1_relat_1(X1)) )
     => ( k1_funct_1(X1,sK11(X0,X1)) = X0
        & r2_hidden(sK11(X0,X1),k1_relat_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ! [X2] :
            ( k1_funct_1(X1,X2) != X0
            | ~ r2_hidden(X2,k1_relat_1(X1)) ) )
      & ( ? [X3] :
            ( k1_funct_1(X1,X3) = X0
            & r2_hidden(X3,k1_relat_1(X1)) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f47])).

fof(f47,plain,(
    ! [X2,X0] :
      ( ( sP0(X2,X0)
        | ! [X3] :
            ( k1_funct_1(X0,X3) != X2
            | ~ r2_hidden(X3,k1_relat_1(X0)) ) )
      & ( ? [X3] :
            ( k1_funct_1(X0,X3) = X2
            & r2_hidden(X3,k1_relat_1(X0)) )
        | ~ sP0(X2,X0) ) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X2,X0] :
      ( sP0(X2,X0)
    <=> ? [X3] :
          ( k1_funct_1(X0,X3) = X2
          & r2_hidden(X3,k1_relat_1(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f402,plain,
    ( sP0(sK6,sK9)
    | ~ spl13_34 ),
    inference(avatar_component_clause,[],[f400])).

fof(f461,plain,
    ( spl13_39
    | ~ spl13_34 ),
    inference(avatar_split_clause,[],[f433,f400,f458])).

fof(f433,plain,
    ( sK6 = k1_funct_1(sK9,sK11(sK6,sK9))
    | ~ spl13_34 ),
    inference(unit_resulting_resolution,[],[f402,f69])).

% (22577)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
fof(f69,plain,(
    ! [X0,X1] :
      ( k1_funct_1(X1,sK11(X0,X1)) = X0
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f425,plain,
    ( spl13_35
    | ~ spl13_2
    | ~ spl13_30 ),
    inference(avatar_split_clause,[],[f420,f360,f103,f422])).

fof(f103,plain,
    ( spl13_2
  <=> m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_2])])).

fof(f360,plain,
    ( spl13_30
  <=> k2_relset_1(sK7,sK8,sK9) = k2_relat_1(sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_30])])).

fof(f420,plain,
    ( m1_subset_1(k2_relat_1(sK9),k1_zfmisc_1(sK8))
    | ~ spl13_2
    | ~ spl13_30 ),
    inference(forward_demodulation,[],[f410,f362])).

fof(f362,plain,
    ( k2_relset_1(sK7,sK8,sK9) = k2_relat_1(sK9)
    | ~ spl13_30 ),
    inference(avatar_component_clause,[],[f360])).

fof(f410,plain,
    ( m1_subset_1(k2_relset_1(sK7,sK8,sK9),k1_zfmisc_1(sK8))
    | ~ spl13_2 ),
    inference(unit_resulting_resolution,[],[f105,f78])).

% (22582)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% (22579)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
fof(f78,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(f105,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
    | ~ spl13_2 ),
    inference(avatar_component_clause,[],[f103])).

fof(f408,plain,
    ( spl13_34
    | ~ spl13_11
    | ~ spl13_33 ),
    inference(avatar_split_clause,[],[f407,f378,f164,f400])).

fof(f164,plain,
    ( spl13_11
  <=> sP2(sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_11])])).

fof(f407,plain,
    ( sP0(sK6,sK9)
    | ~ spl13_11
    | ~ spl13_33 ),
    inference(subsumption_resolution,[],[f395,f166])).

fof(f166,plain,
    ( sP2(sK9)
    | ~ spl13_11 ),
    inference(avatar_component_clause,[],[f164])).

fof(f395,plain,
    ( sP0(sK6,sK9)
    | ~ sP2(sK9)
    | ~ spl13_33 ),
    inference(resolution,[],[f380,f220])).

fof(f220,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k2_relat_1(X1))
      | sP0(X0,X1)
      | ~ sP2(X1) ) ),
    inference(resolution,[],[f64,f89])).

fof(f89,plain,(
    ! [X0] :
      ( sP1(X0,k2_relat_1(X0))
      | ~ sP2(X0) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
      | k2_relat_1(X0) != X1
      | ~ sP2(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ~ sP1(X0,X1) )
          & ( sP1(X0,X1)
            | k2_relat_1(X0) != X1 ) )
      | ~ sP2(X0) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> sP1(X0,X1) )
      | ~ sP2(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f64,plain,(
    ! [X0,X3,X1] :
      ( ~ sP1(X0,X1)
      | ~ r2_hidden(X3,X1)
      | sP0(X3,X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ( ( ~ sP0(sK10(X0,X1),X0)
            | ~ r2_hidden(sK10(X0,X1),X1) )
          & ( sP0(sK10(X0,X1),X0)
            | r2_hidden(sK10(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ sP0(X3,X0) )
            & ( sP0(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | ~ sP1(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f44,f45])).

fof(f45,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ sP0(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( sP0(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ sP0(sK10(X0,X1),X0)
          | ~ r2_hidden(sK10(X0,X1),X1) )
        & ( sP0(sK10(X0,X1),X0)
          | r2_hidden(sK10(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ? [X2] :
            ( ( ~ sP0(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( sP0(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ sP0(X3,X0) )
            & ( sP0(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | ~ sP1(X0,X1) ) ) ),
    inference(rectify,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ? [X2] :
            ( ( ~ sP0(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( sP0(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ sP0(X2,X0) )
            & ( sP0(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | ~ sP1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> sP0(X2,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f381,plain,
    ( spl13_33
    | ~ spl13_1
    | ~ spl13_2 ),
    inference(avatar_split_clause,[],[f376,f103,f98,f378])).

fof(f98,plain,
    ( spl13_1
  <=> r2_hidden(sK6,k2_relset_1(sK7,sK8,sK9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1])])).

fof(f376,plain,
    ( r2_hidden(sK6,k2_relat_1(sK9))
    | ~ spl13_1
    | ~ spl13_2 ),
    inference(subsumption_resolution,[],[f358,f105])).

fof(f358,plain,
    ( r2_hidden(sK6,k2_relat_1(sK9))
    | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
    | ~ spl13_1 ),
    inference(superposition,[],[f100,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f100,plain,
    ( r2_hidden(sK6,k2_relset_1(sK7,sK8,sK9))
    | ~ spl13_1 ),
    inference(avatar_component_clause,[],[f98])).

fof(f363,plain,
    ( spl13_30
    | ~ spl13_2 ),
    inference(avatar_split_clause,[],[f352,f103,f360])).

fof(f352,plain,
    ( k2_relset_1(sK7,sK8,sK9) = k2_relat_1(sK9)
    | ~ spl13_2 ),
    inference(unit_resulting_resolution,[],[f105,f77])).

fof(f351,plain,
    ( spl13_29
    | ~ spl13_2 ),
    inference(avatar_split_clause,[],[f346,f103,f348])).

fof(f346,plain,
    ( k1_relset_1(sK7,sK8,sK9) = k1_relat_1(sK9)
    | ~ spl13_2 ),
    inference(unit_resulting_resolution,[],[f105,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f296,plain,
    ( spl13_23
    | ~ spl13_2 ),
    inference(avatar_split_clause,[],[f289,f103,f292])).

fof(f289,plain,
    ( sP4(sK7,sK9,sK8)
    | ~ spl13_2 ),
    inference(resolution,[],[f85,f105])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP4(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( sP5(X2,X1,X0)
        & sP4(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f28,f38,f37,f36])).

fof(f38,plain,(
    ! [X2,X1,X0] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_xboole_0 = X2 )
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ sP5(X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).

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
    inference(flattening,[],[f27])).

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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

fof(f167,plain,
    ( spl13_11
    | ~ spl13_4
    | ~ spl13_10 ),
    inference(avatar_split_clause,[],[f162,f157,f113,f164])).

fof(f113,plain,
    ( spl13_4
  <=> v1_funct_1(sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_4])])).

fof(f157,plain,
    ( spl13_10
  <=> v1_relat_1(sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_10])])).

fof(f162,plain,
    ( sP2(sK9)
    | ~ spl13_4
    | ~ spl13_10 ),
    inference(unit_resulting_resolution,[],[f115,f159,f71])).

fof(f71,plain,(
    ! [X0] :
      ( sP2(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( sP2(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f18,f34,f33,f32])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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

fof(f159,plain,
    ( v1_relat_1(sK9)
    | ~ spl13_10 ),
    inference(avatar_component_clause,[],[f157])).

fof(f115,plain,
    ( v1_funct_1(sK9)
    | ~ spl13_4 ),
    inference(avatar_component_clause,[],[f113])).

fof(f161,plain,
    ( spl13_10
    | ~ spl13_2 ),
    inference(avatar_split_clause,[],[f154,f103,f157])).

fof(f154,plain,
    ( v1_relat_1(sK9)
    | ~ spl13_2 ),
    inference(resolution,[],[f75,f105])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f124,plain,
    ( ~ spl13_5
    | ~ spl13_1 ),
    inference(avatar_split_clause,[],[f118,f98,f120])).

fof(f120,plain,
    ( spl13_5
  <=> sP12(k2_relset_1(sK7,sK8,sK9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_5])])).

fof(f118,plain,
    ( ~ sP12(k2_relset_1(sK7,sK8,sK9))
    | ~ spl13_1 ),
    inference(resolution,[],[f96,f100])).

fof(f96,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ sP12(X1) ) ),
    inference(general_splitting,[],[f88,f95_D])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f116,plain,(
    spl13_4 ),
    inference(avatar_split_clause,[],[f56,f113])).

fof(f56,plain,(
    v1_funct_1(sK9) ),
    inference(cnf_transformation,[],[f41])).

fof(f111,plain,(
    spl13_3 ),
    inference(avatar_split_clause,[],[f57,f108])).

fof(f57,plain,(
    v1_funct_2(sK9,sK7,sK8) ),
    inference(cnf_transformation,[],[f41])).

fof(f106,plain,(
    spl13_2 ),
    inference(avatar_split_clause,[],[f58,f103])).

fof(f58,plain,(
    m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) ),
    inference(cnf_transformation,[],[f41])).

fof(f101,plain,(
    spl13_1 ),
    inference(avatar_split_clause,[],[f59,f98])).

fof(f59,plain,(
    r2_hidden(sK6,k2_relset_1(sK7,sK8,sK9)) ),
    inference(cnf_transformation,[],[f41])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:35:14 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.46  % (22574)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.47  % (22589)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.47  % (22575)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.48  % (22574)Refutation not found, incomplete strategy% (22574)------------------------------
% 0.21/0.48  % (22574)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (22574)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (22574)Memory used [KB]: 10618
% 0.21/0.48  % (22574)Time elapsed: 0.064 s
% 0.21/0.48  % (22574)------------------------------
% 0.21/0.48  % (22574)------------------------------
% 0.21/0.48  % (22573)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.48  % (22578)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.49  % (22587)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.49  % (22588)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.49  % (22586)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.49  % (22589)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f1092,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f101,f106,f111,f116,f124,f161,f167,f296,f351,f363,f381,f408,f425,f461,f466,f507,f509,f528,f529,f643,f651,f677,f849,f1026,f1091])).
% 0.21/0.50  fof(f1091,plain,(
% 0.21/0.50    ~spl13_39 | ~spl13_102),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f1090])).
% 0.21/0.50  fof(f1090,plain,(
% 0.21/0.50    $false | (~spl13_39 | ~spl13_102)),
% 0.21/0.50    inference(subsumption_resolution,[],[f1088,f460])).
% 0.21/0.50  fof(f460,plain,(
% 0.21/0.50    sK6 = k1_funct_1(sK9,sK11(sK6,sK9)) | ~spl13_39),
% 0.21/0.50    inference(avatar_component_clause,[],[f458])).
% 0.21/0.50  fof(f458,plain,(
% 0.21/0.50    spl13_39 <=> sK6 = k1_funct_1(sK9,sK11(sK6,sK9))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl13_39])])).
% 0.21/0.50  fof(f1088,plain,(
% 0.21/0.50    sK6 != k1_funct_1(sK9,sK11(sK6,sK9)) | ~spl13_102),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f1025,f60])).
% 0.21/0.50  fof(f60,plain,(
% 0.21/0.50    ( ! [X4] : (sK6 != k1_funct_1(sK9,X4) | ~m1_subset_1(X4,sK7)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f41])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    ! [X4] : (sK6 != k1_funct_1(sK9,X4) | ~m1_subset_1(X4,sK7)) & r2_hidden(sK6,k2_relset_1(sK7,sK8,sK9)) & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) & v1_funct_2(sK9,sK7,sK8) & v1_funct_1(sK9)),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9])],[f16,f40])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    ? [X0,X1,X2,X3] : (! [X4] : (k1_funct_1(X3,X4) != X0 | ~m1_subset_1(X4,X1)) & r2_hidden(X0,k2_relset_1(X1,X2,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (! [X4] : (sK6 != k1_funct_1(sK9,X4) | ~m1_subset_1(X4,sK7)) & r2_hidden(sK6,k2_relset_1(sK7,sK8,sK9)) & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) & v1_funct_2(sK9,sK7,sK8) & v1_funct_1(sK9))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ? [X0,X1,X2,X3] : (! [X4] : (k1_funct_1(X3,X4) != X0 | ~m1_subset_1(X4,X1)) & r2_hidden(X0,k2_relset_1(X1,X2,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))),
% 0.21/0.50    inference(flattening,[],[f15])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    ? [X0,X1,X2,X3] : ((! [X4] : (k1_funct_1(X3,X4) != X0 | ~m1_subset_1(X4,X1)) & r2_hidden(X0,k2_relset_1(X1,X2,X3))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)))),
% 0.21/0.50    inference(ennf_transformation,[],[f14])).
% 0.21/0.50  fof(f14,negated_conjecture,(
% 0.21/0.50    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ~(! [X4] : (m1_subset_1(X4,X1) => k1_funct_1(X3,X4) != X0) & r2_hidden(X0,k2_relset_1(X1,X2,X3))))),
% 0.21/0.50    inference(negated_conjecture,[],[f13])).
% 0.21/0.50  fof(f13,conjecture,(
% 0.21/0.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ~(! [X4] : (m1_subset_1(X4,X1) => k1_funct_1(X3,X4) != X0) & r2_hidden(X0,k2_relset_1(X1,X2,X3))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t190_funct_2)).
% 0.21/0.50  fof(f1025,plain,(
% 0.21/0.50    m1_subset_1(sK11(sK6,sK9),sK7) | ~spl13_102),
% 0.21/0.50    inference(avatar_component_clause,[],[f1023])).
% 0.21/0.50  fof(f1023,plain,(
% 0.21/0.50    spl13_102 <=> m1_subset_1(sK11(sK6,sK9),sK7)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl13_102])])).
% 0.21/0.50  fof(f1026,plain,(
% 0.21/0.50    spl13_102 | ~spl13_63),
% 0.21/0.50    inference(avatar_split_clause,[],[f1018,f674,f1023])).
% 0.21/0.50  fof(f674,plain,(
% 0.21/0.50    spl13_63 <=> r2_hidden(sK11(sK6,sK9),sK7)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl13_63])])).
% 0.21/0.50  fof(f1018,plain,(
% 0.21/0.50    m1_subset_1(sK11(sK6,sK9),sK7) | ~spl13_63),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f676,f72])).
% 0.21/0.50  fof(f72,plain,(
% 0.21/0.50    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 0.21/0.50  fof(f676,plain,(
% 0.21/0.50    r2_hidden(sK11(sK6,sK9),sK7) | ~spl13_63),
% 0.21/0.50    inference(avatar_component_clause,[],[f674])).
% 0.21/0.50  fof(f849,plain,(
% 0.21/0.50    ~spl13_48 | ~spl13_59),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f848])).
% 0.21/0.50  fof(f848,plain,(
% 0.21/0.50    $false | (~spl13_48 | ~spl13_59)),
% 0.21/0.50    inference(subsumption_resolution,[],[f719,f131])).
% 0.21/0.50  fof(f131,plain,(
% 0.21/0.50    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f61,f74])).
% 0.21/0.50  fof(f74,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.21/0.50  fof(f61,plain,(
% 0.21/0.50    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.50  fof(f719,plain,(
% 0.21/0.50    r2_hidden(sK6,k1_xboole_0) | (~spl13_48 | ~spl13_59)),
% 0.21/0.50    inference(backward_demodulation,[],[f525,f649])).
% 0.21/0.50  fof(f649,plain,(
% 0.21/0.50    k1_xboole_0 = sK8 | ~spl13_59),
% 0.21/0.50    inference(avatar_component_clause,[],[f647])).
% 0.21/0.50  fof(f647,plain,(
% 0.21/0.50    spl13_59 <=> k1_xboole_0 = sK8),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl13_59])])).
% 0.21/0.50  fof(f525,plain,(
% 0.21/0.50    r2_hidden(sK6,sK8) | ~spl13_48),
% 0.21/0.50    inference(avatar_component_clause,[],[f523])).
% 0.21/0.50  fof(f523,plain,(
% 0.21/0.50    spl13_48 <=> r2_hidden(sK6,sK8)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl13_48])])).
% 0.21/0.50  fof(f677,plain,(
% 0.21/0.50    spl13_63 | ~spl13_40 | ~spl13_58),
% 0.21/0.50    inference(avatar_split_clause,[],[f655,f637,f463,f674])).
% 0.21/0.50  fof(f463,plain,(
% 0.21/0.50    spl13_40 <=> r2_hidden(sK11(sK6,sK9),k1_relat_1(sK9))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl13_40])])).
% 0.21/0.50  fof(f637,plain,(
% 0.21/0.50    spl13_58 <=> sK7 = k1_relat_1(sK9)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl13_58])])).
% 0.21/0.50  fof(f655,plain,(
% 0.21/0.50    r2_hidden(sK11(sK6,sK9),sK7) | (~spl13_40 | ~spl13_58)),
% 0.21/0.50    inference(backward_demodulation,[],[f465,f639])).
% 0.21/0.50  fof(f639,plain,(
% 0.21/0.50    sK7 = k1_relat_1(sK9) | ~spl13_58),
% 0.21/0.50    inference(avatar_component_clause,[],[f637])).
% 0.21/0.50  fof(f465,plain,(
% 0.21/0.50    r2_hidden(sK11(sK6,sK9),k1_relat_1(sK9)) | ~spl13_40),
% 0.21/0.50    inference(avatar_component_clause,[],[f463])).
% 0.21/0.50  fof(f651,plain,(
% 0.21/0.50    spl13_59 | ~spl13_57),
% 0.21/0.50    inference(avatar_split_clause,[],[f645,f633,f647])).
% 0.21/0.50  fof(f633,plain,(
% 0.21/0.50    spl13_57 <=> sP3(sK7,sK8)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl13_57])])).
% 0.21/0.50  fof(f645,plain,(
% 0.21/0.50    k1_xboole_0 = sK8 | ~spl13_57),
% 0.21/0.50    inference(resolution,[],[f635,f83])).
% 0.21/0.50  fof(f83,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~sP3(X0,X1) | k1_xboole_0 = X1) )),
% 0.21/0.50    inference(cnf_transformation,[],[f55])).
% 0.21/0.50  fof(f55,plain,(
% 0.21/0.50    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP3(X0,X1))),
% 0.21/0.50    inference(nnf_transformation,[],[f36])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP3(X0,X1))),
% 0.21/0.50    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 0.21/0.50  fof(f635,plain,(
% 0.21/0.50    sP3(sK7,sK8) | ~spl13_57),
% 0.21/0.50    inference(avatar_component_clause,[],[f633])).
% 0.21/0.50  fof(f643,plain,(
% 0.21/0.50    spl13_57 | spl13_58 | ~spl13_3 | ~spl13_23 | ~spl13_29),
% 0.21/0.50    inference(avatar_split_clause,[],[f642,f348,f292,f108,f637,f633])).
% 0.21/0.50  fof(f108,plain,(
% 0.21/0.50    spl13_3 <=> v1_funct_2(sK9,sK7,sK8)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl13_3])])).
% 0.21/0.50  fof(f292,plain,(
% 0.21/0.50    spl13_23 <=> sP4(sK7,sK9,sK8)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl13_23])])).
% 0.21/0.50  fof(f348,plain,(
% 0.21/0.50    spl13_29 <=> k1_relset_1(sK7,sK8,sK9) = k1_relat_1(sK9)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl13_29])])).
% 0.21/0.50  fof(f642,plain,(
% 0.21/0.50    sK7 = k1_relat_1(sK9) | sP3(sK7,sK8) | (~spl13_3 | ~spl13_23 | ~spl13_29)),
% 0.21/0.50    inference(subsumption_resolution,[],[f641,f294])).
% 0.21/0.50  fof(f294,plain,(
% 0.21/0.50    sP4(sK7,sK9,sK8) | ~spl13_23),
% 0.21/0.50    inference(avatar_component_clause,[],[f292])).
% 0.21/0.50  fof(f641,plain,(
% 0.21/0.50    sK7 = k1_relat_1(sK9) | sP3(sK7,sK8) | ~sP4(sK7,sK9,sK8) | (~spl13_3 | ~spl13_29)),
% 0.21/0.50    inference(subsumption_resolution,[],[f628,f110])).
% 0.21/0.50  fof(f110,plain,(
% 0.21/0.50    v1_funct_2(sK9,sK7,sK8) | ~spl13_3),
% 0.21/0.50    inference(avatar_component_clause,[],[f108])).
% 0.21/0.50  fof(f628,plain,(
% 0.21/0.50    sK7 = k1_relat_1(sK9) | ~v1_funct_2(sK9,sK7,sK8) | sP3(sK7,sK8) | ~sP4(sK7,sK9,sK8) | ~spl13_29),
% 0.21/0.50    inference(superposition,[],[f350,f81])).
% 0.21/0.50  fof(f81,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2) | sP3(X0,X2) | ~sP4(X0,X1,X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f54])).
% 0.21/0.50  fof(f54,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | sP3(X0,X2) | ~sP4(X0,X1,X2))),
% 0.21/0.50    inference(rectify,[],[f53])).
% 0.21/0.50  fof(f53,plain,(
% 0.21/0.50    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | sP3(X0,X1) | ~sP4(X0,X2,X1))),
% 0.21/0.50    inference(nnf_transformation,[],[f37])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | sP3(X0,X1) | ~sP4(X0,X2,X1))),
% 0.21/0.50    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).
% 0.21/0.50  fof(f350,plain,(
% 0.21/0.50    k1_relset_1(sK7,sK8,sK9) = k1_relat_1(sK9) | ~spl13_29),
% 0.21/0.50    inference(avatar_component_clause,[],[f348])).
% 0.21/0.50  fof(f529,plain,(
% 0.21/0.50    k2_relset_1(sK7,sK8,sK9) != k2_relat_1(sK9) | ~sP12(k2_relat_1(sK9)) | sP12(k2_relset_1(sK7,sK8,sK9))),
% 0.21/0.50    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.50  fof(f528,plain,(
% 0.21/0.50    spl13_48 | spl13_44 | ~spl13_45),
% 0.21/0.50    inference(avatar_split_clause,[],[f527,f504,f499,f523])).
% 0.21/0.50  fof(f499,plain,(
% 0.21/0.50    spl13_44 <=> v1_xboole_0(sK8)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl13_44])])).
% 0.21/0.50  fof(f504,plain,(
% 0.21/0.50    spl13_45 <=> m1_subset_1(sK6,sK8)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl13_45])])).
% 0.21/0.50  fof(f527,plain,(
% 0.21/0.50    r2_hidden(sK6,sK8) | (spl13_44 | ~spl13_45)),
% 0.21/0.50    inference(subsumption_resolution,[],[f521,f501])).
% 0.21/0.50  fof(f501,plain,(
% 0.21/0.50    ~v1_xboole_0(sK8) | spl13_44),
% 0.21/0.50    inference(avatar_component_clause,[],[f499])).
% 0.21/0.50  fof(f521,plain,(
% 0.21/0.50    v1_xboole_0(sK8) | r2_hidden(sK6,sK8) | ~spl13_45),
% 0.21/0.50    inference(resolution,[],[f506,f73])).
% 0.21/0.50  fof(f73,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.21/0.50    inference(flattening,[],[f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.21/0.50  fof(f506,plain,(
% 0.21/0.50    m1_subset_1(sK6,sK8) | ~spl13_45),
% 0.21/0.50    inference(avatar_component_clause,[],[f504])).
% 0.21/0.50  fof(f509,plain,(
% 0.21/0.50    ~spl13_44 | spl13_19 | ~spl13_35),
% 0.21/0.50    inference(avatar_split_clause,[],[f508,f422,f232,f499])).
% 0.21/0.50  fof(f232,plain,(
% 0.21/0.50    spl13_19 <=> sP12(k2_relat_1(sK9))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl13_19])])).
% 0.21/0.50  fof(f422,plain,(
% 0.21/0.50    spl13_35 <=> m1_subset_1(k2_relat_1(sK9),k1_zfmisc_1(sK8))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl13_35])])).
% 0.21/0.50  fof(f508,plain,(
% 0.21/0.50    ~v1_xboole_0(sK8) | (spl13_19 | ~spl13_35)),
% 0.21/0.50    inference(subsumption_resolution,[],[f495,f234])).
% 0.21/0.50  fof(f234,plain,(
% 0.21/0.50    ~sP12(k2_relat_1(sK9)) | spl13_19),
% 0.21/0.50    inference(avatar_component_clause,[],[f232])).
% 0.21/0.50  fof(f495,plain,(
% 0.21/0.50    ~v1_xboole_0(sK8) | sP12(k2_relat_1(sK9)) | ~spl13_35),
% 0.21/0.50    inference(resolution,[],[f424,f95])).
% 0.21/0.50  fof(f95,plain,(
% 0.21/0.50    ( ! [X2,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2) | sP12(X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f95_D])).
% 0.21/0.50  fof(f95_D,plain,(
% 0.21/0.50    ( ! [X1] : (( ! [X2] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2)) ) <=> ~sP12(X1)) )),
% 0.21/0.50    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP12])])).
% 0.21/0.50  fof(f424,plain,(
% 0.21/0.50    m1_subset_1(k2_relat_1(sK9),k1_zfmisc_1(sK8)) | ~spl13_35),
% 0.21/0.50    inference(avatar_component_clause,[],[f422])).
% 0.21/0.50  fof(f507,plain,(
% 0.21/0.50    spl13_45 | ~spl13_33 | ~spl13_35),
% 0.21/0.50    inference(avatar_split_clause,[],[f492,f422,f378,f504])).
% 0.21/0.50  fof(f378,plain,(
% 0.21/0.50    spl13_33 <=> r2_hidden(sK6,k2_relat_1(sK9))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl13_33])])).
% 0.21/0.50  fof(f492,plain,(
% 0.21/0.50    m1_subset_1(sK6,sK8) | (~spl13_33 | ~spl13_35)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f380,f424,f87])).
% 0.21/0.50  fof(f87,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2) | ~r2_hidden(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f30])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.50    inference(flattening,[],[f29])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.21/0.50    inference(ennf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 0.21/0.50  fof(f380,plain,(
% 0.21/0.50    r2_hidden(sK6,k2_relat_1(sK9)) | ~spl13_33),
% 0.21/0.50    inference(avatar_component_clause,[],[f378])).
% 0.21/0.50  fof(f466,plain,(
% 0.21/0.50    spl13_40 | ~spl13_34),
% 0.21/0.50    inference(avatar_split_clause,[],[f432,f400,f463])).
% 0.21/0.50  fof(f400,plain,(
% 0.21/0.50    spl13_34 <=> sP0(sK6,sK9)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl13_34])])).
% 0.21/0.50  fof(f432,plain,(
% 0.21/0.50    r2_hidden(sK11(sK6,sK9),k1_relat_1(sK9)) | ~spl13_34),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f402,f68])).
% 0.21/0.50  fof(f68,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r2_hidden(sK11(X0,X1),k1_relat_1(X1)) | ~sP0(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f50])).
% 0.21/0.50  fof(f50,plain,(
% 0.21/0.50    ! [X0,X1] : ((sP0(X0,X1) | ! [X2] : (k1_funct_1(X1,X2) != X0 | ~r2_hidden(X2,k1_relat_1(X1)))) & ((k1_funct_1(X1,sK11(X0,X1)) = X0 & r2_hidden(sK11(X0,X1),k1_relat_1(X1))) | ~sP0(X0,X1)))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f48,f49])).
% 0.21/0.50  fof(f49,plain,(
% 0.21/0.50    ! [X1,X0] : (? [X3] : (k1_funct_1(X1,X3) = X0 & r2_hidden(X3,k1_relat_1(X1))) => (k1_funct_1(X1,sK11(X0,X1)) = X0 & r2_hidden(sK11(X0,X1),k1_relat_1(X1))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f48,plain,(
% 0.21/0.50    ! [X0,X1] : ((sP0(X0,X1) | ! [X2] : (k1_funct_1(X1,X2) != X0 | ~r2_hidden(X2,k1_relat_1(X1)))) & (? [X3] : (k1_funct_1(X1,X3) = X0 & r2_hidden(X3,k1_relat_1(X1))) | ~sP0(X0,X1)))),
% 0.21/0.50    inference(rectify,[],[f47])).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    ! [X2,X0] : ((sP0(X2,X0) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~sP0(X2,X0)))),
% 0.21/0.50    inference(nnf_transformation,[],[f32])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ! [X2,X0] : (sP0(X2,X0) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))),
% 0.21/0.50    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.50  fof(f402,plain,(
% 0.21/0.50    sP0(sK6,sK9) | ~spl13_34),
% 0.21/0.50    inference(avatar_component_clause,[],[f400])).
% 0.21/0.50  fof(f461,plain,(
% 0.21/0.50    spl13_39 | ~spl13_34),
% 0.21/0.50    inference(avatar_split_clause,[],[f433,f400,f458])).
% 0.21/0.50  fof(f433,plain,(
% 0.21/0.50    sK6 = k1_funct_1(sK9,sK11(sK6,sK9)) | ~spl13_34),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f402,f69])).
% 0.21/0.50  % (22577)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.50  fof(f69,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k1_funct_1(X1,sK11(X0,X1)) = X0 | ~sP0(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f50])).
% 0.21/0.50  fof(f425,plain,(
% 0.21/0.50    spl13_35 | ~spl13_2 | ~spl13_30),
% 0.21/0.50    inference(avatar_split_clause,[],[f420,f360,f103,f422])).
% 0.21/0.50  fof(f103,plain,(
% 0.21/0.50    spl13_2 <=> m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl13_2])])).
% 0.21/0.50  fof(f360,plain,(
% 0.21/0.50    spl13_30 <=> k2_relset_1(sK7,sK8,sK9) = k2_relat_1(sK9)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl13_30])])).
% 0.21/0.50  fof(f420,plain,(
% 0.21/0.50    m1_subset_1(k2_relat_1(sK9),k1_zfmisc_1(sK8)) | (~spl13_2 | ~spl13_30)),
% 0.21/0.50    inference(forward_demodulation,[],[f410,f362])).
% 0.21/0.50  fof(f362,plain,(
% 0.21/0.50    k2_relset_1(sK7,sK8,sK9) = k2_relat_1(sK9) | ~spl13_30),
% 0.21/0.50    inference(avatar_component_clause,[],[f360])).
% 0.21/0.50  fof(f410,plain,(
% 0.21/0.50    m1_subset_1(k2_relset_1(sK7,sK8,sK9),k1_zfmisc_1(sK8)) | ~spl13_2),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f105,f78])).
% 0.21/0.50  % (22582)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.50  % (22579)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.50  fof(f78,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f26])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).
% 0.21/0.50  fof(f105,plain,(
% 0.21/0.50    m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) | ~spl13_2),
% 0.21/0.50    inference(avatar_component_clause,[],[f103])).
% 0.21/0.50  fof(f408,plain,(
% 0.21/0.50    spl13_34 | ~spl13_11 | ~spl13_33),
% 0.21/0.50    inference(avatar_split_clause,[],[f407,f378,f164,f400])).
% 0.21/0.50  fof(f164,plain,(
% 0.21/0.50    spl13_11 <=> sP2(sK9)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl13_11])])).
% 0.21/0.50  fof(f407,plain,(
% 0.21/0.50    sP0(sK6,sK9) | (~spl13_11 | ~spl13_33)),
% 0.21/0.50    inference(subsumption_resolution,[],[f395,f166])).
% 0.21/0.50  fof(f166,plain,(
% 0.21/0.50    sP2(sK9) | ~spl13_11),
% 0.21/0.50    inference(avatar_component_clause,[],[f164])).
% 0.21/0.50  fof(f395,plain,(
% 0.21/0.50    sP0(sK6,sK9) | ~sP2(sK9) | ~spl13_33),
% 0.21/0.50    inference(resolution,[],[f380,f220])).
% 0.21/0.50  fof(f220,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r2_hidden(X0,k2_relat_1(X1)) | sP0(X0,X1) | ~sP2(X1)) )),
% 0.21/0.50    inference(resolution,[],[f64,f89])).
% 0.21/0.50  fof(f89,plain,(
% 0.21/0.50    ( ! [X0] : (sP1(X0,k2_relat_1(X0)) | ~sP2(X0)) )),
% 0.21/0.50    inference(equality_resolution,[],[f62])).
% 0.21/0.50  fof(f62,plain,(
% 0.21/0.50    ( ! [X0,X1] : (sP1(X0,X1) | k2_relat_1(X0) != X1 | ~sP2(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f42])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ~sP1(X0,X1)) & (sP1(X0,X1) | k2_relat_1(X0) != X1)) | ~sP2(X0))),
% 0.21/0.50    inference(nnf_transformation,[],[f34])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> sP1(X0,X1)) | ~sP2(X0))),
% 0.21/0.50    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.21/0.50  fof(f64,plain,(
% 0.21/0.50    ( ! [X0,X3,X1] : (~sP1(X0,X1) | ~r2_hidden(X3,X1) | sP0(X3,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f46])).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    ! [X0,X1] : ((sP1(X0,X1) | ((~sP0(sK10(X0,X1),X0) | ~r2_hidden(sK10(X0,X1),X1)) & (sP0(sK10(X0,X1),X0) | r2_hidden(sK10(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~sP0(X3,X0)) & (sP0(X3,X0) | ~r2_hidden(X3,X1))) | ~sP1(X0,X1)))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f44,f45])).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    ! [X1,X0] : (? [X2] : ((~sP0(X2,X0) | ~r2_hidden(X2,X1)) & (sP0(X2,X0) | r2_hidden(X2,X1))) => ((~sP0(sK10(X0,X1),X0) | ~r2_hidden(sK10(X0,X1),X1)) & (sP0(sK10(X0,X1),X0) | r2_hidden(sK10(X0,X1),X1))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    ! [X0,X1] : ((sP1(X0,X1) | ? [X2] : ((~sP0(X2,X0) | ~r2_hidden(X2,X1)) & (sP0(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~sP0(X3,X0)) & (sP0(X3,X0) | ~r2_hidden(X3,X1))) | ~sP1(X0,X1)))),
% 0.21/0.50    inference(rectify,[],[f43])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    ! [X0,X1] : ((sP1(X0,X1) | ? [X2] : ((~sP0(X2,X0) | ~r2_hidden(X2,X1)) & (sP0(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~sP0(X2,X0)) & (sP0(X2,X0) | ~r2_hidden(X2,X1))) | ~sP1(X0,X1)))),
% 0.21/0.50    inference(nnf_transformation,[],[f33])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    ! [X0,X1] : (sP1(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) <=> sP0(X2,X0)))),
% 0.21/0.50    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.50  fof(f381,plain,(
% 0.21/0.50    spl13_33 | ~spl13_1 | ~spl13_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f376,f103,f98,f378])).
% 0.21/0.50  fof(f98,plain,(
% 0.21/0.50    spl13_1 <=> r2_hidden(sK6,k2_relset_1(sK7,sK8,sK9))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl13_1])])).
% 0.21/0.50  fof(f376,plain,(
% 0.21/0.50    r2_hidden(sK6,k2_relat_1(sK9)) | (~spl13_1 | ~spl13_2)),
% 0.21/0.50    inference(subsumption_resolution,[],[f358,f105])).
% 0.21/0.50  fof(f358,plain,(
% 0.21/0.50    r2_hidden(sK6,k2_relat_1(sK9)) | ~m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) | ~spl13_1),
% 0.21/0.50    inference(superposition,[],[f100,f77])).
% 0.21/0.50  fof(f77,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f25])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f11])).
% 0.21/0.50  fof(f11,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.50  fof(f100,plain,(
% 0.21/0.50    r2_hidden(sK6,k2_relset_1(sK7,sK8,sK9)) | ~spl13_1),
% 0.21/0.50    inference(avatar_component_clause,[],[f98])).
% 0.21/0.50  fof(f363,plain,(
% 0.21/0.50    spl13_30 | ~spl13_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f352,f103,f360])).
% 0.21/0.50  fof(f352,plain,(
% 0.21/0.50    k2_relset_1(sK7,sK8,sK9) = k2_relat_1(sK9) | ~spl13_2),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f105,f77])).
% 0.21/0.50  fof(f351,plain,(
% 0.21/0.50    spl13_29 | ~spl13_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f346,f103,f348])).
% 0.21/0.50  fof(f346,plain,(
% 0.21/0.50    k1_relset_1(sK7,sK8,sK9) = k1_relat_1(sK9) | ~spl13_2),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f105,f76])).
% 0.21/0.50  fof(f76,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f24])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.50  fof(f296,plain,(
% 0.21/0.50    spl13_23 | ~spl13_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f289,f103,f292])).
% 0.21/0.50  fof(f289,plain,(
% 0.21/0.50    sP4(sK7,sK9,sK8) | ~spl13_2),
% 0.21/0.50    inference(resolution,[],[f85,f105])).
% 0.21/0.50  fof(f85,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP4(X0,X2,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f39])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((sP5(X2,X1,X0) & sP4(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(definition_folding,[],[f28,f38,f37,f36])).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    ! [X2,X1,X0] : ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~sP5(X2,X1,X0))),
% 0.21/0.50    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(flattening,[],[f27])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f12])).
% 0.21/0.50  fof(f12,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.50  fof(f167,plain,(
% 0.21/0.50    spl13_11 | ~spl13_4 | ~spl13_10),
% 0.21/0.50    inference(avatar_split_clause,[],[f162,f157,f113,f164])).
% 0.21/0.50  fof(f113,plain,(
% 0.21/0.50    spl13_4 <=> v1_funct_1(sK9)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl13_4])])).
% 0.21/0.50  fof(f157,plain,(
% 0.21/0.50    spl13_10 <=> v1_relat_1(sK9)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl13_10])])).
% 0.21/0.50  fof(f162,plain,(
% 0.21/0.50    sP2(sK9) | (~spl13_4 | ~spl13_10)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f115,f159,f71])).
% 0.21/0.50  fof(f71,plain,(
% 0.21/0.50    ( ! [X0] : (sP2(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f35])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    ! [X0] : (sP2(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(definition_folding,[],[f18,f34,f33,f32])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(flattening,[],[f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).
% 0.21/0.50  fof(f159,plain,(
% 0.21/0.50    v1_relat_1(sK9) | ~spl13_10),
% 0.21/0.50    inference(avatar_component_clause,[],[f157])).
% 0.21/0.50  fof(f115,plain,(
% 0.21/0.50    v1_funct_1(sK9) | ~spl13_4),
% 0.21/0.50    inference(avatar_component_clause,[],[f113])).
% 0.21/0.50  fof(f161,plain,(
% 0.21/0.50    spl13_10 | ~spl13_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f154,f103,f157])).
% 0.21/0.50  fof(f154,plain,(
% 0.21/0.50    v1_relat_1(sK9) | ~spl13_2),
% 0.21/0.50    inference(resolution,[],[f75,f105])).
% 0.21/0.50  fof(f75,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f23])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.50  fof(f124,plain,(
% 0.21/0.50    ~spl13_5 | ~spl13_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f118,f98,f120])).
% 0.21/0.50  fof(f120,plain,(
% 0.21/0.50    spl13_5 <=> sP12(k2_relset_1(sK7,sK8,sK9))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl13_5])])).
% 0.21/0.50  fof(f118,plain,(
% 0.21/0.50    ~sP12(k2_relset_1(sK7,sK8,sK9)) | ~spl13_1),
% 0.21/0.50    inference(resolution,[],[f96,f100])).
% 0.21/0.50  fof(f96,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~sP12(X1)) )),
% 0.21/0.50    inference(general_splitting,[],[f88,f95_D])).
% 0.21/0.50  fof(f88,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f31])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 0.21/0.50  fof(f116,plain,(
% 0.21/0.50    spl13_4),
% 0.21/0.50    inference(avatar_split_clause,[],[f56,f113])).
% 0.21/0.50  fof(f56,plain,(
% 0.21/0.50    v1_funct_1(sK9)),
% 0.21/0.50    inference(cnf_transformation,[],[f41])).
% 0.21/0.50  fof(f111,plain,(
% 0.21/0.50    spl13_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f57,f108])).
% 0.21/0.50  fof(f57,plain,(
% 0.21/0.50    v1_funct_2(sK9,sK7,sK8)),
% 0.21/0.50    inference(cnf_transformation,[],[f41])).
% 0.21/0.50  fof(f106,plain,(
% 0.21/0.50    spl13_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f58,f103])).
% 0.21/0.50  fof(f58,plain,(
% 0.21/0.50    m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))),
% 0.21/0.50    inference(cnf_transformation,[],[f41])).
% 0.21/0.50  fof(f101,plain,(
% 0.21/0.50    spl13_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f59,f98])).
% 0.21/0.50  fof(f59,plain,(
% 0.21/0.50    r2_hidden(sK6,k2_relset_1(sK7,sK8,sK9))),
% 0.21/0.50    inference(cnf_transformation,[],[f41])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (22589)------------------------------
% 0.21/0.50  % (22589)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (22589)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (22589)Memory used [KB]: 11257
% 0.21/0.50  % (22589)Time elapsed: 0.088 s
% 0.21/0.50  % (22589)------------------------------
% 0.21/0.50  % (22589)------------------------------
% 0.21/0.50  % (22572)Success in time 0.144 s
%------------------------------------------------------------------------------
