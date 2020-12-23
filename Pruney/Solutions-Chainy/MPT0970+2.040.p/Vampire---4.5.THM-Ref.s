%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:54 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  171 ( 338 expanded)
%              Number of leaves         :   35 ( 114 expanded)
%              Depth                    :   18
%              Number of atoms          :  630 (1538 expanded)
%              Number of equality atoms :  143 ( 430 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f796,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f442,f463,f465,f655,f750,f781,f793,f795])).

fof(f795,plain,
    ( spl19_18
    | ~ spl19_6 ),
    inference(avatar_split_clause,[],[f794,f395,f789])).

fof(f789,plain,
    ( spl19_18
  <=> k1_xboole_0 = sK11 ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_18])])).

fof(f395,plain,
    ( spl19_6
  <=> sP5(sK10,sK11) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_6])])).

fof(f794,plain,
    ( k1_xboole_0 = sK11
    | ~ spl19_6 ),
    inference(resolution,[],[f397,f127])).

fof(f127,plain,(
    ! [X0,X1] :
      ( ~ sP5(X0,X1)
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP5(X0,X1) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP5(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).

fof(f397,plain,
    ( sP5(sK10,sK11)
    | ~ spl19_6 ),
    inference(avatar_component_clause,[],[f395])).

fof(f793,plain,
    ( ~ spl19_18
    | ~ spl19_7 ),
    inference(avatar_split_clause,[],[f701,f412,f789])).

fof(f412,plain,
    ( spl19_7
  <=> k1_xboole_0 = sK12 ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_7])])).

fof(f701,plain,
    ( k1_xboole_0 != sK11
    | ~ spl19_7 ),
    inference(forward_demodulation,[],[f677,f88])).

fof(f88,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f677,plain,
    ( k2_relat_1(k1_xboole_0) != sK11
    | ~ spl19_7 ),
    inference(backward_demodulation,[],[f228,f414])).

fof(f414,plain,
    ( k1_xboole_0 = sK12
    | ~ spl19_7 ),
    inference(avatar_component_clause,[],[f412])).

fof(f228,plain,(
    sK11 != k2_relat_1(sK12) ),
    inference(subsumption_resolution,[],[f227,f83])).

fof(f83,plain,(
    m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,sK11))) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,
    ( sK11 != k2_relset_1(sK10,sK11,sK12)
    & ! [X3] :
        ( ( k1_funct_1(sK12,sK13(X3)) = X3
          & r2_hidden(sK13(X3),sK10) )
        | ~ r2_hidden(X3,sK11) )
    & m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,sK11)))
    & v1_funct_2(sK12,sK10,sK11)
    & v1_funct_1(sK12) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10,sK11,sK12,sK13])],[f18,f47,f46])).

fof(f46,plain,
    ( ? [X0,X1,X2] :
        ( k2_relset_1(X0,X1,X2) != X1
        & ! [X3] :
            ( ? [X4] :
                ( k1_funct_1(X2,X4) = X3
                & r2_hidden(X4,X0) )
            | ~ r2_hidden(X3,X1) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( sK11 != k2_relset_1(sK10,sK11,sK12)
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(sK12,X4) = X3
              & r2_hidden(X4,sK10) )
          | ~ r2_hidden(X3,sK11) )
      & m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,sK11)))
      & v1_funct_2(sK12,sK10,sK11)
      & v1_funct_1(sK12) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X3] :
      ( ? [X4] :
          ( k1_funct_1(sK12,X4) = X3
          & r2_hidden(X4,sK10) )
     => ( k1_funct_1(sK12,sK13(X3)) = X3
        & r2_hidden(sK13(X3),sK10) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
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
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_funct_2)).

fof(f227,plain,
    ( sK11 != k2_relat_1(sK12)
    | ~ m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,sK11))) ),
    inference(superposition,[],[f86,f120])).

fof(f120,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f86,plain,(
    sK11 != k2_relset_1(sK10,sK11,sK12) ),
    inference(cnf_transformation,[],[f48])).

fof(f781,plain,
    ( spl19_5
    | spl19_6 ),
    inference(avatar_split_clause,[],[f780,f395,f391])).

fof(f391,plain,
    ( spl19_5
  <=> sK10 = k1_relat_1(sK12) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_5])])).

fof(f780,plain,
    ( sP5(sK10,sK11)
    | sK10 = k1_relat_1(sK12) ),
    inference(subsumption_resolution,[],[f777,f82])).

fof(f82,plain,(
    v1_funct_2(sK12,sK10,sK11) ),
    inference(cnf_transformation,[],[f48])).

fof(f777,plain,
    ( ~ v1_funct_2(sK12,sK10,sK11)
    | sP5(sK10,sK11)
    | sK10 = k1_relat_1(sK12) ),
    inference(resolution,[],[f83,f330])).

fof(f330,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_2(X5,X3,X4)
      | sP5(X3,X4)
      | k1_relat_1(X5) = X3 ) ),
    inference(subsumption_resolution,[],[f328,f129])).

fof(f129,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP6(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( sP7(X2,X1,X0)
        & sP6(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f30,f41,f40,f39])).

fof(f40,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | sP5(X0,X1)
      | ~ sP6(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP6])])).

fof(f41,plain,(
    ! [X2,X1,X0] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_xboole_0 = X2 )
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ sP7(X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP7])])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

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

fof(f328,plain,(
    ! [X4,X5,X3] :
      ( k1_relat_1(X5) = X3
      | ~ v1_funct_2(X5,X3,X4)
      | sP5(X3,X4)
      | ~ sP6(X3,X5,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ) ),
    inference(superposition,[],[f125,f119])).

fof(f119,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f125,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X2,X1) = X0
      | ~ v1_funct_2(X1,X0,X2)
      | sP5(X0,X2)
      | ~ sP6(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | sP5(X0,X2)
      | ~ sP6(X0,X1,X2) ) ),
    inference(rectify,[],[f71])).

fof(f71,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | sP5(X0,X1)
      | ~ sP6(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f750,plain,
    ( ~ spl19_6
    | ~ spl19_8 ),
    inference(avatar_contradiction_clause,[],[f749])).

fof(f749,plain,
    ( $false
    | ~ spl19_6
    | ~ spl19_8 ),
    inference(subsumption_resolution,[],[f744,f146])).

fof(f146,plain,(
    ! [X1] : ~ sP5(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f128])).

fof(f128,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | ~ sP5(X0,X1) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f744,plain,
    ( sP5(k1_xboole_0,k1_xboole_0)
    | ~ spl19_6
    | ~ spl19_8 ),
    inference(backward_demodulation,[],[f455,f417])).

fof(f417,plain,
    ( k1_xboole_0 = sK10
    | ~ spl19_8 ),
    inference(avatar_component_clause,[],[f416])).

fof(f416,plain,
    ( spl19_8
  <=> k1_xboole_0 = sK10 ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_8])])).

fof(f455,plain,
    ( sP5(sK10,k1_xboole_0)
    | ~ spl19_6 ),
    inference(backward_demodulation,[],[f397,f443])).

fof(f443,plain,
    ( k1_xboole_0 = sK11
    | ~ spl19_6 ),
    inference(resolution,[],[f397,f127])).

fof(f655,plain,
    ( ~ spl19_5
    | ~ spl19_9 ),
    inference(avatar_contradiction_clause,[],[f654])).

fof(f654,plain,
    ( $false
    | ~ spl19_5
    | ~ spl19_9 ),
    inference(subsumption_resolution,[],[f653,f234])).

fof(f234,plain,(
    ~ sP8(sK12,sK11) ),
    inference(subsumption_resolution,[],[f232,f181])).

fof(f181,plain,(
    sP9(sK11,sK12,sK10) ),
    inference(resolution,[],[f136,f83])).

fof(f136,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP9(X1,X2,X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( sP9(X1,X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f31,f44,f43])).

fof(f43,plain,(
    ! [X2,X1] :
      ( sP8(X2,X1)
    <=> ! [X3] :
          ( ? [X4] : r2_hidden(k4_tarski(X4,X3),X2)
          | ~ r2_hidden(X3,X1) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP8])])).

fof(f44,plain,(
    ! [X1,X2,X0] :
      ( ( sP8(X2,X1)
      <=> k2_relset_1(X0,X1,X2) = X1 )
      | ~ sP9(X1,X2,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP9])])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ? [X4] : r2_hidden(k4_tarski(X4,X3),X2)
            | ~ r2_hidden(X3,X1) )
      <=> k2_relset_1(X0,X1,X2) = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ! [X3] :
            ~ ( ! [X4] : ~ r2_hidden(k4_tarski(X4,X3),X2)
              & r2_hidden(X3,X1) )
      <=> k2_relset_1(X0,X1,X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_relset_1)).

fof(f232,plain,
    ( ~ sP8(sK12,sK11)
    | ~ sP9(sK11,sK12,sK10) ),
    inference(trivial_inequality_removal,[],[f230])).

fof(f230,plain,
    ( sK11 != sK11
    | ~ sP8(sK12,sK11)
    | ~ sP9(sK11,sK12,sK10) ),
    inference(superposition,[],[f86,f131])).

fof(f131,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X2,X0,X1) = X0
      | ~ sP8(X1,X0)
      | ~ sP9(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f75,plain,(
    ! [X0,X1,X2] :
      ( ( ( sP8(X1,X0)
          | k2_relset_1(X2,X0,X1) != X0 )
        & ( k2_relset_1(X2,X0,X1) = X0
          | ~ sP8(X1,X0) ) )
      | ~ sP9(X0,X1,X2) ) ),
    inference(rectify,[],[f74])).

fof(f74,plain,(
    ! [X1,X2,X0] :
      ( ( ( sP8(X2,X1)
          | k2_relset_1(X0,X1,X2) != X1 )
        & ( k2_relset_1(X0,X1,X2) = X1
          | ~ sP8(X2,X1) ) )
      | ~ sP9(X1,X2,X0) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f653,plain,
    ( sP8(sK12,sK11)
    | ~ spl19_5
    | ~ spl19_9 ),
    inference(duplicate_literal_removal,[],[f652])).

fof(f652,plain,
    ( sP8(sK12,sK11)
    | sP8(sK12,sK11)
    | ~ spl19_5
    | ~ spl19_9 ),
    inference(resolution,[],[f649,f134])).

fof(f134,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK17(X0,X1),X1)
      | sP8(X0,X1) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ( sP8(X0,X1)
        | ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK17(X0,X1)),X0)
          & r2_hidden(sK17(X0,X1),X1) ) )
      & ( ! [X4] :
            ( r2_hidden(k4_tarski(sK18(X0,X4),X4),X0)
            | ~ r2_hidden(X4,X1) )
        | ~ sP8(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK17,sK18])],[f77,f79,f78])).

fof(f78,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
          & r2_hidden(X2,X1) )
     => ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK17(X0,X1)),X0)
        & r2_hidden(sK17(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f79,plain,(
    ! [X4,X0] :
      ( ? [X5] : r2_hidden(k4_tarski(X5,X4),X0)
     => r2_hidden(k4_tarski(sK18(X0,X4),X4),X0) ) ),
    introduced(choice_axiom,[])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ( sP8(X0,X1)
        | ? [X2] :
            ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            & r2_hidden(X2,X1) ) )
      & ( ! [X4] :
            ( ? [X5] : r2_hidden(k4_tarski(X5,X4),X0)
            | ~ r2_hidden(X4,X1) )
        | ~ sP8(X0,X1) ) ) ),
    inference(rectify,[],[f76])).

fof(f76,plain,(
    ! [X2,X1] :
      ( ( sP8(X2,X1)
        | ? [X3] :
            ( ! [X4] : ~ r2_hidden(k4_tarski(X4,X3),X2)
            & r2_hidden(X3,X1) ) )
      & ( ! [X3] :
            ( ? [X4] : r2_hidden(k4_tarski(X4,X3),X2)
            | ~ r2_hidden(X3,X1) )
        | ~ sP8(X2,X1) ) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f649,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK17(sK12,X0),sK11)
        | sP8(sK12,X0) )
    | ~ spl19_5
    | ~ spl19_9 ),
    inference(duplicate_literal_removal,[],[f643])).

fof(f643,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK17(sK12,X0),sK11)
        | sP8(sK12,X0)
        | ~ r2_hidden(sK17(sK12,X0),sK11) )
    | ~ spl19_5
    | ~ spl19_9 ),
    inference(resolution,[],[f515,f84])).

fof(f84,plain,(
    ! [X3] :
      ( r2_hidden(sK13(X3),sK10)
      | ~ r2_hidden(X3,sK11) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f515,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK13(sK17(sK12,X0)),X1)
        | ~ r2_hidden(sK17(sK12,X0),sK11)
        | sP8(sK12,X0) )
    | ~ spl19_5
    | ~ spl19_9 ),
    inference(subsumption_resolution,[],[f514,f150])).

fof(f150,plain,(
    v1_relat_1(sK12) ),
    inference(subsumption_resolution,[],[f149,f103])).

fof(f103,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f149,plain,
    ( v1_relat_1(sK12)
    | ~ v1_relat_1(k2_zfmisc_1(sK10,sK11)) ),
    inference(resolution,[],[f91,f83])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f514,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK13(sK17(sK12,X0)),X1)
        | ~ r2_hidden(sK17(sK12,X0),sK11)
        | ~ v1_relat_1(sK12)
        | sP8(sK12,X0) )
    | ~ spl19_5
    | ~ spl19_9 ),
    inference(subsumption_resolution,[],[f511,f423])).

fof(f423,plain,
    ( sP2(sK12)
    | ~ spl19_9 ),
    inference(avatar_component_clause,[],[f422])).

fof(f422,plain,
    ( spl19_9
  <=> sP2(sK12) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_9])])).

fof(f511,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK13(sK17(sK12,X0)),X1)
        | ~ r2_hidden(sK17(sK12,X0),sK11)
        | ~ sP2(sK12)
        | ~ v1_relat_1(sK12)
        | sP8(sK12,X0) )
    | ~ spl19_5 ),
    inference(resolution,[],[f497,f293])).

fof(f293,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(sK17(X0,X1),X0,X2)
      | ~ sP2(X0)
      | ~ v1_relat_1(X0)
      | sP8(X0,X1) ) ),
    inference(resolution,[],[f292,f214])).

fof(f214,plain,(
    ! [X2,X0,X1] :
      ( ~ sP3(X0,X1,sK17(X1,X2))
      | sP8(X1,X2) ) ),
    inference(resolution,[],[f115,f135])).

fof(f135,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,sK17(X0,X1)),X0)
      | sP8(X0,X1) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK16(X0,X1,X2),X2),X1)
      | ~ sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0,X1,X2] :
      ( ( sP3(X0,X1,X2)
        | ! [X3] :
            ( ~ r2_hidden(X3,X0)
            | ~ r2_hidden(k4_tarski(X3,X2),X1)
            | ~ r2_hidden(X3,k1_relat_1(X1)) ) )
      & ( ( r2_hidden(sK16(X0,X1,X2),X0)
          & r2_hidden(k4_tarski(sK16(X0,X1,X2),X2),X1)
          & r2_hidden(sK16(X0,X1,X2),k1_relat_1(X1)) )
        | ~ sP3(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK16])],[f66,f67])).

fof(f67,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X0)
          & r2_hidden(k4_tarski(X4,X2),X1)
          & r2_hidden(X4,k1_relat_1(X1)) )
     => ( r2_hidden(sK16(X0,X1,X2),X0)
        & r2_hidden(k4_tarski(sK16(X0,X1,X2),X2),X1)
        & r2_hidden(sK16(X0,X1,X2),k1_relat_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,(
    ! [X0,X1,X2] :
      ( ( sP3(X0,X1,X2)
        | ! [X3] :
            ( ~ r2_hidden(X3,X0)
            | ~ r2_hidden(k4_tarski(X3,X2),X1)
            | ~ r2_hidden(X3,k1_relat_1(X1)) ) )
      & ( ? [X4] :
            ( r2_hidden(X4,X0)
            & r2_hidden(k4_tarski(X4,X2),X1)
            & r2_hidden(X4,k1_relat_1(X1)) )
        | ~ sP3(X0,X1,X2) ) ) ),
    inference(rectify,[],[f65])).

fof(f65,plain,(
    ! [X1,X2,X0] :
      ( ( sP3(X1,X2,X0)
        | ! [X3] :
            ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(k4_tarski(X3,X0),X2)
            | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) )
        | ~ sP3(X1,X2,X0) ) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X1,X2,X0] :
      ( sP3(X1,X2,X0)
    <=> ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(k4_tarski(X3,X0),X2)
          & r2_hidden(X3,k1_relat_1(X2)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f292,plain,(
    ! [X2,X0,X1] :
      ( sP3(X0,X1,X2)
      | ~ sP0(X2,X1,X0)
      | ~ sP2(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f216,f118])).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( sP4(X0,X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( sP4(X0,X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(definition_folding,[],[f25,f37,f36])).

fof(f37,plain,(
    ! [X0,X2,X1] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> sP3(X1,X2,X0) )
      | ~ sP4(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f25,plain,(
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

fof(f216,plain,(
    ! [X2,X0,X1] :
      ( ~ sP4(X2,X1,X0)
      | sP3(X0,X1,X2)
      | ~ sP0(X2,X1,X0)
      | ~ sP2(X1) ) ),
    inference(resolution,[],[f112,f189])).

fof(f189,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k9_relat_1(X1,X2))
      | ~ sP0(X0,X1,X2)
      | ~ sP2(X1) ) ),
    inference(resolution,[],[f95,f137])).

fof(f137,plain,(
    ! [X0,X1] :
      ( sP1(X1,X0,k9_relat_1(X0,X1))
      | ~ sP2(X0) ) ),
    inference(equality_resolution,[],[f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( sP1(X1,X0,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ sP2(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ~ sP1(X1,X0,X2) )
          & ( sP1(X1,X0,X2)
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ sP2(X0) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> sP1(X1,X0,X2) )
      | ~ sP2(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f95,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ sP0(X4,X1,X0)
      | r2_hidden(X4,X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ( ( ~ sP0(sK14(X0,X1,X2),X1,X0)
            | ~ r2_hidden(sK14(X0,X1,X2),X2) )
          & ( sP0(sK14(X0,X1,X2),X1,X0)
            | r2_hidden(sK14(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP0(X4,X1,X0) )
            & ( sP0(X4,X1,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK14])],[f51,f52])).

fof(f52,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ sP0(X3,X1,X0)
            | ~ r2_hidden(X3,X2) )
          & ( sP0(X3,X1,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ~ sP0(sK14(X0,X1,X2),X1,X0)
          | ~ r2_hidden(sK14(X0,X1,X2),X2) )
        & ( sP0(sK14(X0,X1,X2),X1,X0)
          | r2_hidden(sK14(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP0(X3,X1,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP0(X3,X1,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP0(X4,X1,X0) )
            & ( sP0(X4,X1,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f50])).

fof(f50,plain,(
    ! [X1,X0,X2] :
      ( ( sP1(X1,X0,X2)
        | ? [X3] :
            ( ( ~ sP0(X3,X0,X1)
              | ~ r2_hidden(X3,X2) )
            & ( sP0(X3,X0,X1)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ sP0(X3,X0,X1) )
            & ( sP0(X3,X0,X1)
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP1(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X1,X0,X2] :
      ( sP1(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> sP0(X3,X0,X1) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
      | sP3(X2,X1,X0)
      | ~ sP4(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X1,X2))
          | ~ sP3(X2,X1,X0) )
        & ( sP3(X2,X1,X0)
          | ~ r2_hidden(X0,k9_relat_1(X1,X2)) ) )
      | ~ sP4(X0,X1,X2) ) ),
    inference(rectify,[],[f63])).

fof(f63,plain,(
    ! [X0,X2,X1] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ~ sP3(X1,X2,X0) )
        & ( sP3(X1,X2,X0)
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ sP4(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f497,plain,
    ( ! [X0,X1] :
        ( sP0(X0,sK12,X1)
        | ~ r2_hidden(sK13(X0),X1)
        | ~ r2_hidden(X0,sK11) )
    | ~ spl19_5 ),
    inference(subsumption_resolution,[],[f496,f84])).

fof(f496,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK13(X0),sK10)
        | sP0(X0,sK12,X1)
        | ~ r2_hidden(sK13(X0),X1)
        | ~ r2_hidden(X0,sK11) )
    | ~ spl19_5 ),
    inference(forward_demodulation,[],[f495,f393])).

fof(f393,plain,
    ( sK10 = k1_relat_1(sK12)
    | ~ spl19_5 ),
    inference(avatar_component_clause,[],[f391])).

fof(f495,plain,(
    ! [X0,X1] :
      ( sP0(X0,sK12,X1)
      | ~ r2_hidden(sK13(X0),X1)
      | ~ r2_hidden(sK13(X0),k1_relat_1(sK12))
      | ~ r2_hidden(X0,sK11) ) ),
    inference(superposition,[],[f138,f85])).

fof(f85,plain,(
    ! [X3] :
      ( k1_funct_1(sK12,sK13(X3)) = X3
      | ~ r2_hidden(X3,sK11) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f138,plain,(
    ! [X2,X3,X1] :
      ( sP0(k1_funct_1(X1,X3),X1,X2)
      | ~ r2_hidden(X3,X2)
      | ~ r2_hidden(X3,k1_relat_1(X1)) ) ),
    inference(equality_resolution,[],[f101])).

fof(f101,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X1,X2)
      | k1_funct_1(X1,X3) != X0
      | ~ r2_hidden(X3,X2)
      | ~ r2_hidden(X3,k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ! [X3] :
            ( k1_funct_1(X1,X3) != X0
            | ~ r2_hidden(X3,X2)
            | ~ r2_hidden(X3,k1_relat_1(X1)) ) )
      & ( ( k1_funct_1(X1,sK15(X0,X1,X2)) = X0
          & r2_hidden(sK15(X0,X1,X2),X2)
          & r2_hidden(sK15(X0,X1,X2),k1_relat_1(X1)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15])],[f55,f56])).

fof(f56,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X1,X4) = X0
          & r2_hidden(X4,X2)
          & r2_hidden(X4,k1_relat_1(X1)) )
     => ( k1_funct_1(X1,sK15(X0,X1,X2)) = X0
        & r2_hidden(sK15(X0,X1,X2),X2)
        & r2_hidden(sK15(X0,X1,X2),k1_relat_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ! [X3] :
            ( k1_funct_1(X1,X3) != X0
            | ~ r2_hidden(X3,X2)
            | ~ r2_hidden(X3,k1_relat_1(X1)) ) )
      & ( ? [X4] :
            ( k1_funct_1(X1,X4) = X0
            & r2_hidden(X4,X2)
            & r2_hidden(X4,k1_relat_1(X1)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f54])).

fof(f54,plain,(
    ! [X3,X0,X1] :
      ( ( sP0(X3,X0,X1)
        | ! [X4] :
            ( k1_funct_1(X0,X4) != X3
            | ~ r2_hidden(X4,X1)
            | ~ r2_hidden(X4,k1_relat_1(X0)) ) )
      & ( ? [X4] :
            ( k1_funct_1(X0,X4) = X3
            & r2_hidden(X4,X1)
            & r2_hidden(X4,k1_relat_1(X0)) )
        | ~ sP0(X3,X0,X1) ) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X3,X0,X1] :
      ( sP0(X3,X0,X1)
    <=> ? [X4] :
          ( k1_funct_1(X0,X4) = X3
          & r2_hidden(X4,X1)
          & r2_hidden(X4,k1_relat_1(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f465,plain,
    ( spl19_13
    | ~ spl19_6 ),
    inference(avatar_split_clause,[],[f456,f395,f460])).

fof(f460,plain,
    ( spl19_13
  <=> m1_subset_1(sK12,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_13])])).

fof(f456,plain,
    ( m1_subset_1(sK12,k1_zfmisc_1(k1_xboole_0))
    | ~ spl19_6 ),
    inference(forward_demodulation,[],[f445,f141])).

fof(f141,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f111])).

fof(f111,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f445,plain,
    ( m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,k1_xboole_0)))
    | ~ spl19_6 ),
    inference(backward_demodulation,[],[f83,f443])).

fof(f463,plain,
    ( ~ spl19_13
    | spl19_7
    | ~ spl19_6
    | spl19_8 ),
    inference(avatar_split_clause,[],[f458,f416,f395,f412,f460])).

fof(f458,plain,
    ( k1_xboole_0 = sK12
    | ~ m1_subset_1(sK12,k1_zfmisc_1(k1_xboole_0))
    | ~ spl19_6
    | spl19_8 ),
    inference(subsumption_resolution,[],[f457,f418])).

fof(f418,plain,
    ( k1_xboole_0 != sK10
    | spl19_8 ),
    inference(avatar_component_clause,[],[f416])).

fof(f457,plain,
    ( k1_xboole_0 = sK10
    | k1_xboole_0 = sK12
    | ~ m1_subset_1(sK12,k1_zfmisc_1(k1_xboole_0))
    | ~ spl19_6 ),
    inference(resolution,[],[f444,f262])).

fof(f262,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(resolution,[],[f145,f179])).

fof(f179,plain,(
    ! [X0,X1] :
      ( sP7(X1,k1_xboole_0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[],[f130,f141])).

fof(f130,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP7(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f145,plain,(
    ! [X2,X0] :
      ( ~ sP7(X0,k1_xboole_0,X2)
      | ~ v1_funct_2(X0,X2,k1_xboole_0)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f123])).

fof(f123,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | ~ v1_funct_2(X0,X2,X1)
      | k1_xboole_0 = X2
      | k1_xboole_0 != X1
      | ~ sP7(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X0,X2,X1)
          | k1_xboole_0 != X0 )
        & ( k1_xboole_0 = X0
          | ~ v1_funct_2(X0,X2,X1) ) )
      | k1_xboole_0 = X2
      | k1_xboole_0 != X1
      | ~ sP7(X0,X1,X2) ) ),
    inference(rectify,[],[f69])).

fof(f69,plain,(
    ! [X2,X1,X0] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_xboole_0 != X2 )
        & ( k1_xboole_0 = X2
          | ~ v1_funct_2(X2,X0,X1) ) )
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ sP7(X2,X1,X0) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f444,plain,
    ( v1_funct_2(sK12,sK10,k1_xboole_0)
    | ~ spl19_6 ),
    inference(backward_demodulation,[],[f82,f443])).

fof(f442,plain,(
    spl19_9 ),
    inference(avatar_contradiction_clause,[],[f441])).

fof(f441,plain,
    ( $false
    | spl19_9 ),
    inference(subsumption_resolution,[],[f440,f150])).

fof(f440,plain,
    ( ~ v1_relat_1(sK12)
    | spl19_9 ),
    inference(subsumption_resolution,[],[f439,f81])).

fof(f81,plain,(
    v1_funct_1(sK12) ),
    inference(cnf_transformation,[],[f48])).

fof(f439,plain,
    ( ~ v1_funct_1(sK12)
    | ~ v1_relat_1(sK12)
    | spl19_9 ),
    inference(resolution,[],[f424,f102])).

fof(f102,plain,(
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
    inference(definition_folding,[],[f23,f34,f33,f32])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_funct_1)).

fof(f424,plain,
    ( ~ sP2(sK12)
    | spl19_9 ),
    inference(avatar_component_clause,[],[f422])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:00:26 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.47  % (16690)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.48  % (16686)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.48  % (16706)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.20/0.49  % (16683)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.49  % (16685)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.49  % (16693)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.50  % (16698)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.20/0.50  % (16701)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.50  % (16684)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.50  % (16700)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.50  % (16687)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.50  % (16699)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.20/0.50  % (16692)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.51  % (16691)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.51  % (16704)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.51  % (16702)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.51  % (16697)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.51  % (16688)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.51  % (16695)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.52  % (16703)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.52  % (16689)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.52  % (16705)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.20/0.52  % (16686)Refutation found. Thanks to Tanya!
% 0.20/0.52  % SZS status Theorem for theBenchmark
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f796,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(avatar_sat_refutation,[],[f442,f463,f465,f655,f750,f781,f793,f795])).
% 0.20/0.52  fof(f795,plain,(
% 0.20/0.52    spl19_18 | ~spl19_6),
% 0.20/0.52    inference(avatar_split_clause,[],[f794,f395,f789])).
% 0.20/0.52  fof(f789,plain,(
% 0.20/0.52    spl19_18 <=> k1_xboole_0 = sK11),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl19_18])])).
% 0.20/0.52  fof(f395,plain,(
% 0.20/0.52    spl19_6 <=> sP5(sK10,sK11)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl19_6])])).
% 0.20/0.52  fof(f794,plain,(
% 0.20/0.52    k1_xboole_0 = sK11 | ~spl19_6),
% 0.20/0.52    inference(resolution,[],[f397,f127])).
% 0.20/0.52  fof(f127,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~sP5(X0,X1) | k1_xboole_0 = X1) )),
% 0.20/0.52    inference(cnf_transformation,[],[f73])).
% 0.20/0.52  fof(f73,plain,(
% 0.20/0.52    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP5(X0,X1))),
% 0.20/0.52    inference(nnf_transformation,[],[f39])).
% 0.20/0.52  fof(f39,plain,(
% 0.20/0.52    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP5(X0,X1))),
% 0.20/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).
% 0.20/0.52  fof(f397,plain,(
% 0.20/0.52    sP5(sK10,sK11) | ~spl19_6),
% 0.20/0.52    inference(avatar_component_clause,[],[f395])).
% 0.20/0.52  fof(f793,plain,(
% 0.20/0.52    ~spl19_18 | ~spl19_7),
% 0.20/0.52    inference(avatar_split_clause,[],[f701,f412,f789])).
% 0.20/0.52  fof(f412,plain,(
% 0.20/0.52    spl19_7 <=> k1_xboole_0 = sK12),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl19_7])])).
% 0.20/0.52  fof(f701,plain,(
% 0.20/0.52    k1_xboole_0 != sK11 | ~spl19_7),
% 0.20/0.52    inference(forward_demodulation,[],[f677,f88])).
% 0.20/0.52  fof(f88,plain,(
% 0.20/0.52    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.20/0.52    inference(cnf_transformation,[],[f7])).
% 0.20/0.52  fof(f7,axiom,(
% 0.20/0.52    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.20/0.52  fof(f677,plain,(
% 0.20/0.52    k2_relat_1(k1_xboole_0) != sK11 | ~spl19_7),
% 0.20/0.52    inference(backward_demodulation,[],[f228,f414])).
% 0.20/0.52  fof(f414,plain,(
% 0.20/0.52    k1_xboole_0 = sK12 | ~spl19_7),
% 0.20/0.52    inference(avatar_component_clause,[],[f412])).
% 0.20/0.52  fof(f228,plain,(
% 0.20/0.52    sK11 != k2_relat_1(sK12)),
% 0.20/0.52    inference(subsumption_resolution,[],[f227,f83])).
% 0.20/0.52  fof(f83,plain,(
% 0.20/0.52    m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,sK11)))),
% 0.20/0.52    inference(cnf_transformation,[],[f48])).
% 0.20/0.52  fof(f48,plain,(
% 0.20/0.52    sK11 != k2_relset_1(sK10,sK11,sK12) & ! [X3] : ((k1_funct_1(sK12,sK13(X3)) = X3 & r2_hidden(sK13(X3),sK10)) | ~r2_hidden(X3,sK11)) & m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,sK11))) & v1_funct_2(sK12,sK10,sK11) & v1_funct_1(sK12)),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10,sK11,sK12,sK13])],[f18,f47,f46])).
% 0.20/0.52  fof(f46,plain,(
% 0.20/0.52    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (sK11 != k2_relset_1(sK10,sK11,sK12) & ! [X3] : (? [X4] : (k1_funct_1(sK12,X4) = X3 & r2_hidden(X4,sK10)) | ~r2_hidden(X3,sK11)) & m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,sK11))) & v1_funct_2(sK12,sK10,sK11) & v1_funct_1(sK12))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f47,plain,(
% 0.20/0.52    ! [X3] : (? [X4] : (k1_funct_1(sK12,X4) = X3 & r2_hidden(X4,sK10)) => (k1_funct_1(sK12,sK13(X3)) = X3 & r2_hidden(sK13(X3),sK10)))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f18,plain,(
% 0.20/0.52    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.20/0.52    inference(flattening,[],[f17])).
% 0.20/0.52  fof(f17,plain,(
% 0.20/0.52    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.20/0.52    inference(ennf_transformation,[],[f16])).
% 0.20/0.52  fof(f16,negated_conjecture,(
% 0.20/0.52    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 0.20/0.52    inference(negated_conjecture,[],[f15])).
% 0.20/0.52  fof(f15,conjecture,(
% 0.20/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_funct_2)).
% 0.20/0.52  fof(f227,plain,(
% 0.20/0.52    sK11 != k2_relat_1(sK12) | ~m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,sK11)))),
% 0.20/0.52    inference(superposition,[],[f86,f120])).
% 0.20/0.52  fof(f120,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f27])).
% 0.20/0.52  fof(f27,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.52    inference(ennf_transformation,[],[f12])).
% 0.20/0.52  fof(f12,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.20/0.52  fof(f86,plain,(
% 0.20/0.52    sK11 != k2_relset_1(sK10,sK11,sK12)),
% 0.20/0.52    inference(cnf_transformation,[],[f48])).
% 0.20/0.52  fof(f781,plain,(
% 0.20/0.52    spl19_5 | spl19_6),
% 0.20/0.52    inference(avatar_split_clause,[],[f780,f395,f391])).
% 0.20/0.52  fof(f391,plain,(
% 0.20/0.52    spl19_5 <=> sK10 = k1_relat_1(sK12)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl19_5])])).
% 0.20/0.52  fof(f780,plain,(
% 0.20/0.52    sP5(sK10,sK11) | sK10 = k1_relat_1(sK12)),
% 0.20/0.52    inference(subsumption_resolution,[],[f777,f82])).
% 0.20/0.52  fof(f82,plain,(
% 0.20/0.52    v1_funct_2(sK12,sK10,sK11)),
% 0.20/0.52    inference(cnf_transformation,[],[f48])).
% 0.20/0.52  fof(f777,plain,(
% 0.20/0.52    ~v1_funct_2(sK12,sK10,sK11) | sP5(sK10,sK11) | sK10 = k1_relat_1(sK12)),
% 0.20/0.52    inference(resolution,[],[f83,f330])).
% 0.20/0.52  fof(f330,plain,(
% 0.20/0.52    ( ! [X4,X5,X3] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_2(X5,X3,X4) | sP5(X3,X4) | k1_relat_1(X5) = X3) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f328,f129])).
% 0.20/0.52  fof(f129,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP6(X0,X2,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f42])).
% 0.20/0.52  fof(f42,plain,(
% 0.20/0.52    ! [X0,X1,X2] : ((sP7(X2,X1,X0) & sP6(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.52    inference(definition_folding,[],[f30,f41,f40,f39])).
% 0.20/0.52  fof(f40,plain,(
% 0.20/0.52    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | sP5(X0,X1) | ~sP6(X0,X2,X1))),
% 0.20/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP6])])).
% 0.20/0.52  fof(f41,plain,(
% 0.20/0.52    ! [X2,X1,X0] : ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~sP7(X2,X1,X0))),
% 0.20/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP7])])).
% 0.20/0.52  fof(f30,plain,(
% 0.20/0.52    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.52    inference(flattening,[],[f29])).
% 0.20/0.52  fof(f29,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.52    inference(ennf_transformation,[],[f14])).
% 0.20/0.52  fof(f14,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.20/0.52  fof(f328,plain,(
% 0.20/0.52    ( ! [X4,X5,X3] : (k1_relat_1(X5) = X3 | ~v1_funct_2(X5,X3,X4) | sP5(X3,X4) | ~sP6(X3,X5,X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) )),
% 0.20/0.52    inference(superposition,[],[f125,f119])).
% 0.20/0.52  fof(f119,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f26])).
% 0.20/0.52  fof(f26,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.52    inference(ennf_transformation,[],[f11])).
% 0.20/0.52  fof(f11,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.52  fof(f125,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2) | sP5(X0,X2) | ~sP6(X0,X1,X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f72])).
% 0.20/0.52  fof(f72,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | sP5(X0,X2) | ~sP6(X0,X1,X2))),
% 0.20/0.52    inference(rectify,[],[f71])).
% 0.20/0.52  fof(f71,plain,(
% 0.20/0.52    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | sP5(X0,X1) | ~sP6(X0,X2,X1))),
% 0.20/0.52    inference(nnf_transformation,[],[f40])).
% 0.20/0.52  fof(f750,plain,(
% 0.20/0.52    ~spl19_6 | ~spl19_8),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f749])).
% 0.20/0.52  fof(f749,plain,(
% 0.20/0.52    $false | (~spl19_6 | ~spl19_8)),
% 0.20/0.52    inference(subsumption_resolution,[],[f744,f146])).
% 0.20/0.52  fof(f146,plain,(
% 0.20/0.52    ( ! [X1] : (~sP5(k1_xboole_0,X1)) )),
% 0.20/0.52    inference(equality_resolution,[],[f128])).
% 0.20/0.52  fof(f128,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k1_xboole_0 != X0 | ~sP5(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f73])).
% 0.20/0.52  fof(f744,plain,(
% 0.20/0.52    sP5(k1_xboole_0,k1_xboole_0) | (~spl19_6 | ~spl19_8)),
% 0.20/0.52    inference(backward_demodulation,[],[f455,f417])).
% 0.20/0.52  fof(f417,plain,(
% 0.20/0.52    k1_xboole_0 = sK10 | ~spl19_8),
% 0.20/0.52    inference(avatar_component_clause,[],[f416])).
% 0.20/0.52  fof(f416,plain,(
% 0.20/0.52    spl19_8 <=> k1_xboole_0 = sK10),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl19_8])])).
% 0.20/0.52  fof(f455,plain,(
% 0.20/0.52    sP5(sK10,k1_xboole_0) | ~spl19_6),
% 0.20/0.52    inference(backward_demodulation,[],[f397,f443])).
% 0.20/0.52  fof(f443,plain,(
% 0.20/0.52    k1_xboole_0 = sK11 | ~spl19_6),
% 0.20/0.52    inference(resolution,[],[f397,f127])).
% 0.20/0.52  fof(f655,plain,(
% 0.20/0.52    ~spl19_5 | ~spl19_9),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f654])).
% 0.20/0.52  fof(f654,plain,(
% 0.20/0.52    $false | (~spl19_5 | ~spl19_9)),
% 0.20/0.52    inference(subsumption_resolution,[],[f653,f234])).
% 0.20/0.52  fof(f234,plain,(
% 0.20/0.52    ~sP8(sK12,sK11)),
% 0.20/0.52    inference(subsumption_resolution,[],[f232,f181])).
% 0.20/0.52  fof(f181,plain,(
% 0.20/0.52    sP9(sK11,sK12,sK10)),
% 0.20/0.52    inference(resolution,[],[f136,f83])).
% 0.20/0.52  fof(f136,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP9(X1,X2,X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f45])).
% 0.20/0.52  fof(f45,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (sP9(X1,X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.52    inference(definition_folding,[],[f31,f44,f43])).
% 0.20/0.52  fof(f43,plain,(
% 0.20/0.52    ! [X2,X1] : (sP8(X2,X1) <=> ! [X3] : (? [X4] : r2_hidden(k4_tarski(X4,X3),X2) | ~r2_hidden(X3,X1)))),
% 0.20/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP8])])).
% 0.20/0.52  fof(f44,plain,(
% 0.20/0.52    ! [X1,X2,X0] : ((sP8(X2,X1) <=> k2_relset_1(X0,X1,X2) = X1) | ~sP9(X1,X2,X0))),
% 0.20/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP9])])).
% 0.20/0.52  fof(f31,plain,(
% 0.20/0.52    ! [X0,X1,X2] : ((! [X3] : (? [X4] : r2_hidden(k4_tarski(X4,X3),X2) | ~r2_hidden(X3,X1)) <=> k2_relset_1(X0,X1,X2) = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.52    inference(ennf_transformation,[],[f13])).
% 0.20/0.52  fof(f13,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (! [X3] : ~(! [X4] : ~r2_hidden(k4_tarski(X4,X3),X2) & r2_hidden(X3,X1)) <=> k2_relset_1(X0,X1,X2) = X1))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_relset_1)).
% 0.20/0.52  fof(f232,plain,(
% 0.20/0.52    ~sP8(sK12,sK11) | ~sP9(sK11,sK12,sK10)),
% 0.20/0.52    inference(trivial_inequality_removal,[],[f230])).
% 0.20/0.52  fof(f230,plain,(
% 0.20/0.52    sK11 != sK11 | ~sP8(sK12,sK11) | ~sP9(sK11,sK12,sK10)),
% 0.20/0.52    inference(superposition,[],[f86,f131])).
% 0.20/0.52  fof(f131,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (k2_relset_1(X2,X0,X1) = X0 | ~sP8(X1,X0) | ~sP9(X0,X1,X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f75])).
% 0.20/0.52  fof(f75,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (((sP8(X1,X0) | k2_relset_1(X2,X0,X1) != X0) & (k2_relset_1(X2,X0,X1) = X0 | ~sP8(X1,X0))) | ~sP9(X0,X1,X2))),
% 0.20/0.53    inference(rectify,[],[f74])).
% 0.20/0.53  fof(f74,plain,(
% 0.20/0.53    ! [X1,X2,X0] : (((sP8(X2,X1) | k2_relset_1(X0,X1,X2) != X1) & (k2_relset_1(X0,X1,X2) = X1 | ~sP8(X2,X1))) | ~sP9(X1,X2,X0))),
% 0.20/0.53    inference(nnf_transformation,[],[f44])).
% 0.20/0.53  fof(f653,plain,(
% 0.20/0.53    sP8(sK12,sK11) | (~spl19_5 | ~spl19_9)),
% 0.20/0.53    inference(duplicate_literal_removal,[],[f652])).
% 0.20/0.53  fof(f652,plain,(
% 0.20/0.53    sP8(sK12,sK11) | sP8(sK12,sK11) | (~spl19_5 | ~spl19_9)),
% 0.20/0.53    inference(resolution,[],[f649,f134])).
% 0.20/0.53  fof(f134,plain,(
% 0.20/0.53    ( ! [X0,X1] : (r2_hidden(sK17(X0,X1),X1) | sP8(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f80])).
% 0.20/0.53  fof(f80,plain,(
% 0.20/0.53    ! [X0,X1] : ((sP8(X0,X1) | (! [X3] : ~r2_hidden(k4_tarski(X3,sK17(X0,X1)),X0) & r2_hidden(sK17(X0,X1),X1))) & (! [X4] : (r2_hidden(k4_tarski(sK18(X0,X4),X4),X0) | ~r2_hidden(X4,X1)) | ~sP8(X0,X1)))),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK17,sK18])],[f77,f79,f78])).
% 0.20/0.53  fof(f78,plain,(
% 0.20/0.53    ! [X1,X0] : (? [X2] : (! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) & r2_hidden(X2,X1)) => (! [X3] : ~r2_hidden(k4_tarski(X3,sK17(X0,X1)),X0) & r2_hidden(sK17(X0,X1),X1)))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f79,plain,(
% 0.20/0.53    ! [X4,X0] : (? [X5] : r2_hidden(k4_tarski(X5,X4),X0) => r2_hidden(k4_tarski(sK18(X0,X4),X4),X0))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f77,plain,(
% 0.20/0.53    ! [X0,X1] : ((sP8(X0,X1) | ? [X2] : (! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) & r2_hidden(X2,X1))) & (! [X4] : (? [X5] : r2_hidden(k4_tarski(X5,X4),X0) | ~r2_hidden(X4,X1)) | ~sP8(X0,X1)))),
% 0.20/0.53    inference(rectify,[],[f76])).
% 0.20/0.53  fof(f76,plain,(
% 0.20/0.53    ! [X2,X1] : ((sP8(X2,X1) | ? [X3] : (! [X4] : ~r2_hidden(k4_tarski(X4,X3),X2) & r2_hidden(X3,X1))) & (! [X3] : (? [X4] : r2_hidden(k4_tarski(X4,X3),X2) | ~r2_hidden(X3,X1)) | ~sP8(X2,X1)))),
% 0.20/0.53    inference(nnf_transformation,[],[f43])).
% 0.20/0.53  fof(f649,plain,(
% 0.20/0.53    ( ! [X0] : (~r2_hidden(sK17(sK12,X0),sK11) | sP8(sK12,X0)) ) | (~spl19_5 | ~spl19_9)),
% 0.20/0.53    inference(duplicate_literal_removal,[],[f643])).
% 0.20/0.53  fof(f643,plain,(
% 0.20/0.53    ( ! [X0] : (~r2_hidden(sK17(sK12,X0),sK11) | sP8(sK12,X0) | ~r2_hidden(sK17(sK12,X0),sK11)) ) | (~spl19_5 | ~spl19_9)),
% 0.20/0.53    inference(resolution,[],[f515,f84])).
% 0.20/0.53  fof(f84,plain,(
% 0.20/0.53    ( ! [X3] : (r2_hidden(sK13(X3),sK10) | ~r2_hidden(X3,sK11)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f48])).
% 0.20/0.53  fof(f515,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~r2_hidden(sK13(sK17(sK12,X0)),X1) | ~r2_hidden(sK17(sK12,X0),sK11) | sP8(sK12,X0)) ) | (~spl19_5 | ~spl19_9)),
% 0.20/0.53    inference(subsumption_resolution,[],[f514,f150])).
% 0.20/0.53  fof(f150,plain,(
% 0.20/0.53    v1_relat_1(sK12)),
% 0.20/0.53    inference(subsumption_resolution,[],[f149,f103])).
% 0.20/0.53  fof(f103,plain,(
% 0.20/0.53    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f5])).
% 0.20/0.53  fof(f5,axiom,(
% 0.20/0.53    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.20/0.53  fof(f149,plain,(
% 0.20/0.53    v1_relat_1(sK12) | ~v1_relat_1(k2_zfmisc_1(sK10,sK11))),
% 0.20/0.53    inference(resolution,[],[f91,f83])).
% 0.20/0.53  fof(f91,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f21])).
% 0.20/0.53  fof(f21,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f3])).
% 0.20/0.53  fof(f3,axiom,(
% 0.20/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.20/0.53  fof(f514,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~r2_hidden(sK13(sK17(sK12,X0)),X1) | ~r2_hidden(sK17(sK12,X0),sK11) | ~v1_relat_1(sK12) | sP8(sK12,X0)) ) | (~spl19_5 | ~spl19_9)),
% 0.20/0.53    inference(subsumption_resolution,[],[f511,f423])).
% 0.20/0.53  fof(f423,plain,(
% 0.20/0.53    sP2(sK12) | ~spl19_9),
% 0.20/0.53    inference(avatar_component_clause,[],[f422])).
% 0.20/0.53  fof(f422,plain,(
% 0.20/0.53    spl19_9 <=> sP2(sK12)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl19_9])])).
% 0.20/0.53  fof(f511,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~r2_hidden(sK13(sK17(sK12,X0)),X1) | ~r2_hidden(sK17(sK12,X0),sK11) | ~sP2(sK12) | ~v1_relat_1(sK12) | sP8(sK12,X0)) ) | ~spl19_5),
% 0.20/0.53    inference(resolution,[],[f497,f293])).
% 0.20/0.53  fof(f293,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~sP0(sK17(X0,X1),X0,X2) | ~sP2(X0) | ~v1_relat_1(X0) | sP8(X0,X1)) )),
% 0.20/0.53    inference(resolution,[],[f292,f214])).
% 0.20/0.53  fof(f214,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~sP3(X0,X1,sK17(X1,X2)) | sP8(X1,X2)) )),
% 0.20/0.53    inference(resolution,[],[f115,f135])).
% 0.20/0.53  fof(f135,plain,(
% 0.20/0.53    ( ! [X0,X3,X1] : (~r2_hidden(k4_tarski(X3,sK17(X0,X1)),X0) | sP8(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f80])).
% 0.20/0.53  fof(f115,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK16(X0,X1,X2),X2),X1) | ~sP3(X0,X1,X2)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f68])).
% 0.20/0.53  fof(f68,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((sP3(X0,X1,X2) | ! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(k4_tarski(X3,X2),X1) | ~r2_hidden(X3,k1_relat_1(X1)))) & ((r2_hidden(sK16(X0,X1,X2),X0) & r2_hidden(k4_tarski(sK16(X0,X1,X2),X2),X1) & r2_hidden(sK16(X0,X1,X2),k1_relat_1(X1))) | ~sP3(X0,X1,X2)))),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK16])],[f66,f67])).
% 0.20/0.53  fof(f67,plain,(
% 0.20/0.53    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X0) & r2_hidden(k4_tarski(X4,X2),X1) & r2_hidden(X4,k1_relat_1(X1))) => (r2_hidden(sK16(X0,X1,X2),X0) & r2_hidden(k4_tarski(sK16(X0,X1,X2),X2),X1) & r2_hidden(sK16(X0,X1,X2),k1_relat_1(X1))))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f66,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((sP3(X0,X1,X2) | ! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(k4_tarski(X3,X2),X1) | ~r2_hidden(X3,k1_relat_1(X1)))) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(k4_tarski(X4,X2),X1) & r2_hidden(X4,k1_relat_1(X1))) | ~sP3(X0,X1,X2)))),
% 0.20/0.53    inference(rectify,[],[f65])).
% 0.20/0.53  fof(f65,plain,(
% 0.20/0.53    ! [X1,X2,X0] : ((sP3(X1,X2,X0) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~sP3(X1,X2,X0)))),
% 0.20/0.53    inference(nnf_transformation,[],[f36])).
% 0.20/0.53  fof(f36,plain,(
% 0.20/0.53    ! [X1,X2,X0] : (sP3(X1,X2,X0) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))))),
% 0.20/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 0.20/0.53  fof(f292,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (sP3(X0,X1,X2) | ~sP0(X2,X1,X0) | ~sP2(X1) | ~v1_relat_1(X1)) )),
% 0.20/0.53    inference(resolution,[],[f216,f118])).
% 0.20/0.53  fof(f118,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (sP4(X0,X2,X1) | ~v1_relat_1(X2)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f38])).
% 0.20/0.53  fof(f38,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (sP4(X0,X2,X1) | ~v1_relat_1(X2))),
% 0.20/0.53    inference(definition_folding,[],[f25,f37,f36])).
% 0.20/0.53  fof(f37,plain,(
% 0.20/0.53    ! [X0,X2,X1] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> sP3(X1,X2,X0)) | ~sP4(X0,X2,X1))),
% 0.20/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).
% 0.20/0.53  fof(f25,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.20/0.53    inference(ennf_transformation,[],[f6])).
% 0.20/0.53  fof(f6,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).
% 0.20/0.53  fof(f216,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~sP4(X2,X1,X0) | sP3(X0,X1,X2) | ~sP0(X2,X1,X0) | ~sP2(X1)) )),
% 0.20/0.53    inference(resolution,[],[f112,f189])).
% 0.20/0.53  fof(f189,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (r2_hidden(X0,k9_relat_1(X1,X2)) | ~sP0(X0,X1,X2) | ~sP2(X1)) )),
% 0.20/0.53    inference(resolution,[],[f95,f137])).
% 0.20/0.53  fof(f137,plain,(
% 0.20/0.53    ( ! [X0,X1] : (sP1(X1,X0,k9_relat_1(X0,X1)) | ~sP2(X0)) )),
% 0.20/0.53    inference(equality_resolution,[],[f92])).
% 0.20/0.53  fof(f92,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (sP1(X1,X0,X2) | k9_relat_1(X0,X1) != X2 | ~sP2(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f49])).
% 0.20/0.53  fof(f49,plain,(
% 0.20/0.53    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ~sP1(X1,X0,X2)) & (sP1(X1,X0,X2) | k9_relat_1(X0,X1) != X2)) | ~sP2(X0))),
% 0.20/0.53    inference(nnf_transformation,[],[f34])).
% 0.20/0.53  fof(f34,plain,(
% 0.20/0.53    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> sP1(X1,X0,X2)) | ~sP2(X0))),
% 0.20/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.20/0.53  fof(f95,plain,(
% 0.20/0.53    ( ! [X4,X2,X0,X1] : (~sP1(X0,X1,X2) | ~sP0(X4,X1,X0) | r2_hidden(X4,X2)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f53])).
% 0.20/0.53  fof(f53,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ((~sP0(sK14(X0,X1,X2),X1,X0) | ~r2_hidden(sK14(X0,X1,X2),X2)) & (sP0(sK14(X0,X1,X2),X1,X0) | r2_hidden(sK14(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP0(X4,X1,X0)) & (sP0(X4,X1,X0) | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK14])],[f51,f52])).
% 0.20/0.53  fof(f52,plain,(
% 0.20/0.53    ! [X2,X1,X0] : (? [X3] : ((~sP0(X3,X1,X0) | ~r2_hidden(X3,X2)) & (sP0(X3,X1,X0) | r2_hidden(X3,X2))) => ((~sP0(sK14(X0,X1,X2),X1,X0) | ~r2_hidden(sK14(X0,X1,X2),X2)) & (sP0(sK14(X0,X1,X2),X1,X0) | r2_hidden(sK14(X0,X1,X2),X2))))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f51,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : ((~sP0(X3,X1,X0) | ~r2_hidden(X3,X2)) & (sP0(X3,X1,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP0(X4,X1,X0)) & (sP0(X4,X1,X0) | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 0.20/0.53    inference(rectify,[],[f50])).
% 0.20/0.53  fof(f50,plain,(
% 0.20/0.53    ! [X1,X0,X2] : ((sP1(X1,X0,X2) | ? [X3] : ((~sP0(X3,X0,X1) | ~r2_hidden(X3,X2)) & (sP0(X3,X0,X1) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~sP0(X3,X0,X1)) & (sP0(X3,X0,X1) | ~r2_hidden(X3,X2))) | ~sP1(X1,X0,X2)))),
% 0.20/0.53    inference(nnf_transformation,[],[f33])).
% 0.20/0.53  fof(f33,plain,(
% 0.20/0.53    ! [X1,X0,X2] : (sP1(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> sP0(X3,X0,X1)))),
% 0.20/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.20/0.53  fof(f112,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X0,k9_relat_1(X1,X2)) | sP3(X2,X1,X0) | ~sP4(X0,X1,X2)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f64])).
% 0.20/0.53  fof(f64,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X1,X2)) | ~sP3(X2,X1,X0)) & (sP3(X2,X1,X0) | ~r2_hidden(X0,k9_relat_1(X1,X2)))) | ~sP4(X0,X1,X2))),
% 0.20/0.53    inference(rectify,[],[f63])).
% 0.20/0.53  fof(f63,plain,(
% 0.20/0.53    ! [X0,X2,X1] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ~sP3(X1,X2,X0)) & (sP3(X1,X2,X0) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~sP4(X0,X2,X1))),
% 0.20/0.53    inference(nnf_transformation,[],[f37])).
% 0.20/0.53  fof(f497,plain,(
% 0.20/0.53    ( ! [X0,X1] : (sP0(X0,sK12,X1) | ~r2_hidden(sK13(X0),X1) | ~r2_hidden(X0,sK11)) ) | ~spl19_5),
% 0.20/0.53    inference(subsumption_resolution,[],[f496,f84])).
% 0.20/0.53  fof(f496,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~r2_hidden(sK13(X0),sK10) | sP0(X0,sK12,X1) | ~r2_hidden(sK13(X0),X1) | ~r2_hidden(X0,sK11)) ) | ~spl19_5),
% 0.20/0.53    inference(forward_demodulation,[],[f495,f393])).
% 0.20/0.53  fof(f393,plain,(
% 0.20/0.53    sK10 = k1_relat_1(sK12) | ~spl19_5),
% 0.20/0.53    inference(avatar_component_clause,[],[f391])).
% 0.20/0.53  fof(f495,plain,(
% 0.20/0.53    ( ! [X0,X1] : (sP0(X0,sK12,X1) | ~r2_hidden(sK13(X0),X1) | ~r2_hidden(sK13(X0),k1_relat_1(sK12)) | ~r2_hidden(X0,sK11)) )),
% 0.20/0.53    inference(superposition,[],[f138,f85])).
% 0.20/0.53  fof(f85,plain,(
% 0.20/0.53    ( ! [X3] : (k1_funct_1(sK12,sK13(X3)) = X3 | ~r2_hidden(X3,sK11)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f48])).
% 0.20/0.53  fof(f138,plain,(
% 0.20/0.53    ( ! [X2,X3,X1] : (sP0(k1_funct_1(X1,X3),X1,X2) | ~r2_hidden(X3,X2) | ~r2_hidden(X3,k1_relat_1(X1))) )),
% 0.20/0.53    inference(equality_resolution,[],[f101])).
% 0.20/0.53  fof(f101,plain,(
% 0.20/0.53    ( ! [X2,X0,X3,X1] : (sP0(X0,X1,X2) | k1_funct_1(X1,X3) != X0 | ~r2_hidden(X3,X2) | ~r2_hidden(X3,k1_relat_1(X1))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f57])).
% 0.20/0.53  fof(f57,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ! [X3] : (k1_funct_1(X1,X3) != X0 | ~r2_hidden(X3,X2) | ~r2_hidden(X3,k1_relat_1(X1)))) & ((k1_funct_1(X1,sK15(X0,X1,X2)) = X0 & r2_hidden(sK15(X0,X1,X2),X2) & r2_hidden(sK15(X0,X1,X2),k1_relat_1(X1))) | ~sP0(X0,X1,X2)))),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15])],[f55,f56])).
% 0.20/0.53  fof(f56,plain,(
% 0.20/0.53    ! [X2,X1,X0] : (? [X4] : (k1_funct_1(X1,X4) = X0 & r2_hidden(X4,X2) & r2_hidden(X4,k1_relat_1(X1))) => (k1_funct_1(X1,sK15(X0,X1,X2)) = X0 & r2_hidden(sK15(X0,X1,X2),X2) & r2_hidden(sK15(X0,X1,X2),k1_relat_1(X1))))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f55,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ! [X3] : (k1_funct_1(X1,X3) != X0 | ~r2_hidden(X3,X2) | ~r2_hidden(X3,k1_relat_1(X1)))) & (? [X4] : (k1_funct_1(X1,X4) = X0 & r2_hidden(X4,X2) & r2_hidden(X4,k1_relat_1(X1))) | ~sP0(X0,X1,X2)))),
% 0.20/0.53    inference(rectify,[],[f54])).
% 0.20/0.53  fof(f54,plain,(
% 0.20/0.53    ! [X3,X0,X1] : ((sP0(X3,X0,X1) | ! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0)))) & (? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))) | ~sP0(X3,X0,X1)))),
% 0.20/0.53    inference(nnf_transformation,[],[f32])).
% 0.20/0.53  fof(f32,plain,(
% 0.20/0.53    ! [X3,X0,X1] : (sP0(X3,X0,X1) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))),
% 0.20/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.20/0.53  fof(f465,plain,(
% 0.20/0.53    spl19_13 | ~spl19_6),
% 0.20/0.53    inference(avatar_split_clause,[],[f456,f395,f460])).
% 0.20/0.53  fof(f460,plain,(
% 0.20/0.53    spl19_13 <=> m1_subset_1(sK12,k1_zfmisc_1(k1_xboole_0))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl19_13])])).
% 0.20/0.53  fof(f456,plain,(
% 0.20/0.53    m1_subset_1(sK12,k1_zfmisc_1(k1_xboole_0)) | ~spl19_6),
% 0.20/0.53    inference(forward_demodulation,[],[f445,f141])).
% 0.20/0.53  fof(f141,plain,(
% 0.20/0.53    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.20/0.53    inference(equality_resolution,[],[f111])).
% 0.20/0.53  fof(f111,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 0.20/0.53    inference(cnf_transformation,[],[f62])).
% 0.20/0.53  fof(f62,plain,(
% 0.20/0.53    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.20/0.53    inference(flattening,[],[f61])).
% 0.20/0.53  fof(f61,plain,(
% 0.20/0.53    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.20/0.53    inference(nnf_transformation,[],[f2])).
% 0.20/0.53  fof(f2,axiom,(
% 0.20/0.53    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.20/0.53  fof(f445,plain,(
% 0.20/0.53    m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,k1_xboole_0))) | ~spl19_6),
% 0.20/0.53    inference(backward_demodulation,[],[f83,f443])).
% 0.20/0.53  fof(f463,plain,(
% 0.20/0.53    ~spl19_13 | spl19_7 | ~spl19_6 | spl19_8),
% 0.20/0.53    inference(avatar_split_clause,[],[f458,f416,f395,f412,f460])).
% 0.20/0.53  fof(f458,plain,(
% 0.20/0.53    k1_xboole_0 = sK12 | ~m1_subset_1(sK12,k1_zfmisc_1(k1_xboole_0)) | (~spl19_6 | spl19_8)),
% 0.20/0.53    inference(subsumption_resolution,[],[f457,f418])).
% 0.20/0.53  fof(f418,plain,(
% 0.20/0.53    k1_xboole_0 != sK10 | spl19_8),
% 0.20/0.53    inference(avatar_component_clause,[],[f416])).
% 0.20/0.53  fof(f457,plain,(
% 0.20/0.53    k1_xboole_0 = sK10 | k1_xboole_0 = sK12 | ~m1_subset_1(sK12,k1_zfmisc_1(k1_xboole_0)) | ~spl19_6),
% 0.20/0.53    inference(resolution,[],[f444,f262])).
% 0.20/0.53  fof(f262,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~v1_funct_2(X0,X1,k1_xboole_0) | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))) )),
% 0.20/0.53    inference(resolution,[],[f145,f179])).
% 0.20/0.53  fof(f179,plain,(
% 0.20/0.53    ( ! [X0,X1] : (sP7(X1,k1_xboole_0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))) )),
% 0.20/0.53    inference(superposition,[],[f130,f141])).
% 0.20/0.53  fof(f130,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP7(X2,X1,X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f42])).
% 0.20/0.53  fof(f145,plain,(
% 0.20/0.53    ( ! [X2,X0] : (~sP7(X0,k1_xboole_0,X2) | ~v1_funct_2(X0,X2,k1_xboole_0) | k1_xboole_0 = X2 | k1_xboole_0 = X0) )),
% 0.20/0.53    inference(equality_resolution,[],[f123])).
% 0.20/0.53  fof(f123,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (k1_xboole_0 = X0 | ~v1_funct_2(X0,X2,X1) | k1_xboole_0 = X2 | k1_xboole_0 != X1 | ~sP7(X0,X1,X2)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f70])).
% 0.20/0.53  fof(f70,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (((v1_funct_2(X0,X2,X1) | k1_xboole_0 != X0) & (k1_xboole_0 = X0 | ~v1_funct_2(X0,X2,X1))) | k1_xboole_0 = X2 | k1_xboole_0 != X1 | ~sP7(X0,X1,X2))),
% 0.20/0.53    inference(rectify,[],[f69])).
% 0.20/0.53  fof(f69,plain,(
% 0.20/0.53    ! [X2,X1,X0] : (((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~sP7(X2,X1,X0))),
% 0.20/0.53    inference(nnf_transformation,[],[f41])).
% 0.20/0.53  fof(f444,plain,(
% 0.20/0.53    v1_funct_2(sK12,sK10,k1_xboole_0) | ~spl19_6),
% 0.20/0.53    inference(backward_demodulation,[],[f82,f443])).
% 0.20/0.53  fof(f442,plain,(
% 0.20/0.53    spl19_9),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f441])).
% 0.20/0.53  fof(f441,plain,(
% 0.20/0.53    $false | spl19_9),
% 0.20/0.53    inference(subsumption_resolution,[],[f440,f150])).
% 0.20/0.53  fof(f440,plain,(
% 0.20/0.53    ~v1_relat_1(sK12) | spl19_9),
% 0.20/0.53    inference(subsumption_resolution,[],[f439,f81])).
% 0.20/0.53  fof(f81,plain,(
% 0.20/0.53    v1_funct_1(sK12)),
% 0.20/0.53    inference(cnf_transformation,[],[f48])).
% 0.20/0.53  fof(f439,plain,(
% 0.20/0.53    ~v1_funct_1(sK12) | ~v1_relat_1(sK12) | spl19_9),
% 0.20/0.53    inference(resolution,[],[f424,f102])).
% 0.20/0.53  fof(f102,plain,(
% 0.20/0.53    ( ! [X0] : (sP2(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f35])).
% 0.20/0.53  fof(f35,plain,(
% 0.20/0.53    ! [X0] : (sP2(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.53    inference(definition_folding,[],[f23,f34,f33,f32])).
% 0.20/0.53  fof(f23,plain,(
% 0.20/0.53    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.53    inference(flattening,[],[f22])).
% 0.20/0.53  fof(f22,plain,(
% 0.20/0.53    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f9])).
% 0.20/0.53  fof(f9,axiom,(
% 0.20/0.53    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_funct_1)).
% 0.20/0.53  fof(f424,plain,(
% 0.20/0.53    ~sP2(sK12) | spl19_9),
% 0.20/0.53    inference(avatar_component_clause,[],[f422])).
% 0.20/0.53  % SZS output end Proof for theBenchmark
% 0.20/0.53  % (16686)------------------------------
% 0.20/0.53  % (16686)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (16686)Termination reason: Refutation
% 0.20/0.53  
% 0.20/0.53  % (16686)Memory used [KB]: 6524
% 0.20/0.53  % (16686)Time elapsed: 0.119 s
% 0.20/0.53  % (16686)------------------------------
% 0.20/0.53  % (16686)------------------------------
% 1.39/0.53  % (16696)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.39/0.53  % (16681)Success in time 0.177 s
%------------------------------------------------------------------------------
