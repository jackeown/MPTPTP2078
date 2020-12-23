%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:22 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 1.65s
% Verified   : 
% Statistics : Number of formulae       :  163 ( 280 expanded)
%              Number of leaves         :   43 ( 123 expanded)
%              Depth                    :    9
%              Number of atoms          :  454 ( 841 expanded)
%              Number of equality atoms :   79 ( 162 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1071,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f81,f86,f91,f96,f122,f130,f133,f196,f225,f232,f276,f380,f421,f422,f607,f616,f617,f634,f644,f666,f671,f691,f711,f724,f768,f863,f884,f1061,f1070])).

fof(f1070,plain,(
    spl10_80 ),
    inference(avatar_contradiction_clause,[],[f1069])).

fof(f1069,plain,
    ( $false
    | spl10_80 ),
    inference(resolution,[],[f806,f36])).

fof(f36,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f806,plain,
    ( ~ r1_tarski(k1_xboole_0,k4_tarski(sK9(sK4,sK2,k1_xboole_0),sK4))
    | spl10_80 ),
    inference(avatar_component_clause,[],[f804])).

fof(f804,plain,
    ( spl10_80
  <=> r1_tarski(k1_xboole_0,k4_tarski(sK9(sK4,sK2,k1_xboole_0),sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_80])])).

fof(f1061,plain,
    ( ~ spl10_80
    | ~ spl10_74 ),
    inference(avatar_split_clause,[],[f1059,f770,f804])).

fof(f770,plain,
    ( spl10_74
  <=> r2_hidden(k4_tarski(sK9(sK4,sK2,k1_xboole_0),sK4),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_74])])).

fof(f1059,plain,
    ( ~ r1_tarski(k1_xboole_0,k4_tarski(sK9(sK4,sK2,k1_xboole_0),sK4))
    | ~ spl10_74 ),
    inference(resolution,[],[f772,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f772,plain,
    ( r2_hidden(k4_tarski(sK9(sK4,sK2,k1_xboole_0),sK4),k1_xboole_0)
    | ~ spl10_74 ),
    inference(avatar_component_clause,[],[f770])).

fof(f884,plain,
    ( ~ spl10_9
    | spl10_74
    | ~ spl10_73 ),
    inference(avatar_split_clause,[],[f871,f765,f770,f124])).

fof(f124,plain,
    ( spl10_9
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).

fof(f765,plain,
    ( spl10_73
  <=> r2_hidden(sK4,k9_relat_1(k1_xboole_0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_73])])).

fof(f871,plain,
    ( r2_hidden(k4_tarski(sK9(sK4,sK2,k1_xboole_0),sK4),k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl10_73 ),
    inference(resolution,[],[f767,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(k4_tarski(sK9(X0,X1,X2),X0),X2)
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

fof(f767,plain,
    ( r2_hidden(sK4,k9_relat_1(k1_xboole_0,sK2))
    | ~ spl10_73 ),
    inference(avatar_component_clause,[],[f765])).

fof(f863,plain,(
    ~ spl10_10 ),
    inference(avatar_contradiction_clause,[],[f860])).

fof(f860,plain,
    ( $false
    | ~ spl10_10 ),
    inference(resolution,[],[f129,f46])).

fof(f46,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f129,plain,
    ( ! [X0] : ~ v1_relat_1(X0)
    | ~ spl10_10 ),
    inference(avatar_component_clause,[],[f128])).

fof(f128,plain,
    ( spl10_10
  <=> ! [X0] : ~ v1_relat_1(X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).

fof(f768,plain,
    ( spl10_73
    | ~ spl10_15
    | ~ spl10_42 ),
    inference(avatar_split_clause,[],[f732,f396,f193,f765])).

fof(f193,plain,
    ( spl10_15
  <=> r2_hidden(sK4,k9_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_15])])).

fof(f396,plain,
    ( spl10_42
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_42])])).

fof(f732,plain,
    ( r2_hidden(sK4,k9_relat_1(k1_xboole_0,sK2))
    | ~ spl10_15
    | ~ spl10_42 ),
    inference(backward_demodulation,[],[f195,f398])).

fof(f398,plain,
    ( k1_xboole_0 = sK3
    | ~ spl10_42 ),
    inference(avatar_component_clause,[],[f396])).

fof(f195,plain,
    ( r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | ~ spl10_15 ),
    inference(avatar_component_clause,[],[f193])).

fof(f724,plain,
    ( k1_xboole_0 != sK1
    | sK0 != k1_relset_1(sK0,k1_xboole_0,sK3)
    | sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f711,plain,
    ( ~ spl10_62
    | spl10_66
    | ~ spl10_61 ),
    inference(avatar_split_clause,[],[f701,f663,f688,f668])).

fof(f668,plain,
    ( spl10_62
  <=> v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_62])])).

fof(f688,plain,
    ( spl10_66
  <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_66])])).

fof(f663,plain,
    ( spl10_61
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_61])])).

fof(f701,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | ~ v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | ~ spl10_61 ),
    inference(resolution,[],[f665,f72])).

fof(f72,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

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
    inference(flattening,[],[f26])).

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
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

fof(f665,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl10_61 ),
    inference(avatar_component_clause,[],[f663])).

fof(f691,plain,
    ( ~ spl10_66
    | ~ spl10_43
    | spl10_49 ),
    inference(avatar_split_clause,[],[f661,f466,f400,f688])).

fof(f400,plain,
    ( spl10_43
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_43])])).

fof(f466,plain,
    ( spl10_49
  <=> sK0 = k1_relset_1(sK0,k1_xboole_0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_49])])).

fof(f661,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | ~ spl10_43
    | spl10_49 ),
    inference(backward_demodulation,[],[f467,f402])).

fof(f402,plain,
    ( k1_xboole_0 = sK0
    | ~ spl10_43 ),
    inference(avatar_component_clause,[],[f400])).

fof(f467,plain,
    ( sK0 != k1_relset_1(sK0,k1_xboole_0,sK3)
    | spl10_49 ),
    inference(avatar_component_clause,[],[f466])).

fof(f671,plain,
    ( spl10_62
    | ~ spl10_34
    | ~ spl10_43 ),
    inference(avatar_split_clause,[],[f655,f400,f335,f668])).

fof(f335,plain,
    ( spl10_34
  <=> v1_funct_2(sK3,sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_34])])).

fof(f655,plain,
    ( v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | ~ spl10_34
    | ~ spl10_43 ),
    inference(backward_demodulation,[],[f337,f402])).

fof(f337,plain,
    ( v1_funct_2(sK3,sK0,k1_xboole_0)
    | ~ spl10_34 ),
    inference(avatar_component_clause,[],[f335])).

fof(f666,plain,
    ( spl10_61
    | ~ spl10_33
    | ~ spl10_43 ),
    inference(avatar_split_clause,[],[f654,f400,f330,f663])).

fof(f330,plain,
    ( spl10_33
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_33])])).

fof(f654,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl10_33
    | ~ spl10_43 ),
    inference(backward_demodulation,[],[f332,f402])).

fof(f332,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl10_33 ),
    inference(avatar_component_clause,[],[f330])).

fof(f644,plain,
    ( ~ spl10_34
    | spl10_42
    | spl10_43
    | ~ spl10_33 ),
    inference(avatar_split_clause,[],[f635,f330,f400,f396,f335])).

fof(f635,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK3
    | ~ v1_funct_2(sK3,sK0,k1_xboole_0)
    | ~ spl10_33 ),
    inference(resolution,[],[f332,f74])).

fof(f74,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0) ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X1
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f634,plain,
    ( spl10_33
    | ~ spl10_1
    | ~ spl10_31 ),
    inference(avatar_split_clause,[],[f323,f314,f78,f330])).

fof(f78,plain,
    ( spl10_1
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f314,plain,
    ( spl10_31
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_31])])).

fof(f323,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl10_1
    | ~ spl10_31 ),
    inference(backward_demodulation,[],[f80,f316])).

fof(f316,plain,
    ( k1_xboole_0 = sK1
    | ~ spl10_31 ),
    inference(avatar_component_clause,[],[f314])).

fof(f80,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f78])).

fof(f617,plain,
    ( sK0 != k1_relset_1(sK0,sK1,sK3)
    | k1_relat_1(sK3) != k1_relset_1(sK0,sK1,sK3)
    | r2_hidden(sK6(sK3,sK2,sK4),sK0)
    | ~ r2_hidden(sK6(sK3,sK2,sK4),k1_relat_1(sK3)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f616,plain,
    ( ~ spl10_19
    | ~ spl10_26
    | ~ spl10_57 ),
    inference(avatar_split_clause,[],[f615,f604,f273,f222])).

fof(f222,plain,
    ( spl10_19
  <=> r2_hidden(sK6(sK3,sK2,sK4),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_19])])).

fof(f273,plain,
    ( spl10_26
  <=> sK4 = k1_funct_1(sK3,sK6(sK3,sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_26])])).

fof(f604,plain,
    ( spl10_57
  <=> m1_subset_1(sK6(sK3,sK2,sK4),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_57])])).

fof(f615,plain,
    ( ~ r2_hidden(sK6(sK3,sK2,sK4),sK2)
    | ~ spl10_26
    | ~ spl10_57 ),
    inference(trivial_inequality_removal,[],[f614])).

fof(f614,plain,
    ( sK4 != sK4
    | ~ r2_hidden(sK6(sK3,sK2,sK4),sK2)
    | ~ spl10_26
    | ~ spl10_57 ),
    inference(forward_demodulation,[],[f613,f275])).

fof(f275,plain,
    ( sK4 = k1_funct_1(sK3,sK6(sK3,sK2,sK4))
    | ~ spl10_26 ),
    inference(avatar_component_clause,[],[f273])).

fof(f613,plain,
    ( ~ r2_hidden(sK6(sK3,sK2,sK4),sK2)
    | sK4 != k1_funct_1(sK3,sK6(sK3,sK2,sK4))
    | ~ spl10_57 ),
    inference(resolution,[],[f606,f31])).

fof(f31,plain,(
    ! [X5] :
      ( ~ m1_subset_1(X5,sK0)
      | ~ r2_hidden(X5,sK2)
      | sK4 != k1_funct_1(sK3,X5) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
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
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
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

fof(f606,plain,
    ( m1_subset_1(sK6(sK3,sK2,sK4),sK0)
    | ~ spl10_57 ),
    inference(avatar_component_clause,[],[f604])).

fof(f607,plain,
    ( spl10_57
    | ~ spl10_39 ),
    inference(avatar_split_clause,[],[f602,f365,f604])).

fof(f365,plain,
    ( spl10_39
  <=> r2_hidden(sK6(sK3,sK2,sK4),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_39])])).

fof(f602,plain,
    ( m1_subset_1(sK6(sK3,sK2,sK4),sK0)
    | ~ spl10_39 ),
    inference(resolution,[],[f442,f136])).

fof(f136,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(resolution,[],[f135,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f135,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(duplicate_literal_removal,[],[f134])).

fof(f134,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f49,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK8(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK8(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f442,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK0,k1_zfmisc_1(X0))
        | m1_subset_1(sK6(sK3,sK2,sK4),X0) )
    | ~ spl10_39 ),
    inference(resolution,[],[f367,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
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

fof(f367,plain,
    ( r2_hidden(sK6(sK3,sK2,sK4),sK0)
    | ~ spl10_39 ),
    inference(avatar_component_clause,[],[f365])).

fof(f422,plain,
    ( spl10_12
    | ~ spl10_1 ),
    inference(avatar_split_clause,[],[f413,f78,f159])).

fof(f159,plain,
    ( spl10_12
  <=> k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).

fof(f413,plain,
    ( k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3)
    | ~ spl10_1 ),
    inference(resolution,[],[f80,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f421,plain,
    ( ~ spl10_2
    | spl10_44
    | spl10_31
    | ~ spl10_1 ),
    inference(avatar_split_clause,[],[f410,f78,f314,f418,f83])).

fof(f83,plain,
    ( spl10_2
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f418,plain,
    ( spl10_44
  <=> sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_44])])).

fof(f410,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ v1_funct_2(sK3,sK0,sK1)
    | ~ spl10_1 ),
    inference(resolution,[],[f80,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f380,plain,
    ( spl10_34
    | ~ spl10_2
    | ~ spl10_31 ),
    inference(avatar_split_clause,[],[f324,f314,f83,f335])).

fof(f324,plain,
    ( v1_funct_2(sK3,sK0,k1_xboole_0)
    | ~ spl10_2
    | ~ spl10_31 ),
    inference(backward_demodulation,[],[f85,f316])).

fof(f85,plain,
    ( v1_funct_2(sK3,sK0,sK1)
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f83])).

fof(f276,plain,
    ( ~ spl10_7
    | spl10_26
    | ~ spl10_3
    | ~ spl10_15 ),
    inference(avatar_split_clause,[],[f270,f193,f88,f273,f115])).

fof(f115,plain,
    ( spl10_7
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).

fof(f88,plain,
    ( spl10_3
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f270,plain,
    ( ~ v1_funct_1(sK3)
    | sK4 = k1_funct_1(sK3,sK6(sK3,sK2,sK4))
    | ~ v1_relat_1(sK3)
    | ~ spl10_15 ),
    inference(resolution,[],[f69,f195])).

fof(f69,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | k1_funct_1(X0,sK6(X0,X1,X3)) = X3
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | k1_funct_1(X0,sK6(X0,X1,X3)) = X3
      | ~ r2_hidden(X3,X2)
      | k9_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_funct_1)).

fof(f232,plain,
    ( ~ spl10_7
    | spl10_20
    | ~ spl10_3
    | ~ spl10_15 ),
    inference(avatar_split_clause,[],[f227,f193,f88,f229,f115])).

fof(f229,plain,
    ( spl10_20
  <=> r2_hidden(sK6(sK3,sK2,sK4),k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_20])])).

fof(f227,plain,
    ( ~ v1_funct_1(sK3)
    | r2_hidden(sK6(sK3,sK2,sK4),k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ spl10_15 ),
    inference(resolution,[],[f71,f195])).

fof(f71,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | r2_hidden(sK6(X0,X1,X3),k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(sK6(X0,X1,X3),k1_relat_1(X0))
      | ~ r2_hidden(X3,X2)
      | k9_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f225,plain,
    ( ~ spl10_7
    | spl10_19
    | ~ spl10_3
    | ~ spl10_15 ),
    inference(avatar_split_clause,[],[f220,f193,f88,f222,f115])).

fof(f220,plain,
    ( ~ v1_funct_1(sK3)
    | r2_hidden(sK6(sK3,sK2,sK4),sK2)
    | ~ v1_relat_1(sK3)
    | ~ spl10_15 ),
    inference(resolution,[],[f70,f195])).

fof(f70,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | r2_hidden(sK6(X0,X1,X3),X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(sK6(X0,X1,X3),X1)
      | ~ r2_hidden(X3,X2)
      | k9_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f196,plain,
    ( spl10_15
    | ~ spl10_1
    | ~ spl10_4 ),
    inference(avatar_split_clause,[],[f181,f93,f78,f193])).

fof(f93,plain,
    ( spl10_4
  <=> r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f181,plain,
    ( r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | ~ spl10_1
    | ~ spl10_4 ),
    inference(backward_demodulation,[],[f95,f174])).

fof(f174,plain,
    ( ! [X0] : k7_relset_1(sK0,sK1,sK3,X0) = k9_relat_1(sK3,X0)
    | ~ spl10_1 ),
    inference(resolution,[],[f66,f80])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f95,plain,
    ( r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f93])).

fof(f133,plain,(
    spl10_8 ),
    inference(avatar_contradiction_clause,[],[f132])).

fof(f132,plain,
    ( $false
    | spl10_8 ),
    inference(resolution,[],[f121,f46])).

fof(f121,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | spl10_8 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl10_8
  <=> v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f130,plain,
    ( spl10_9
    | spl10_10 ),
    inference(avatar_split_clause,[],[f113,f128,f124])).

fof(f113,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[],[f37,f103])).

fof(f103,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(resolution,[],[f50,f36])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f122,plain,
    ( spl10_7
    | ~ spl10_8
    | ~ spl10_1 ),
    inference(avatar_split_clause,[],[f112,f78,f119,f115])).

fof(f112,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK3)
    | ~ spl10_1 ),
    inference(resolution,[],[f37,f80])).

fof(f96,plain,(
    spl10_4 ),
    inference(avatar_split_clause,[],[f32,f93])).

fof(f32,plain,(
    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f17])).

fof(f91,plain,(
    spl10_3 ),
    inference(avatar_split_clause,[],[f33,f88])).

fof(f33,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f17])).

fof(f86,plain,(
    spl10_2 ),
    inference(avatar_split_clause,[],[f34,f83])).

fof(f34,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f81,plain,(
    spl10_1 ),
    inference(avatar_split_clause,[],[f35,f78])).

fof(f35,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:22:45 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.49  % (9868)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.50  % (9877)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.50  % (9878)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.50  % (9877)Refutation not found, incomplete strategy% (9877)------------------------------
% 0.20/0.50  % (9877)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (9872)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.51  % (9866)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.51  % (9873)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.51  % (9885)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.52  % (9882)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.52  % (9890)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.52  % (9871)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.52  % (9889)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.52  % (9877)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (9877)Memory used [KB]: 10874
% 0.20/0.52  % (9877)Time elapsed: 0.090 s
% 0.20/0.52  % (9877)------------------------------
% 0.20/0.52  % (9877)------------------------------
% 0.20/0.52  % (9883)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.52  % (9874)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.53  % (9870)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.53  % (9892)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.53  % (9876)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.53  % (9891)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.53  % (9879)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  % (9880)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.53  % (9867)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.53  % (9875)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.53  % (9884)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.53  % (9881)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.54  % (9894)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.54  % (9886)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.54  % (9887)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.54  % (9893)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.54  % (9889)Refutation not found, incomplete strategy% (9889)------------------------------
% 0.20/0.54  % (9889)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (9889)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (9889)Memory used [KB]: 10874
% 0.20/0.54  % (9889)Time elapsed: 0.142 s
% 0.20/0.54  % (9889)------------------------------
% 0.20/0.54  % (9889)------------------------------
% 0.20/0.54  % (9888)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.55  % (9895)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.55  % (9896)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.56  % (9883)Refutation found. Thanks to Tanya!
% 0.20/0.56  % SZS status Theorem for theBenchmark
% 1.65/0.58  % SZS output start Proof for theBenchmark
% 1.65/0.58  fof(f1071,plain,(
% 1.65/0.58    $false),
% 1.65/0.58    inference(avatar_sat_refutation,[],[f81,f86,f91,f96,f122,f130,f133,f196,f225,f232,f276,f380,f421,f422,f607,f616,f617,f634,f644,f666,f671,f691,f711,f724,f768,f863,f884,f1061,f1070])).
% 1.65/0.58  fof(f1070,plain,(
% 1.65/0.58    spl10_80),
% 1.65/0.58    inference(avatar_contradiction_clause,[],[f1069])).
% 1.65/0.58  fof(f1069,plain,(
% 1.65/0.58    $false | spl10_80),
% 1.65/0.58    inference(resolution,[],[f806,f36])).
% 1.65/0.58  fof(f36,plain,(
% 1.65/0.58    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.65/0.58    inference(cnf_transformation,[],[f2])).
% 1.65/0.58  fof(f2,axiom,(
% 1.65/0.58    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.65/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.65/0.58  fof(f806,plain,(
% 1.65/0.58    ~r1_tarski(k1_xboole_0,k4_tarski(sK9(sK4,sK2,k1_xboole_0),sK4)) | spl10_80),
% 1.65/0.58    inference(avatar_component_clause,[],[f804])).
% 1.65/0.58  fof(f804,plain,(
% 1.65/0.58    spl10_80 <=> r1_tarski(k1_xboole_0,k4_tarski(sK9(sK4,sK2,k1_xboole_0),sK4))),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl10_80])])).
% 1.65/0.58  fof(f1061,plain,(
% 1.65/0.58    ~spl10_80 | ~spl10_74),
% 1.65/0.58    inference(avatar_split_clause,[],[f1059,f770,f804])).
% 1.65/0.58  fof(f770,plain,(
% 1.65/0.58    spl10_74 <=> r2_hidden(k4_tarski(sK9(sK4,sK2,k1_xboole_0),sK4),k1_xboole_0)),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl10_74])])).
% 1.65/0.58  fof(f1059,plain,(
% 1.65/0.58    ~r1_tarski(k1_xboole_0,k4_tarski(sK9(sK4,sK2,k1_xboole_0),sK4)) | ~spl10_74),
% 1.65/0.58    inference(resolution,[],[f772,f52])).
% 1.65/0.58  fof(f52,plain,(
% 1.65/0.58    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 1.65/0.58    inference(cnf_transformation,[],[f22])).
% 1.65/0.58  fof(f22,plain,(
% 1.65/0.58    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.65/0.58    inference(ennf_transformation,[],[f9])).
% 1.65/0.58  fof(f9,axiom,(
% 1.65/0.58    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.65/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 1.65/0.58  fof(f772,plain,(
% 1.65/0.58    r2_hidden(k4_tarski(sK9(sK4,sK2,k1_xboole_0),sK4),k1_xboole_0) | ~spl10_74),
% 1.65/0.58    inference(avatar_component_clause,[],[f770])).
% 1.65/0.58  fof(f884,plain,(
% 1.65/0.58    ~spl10_9 | spl10_74 | ~spl10_73),
% 1.65/0.58    inference(avatar_split_clause,[],[f871,f765,f770,f124])).
% 1.65/0.58  fof(f124,plain,(
% 1.65/0.58    spl10_9 <=> v1_relat_1(k1_xboole_0)),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).
% 1.65/0.58  fof(f765,plain,(
% 1.65/0.58    spl10_73 <=> r2_hidden(sK4,k9_relat_1(k1_xboole_0,sK2))),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl10_73])])).
% 1.65/0.58  fof(f871,plain,(
% 1.65/0.58    r2_hidden(k4_tarski(sK9(sK4,sK2,k1_xboole_0),sK4),k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~spl10_73),
% 1.65/0.58    inference(resolution,[],[f767,f54])).
% 1.65/0.58  fof(f54,plain,(
% 1.65/0.58    ( ! [X2,X0,X1] : (~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(k4_tarski(sK9(X0,X1,X2),X0),X2) | ~v1_relat_1(X2)) )),
% 1.65/0.58    inference(cnf_transformation,[],[f23])).
% 1.65/0.58  fof(f23,plain,(
% 1.65/0.58    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 1.65/0.58    inference(ennf_transformation,[],[f7])).
% 1.65/0.58  fof(f7,axiom,(
% 1.65/0.58    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 1.65/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).
% 1.65/0.58  fof(f767,plain,(
% 1.65/0.58    r2_hidden(sK4,k9_relat_1(k1_xboole_0,sK2)) | ~spl10_73),
% 1.65/0.58    inference(avatar_component_clause,[],[f765])).
% 1.65/0.58  fof(f863,plain,(
% 1.65/0.58    ~spl10_10),
% 1.65/0.58    inference(avatar_contradiction_clause,[],[f860])).
% 1.65/0.58  fof(f860,plain,(
% 1.65/0.58    $false | ~spl10_10),
% 1.65/0.58    inference(resolution,[],[f129,f46])).
% 1.65/0.58  fof(f46,plain,(
% 1.65/0.58    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.65/0.58    inference(cnf_transformation,[],[f6])).
% 1.65/0.58  fof(f6,axiom,(
% 1.65/0.58    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.65/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.65/0.58  fof(f129,plain,(
% 1.65/0.58    ( ! [X0] : (~v1_relat_1(X0)) ) | ~spl10_10),
% 1.65/0.58    inference(avatar_component_clause,[],[f128])).
% 1.65/0.58  fof(f128,plain,(
% 1.65/0.58    spl10_10 <=> ! [X0] : ~v1_relat_1(X0)),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).
% 1.65/0.58  fof(f768,plain,(
% 1.65/0.58    spl10_73 | ~spl10_15 | ~spl10_42),
% 1.65/0.58    inference(avatar_split_clause,[],[f732,f396,f193,f765])).
% 1.65/0.58  fof(f193,plain,(
% 1.65/0.58    spl10_15 <=> r2_hidden(sK4,k9_relat_1(sK3,sK2))),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl10_15])])).
% 1.65/0.58  fof(f396,plain,(
% 1.65/0.58    spl10_42 <=> k1_xboole_0 = sK3),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl10_42])])).
% 1.65/0.58  fof(f732,plain,(
% 1.65/0.58    r2_hidden(sK4,k9_relat_1(k1_xboole_0,sK2)) | (~spl10_15 | ~spl10_42)),
% 1.65/0.58    inference(backward_demodulation,[],[f195,f398])).
% 1.65/0.58  fof(f398,plain,(
% 1.65/0.58    k1_xboole_0 = sK3 | ~spl10_42),
% 1.65/0.58    inference(avatar_component_clause,[],[f396])).
% 1.65/0.58  fof(f195,plain,(
% 1.65/0.58    r2_hidden(sK4,k9_relat_1(sK3,sK2)) | ~spl10_15),
% 1.65/0.58    inference(avatar_component_clause,[],[f193])).
% 1.65/0.58  fof(f724,plain,(
% 1.65/0.58    k1_xboole_0 != sK1 | sK0 != k1_relset_1(sK0,k1_xboole_0,sK3) | sK0 = k1_relset_1(sK0,sK1,sK3)),
% 1.65/0.58    introduced(theory_tautology_sat_conflict,[])).
% 1.65/0.58  fof(f711,plain,(
% 1.65/0.58    ~spl10_62 | spl10_66 | ~spl10_61),
% 1.65/0.58    inference(avatar_split_clause,[],[f701,f663,f688,f668])).
% 1.65/0.58  fof(f668,plain,(
% 1.65/0.58    spl10_62 <=> v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl10_62])])).
% 1.65/0.58  fof(f688,plain,(
% 1.65/0.58    spl10_66 <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl10_66])])).
% 1.65/0.58  fof(f663,plain,(
% 1.65/0.58    spl10_61 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl10_61])])).
% 1.65/0.58  fof(f701,plain,(
% 1.65/0.58    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) | ~v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | ~spl10_61),
% 1.65/0.58    inference(resolution,[],[f665,f72])).
% 1.65/0.58  fof(f72,plain,(
% 1.65/0.58    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1)) )),
% 1.65/0.58    inference(equality_resolution,[],[f62])).
% 1.65/0.58  fof(f62,plain,(
% 1.65/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 1.65/0.58    inference(cnf_transformation,[],[f27])).
% 1.65/0.58  fof(f27,plain,(
% 1.65/0.58    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.65/0.58    inference(flattening,[],[f26])).
% 1.65/0.58  fof(f26,plain,(
% 1.65/0.58    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.65/0.58    inference(ennf_transformation,[],[f13])).
% 1.65/0.58  fof(f13,axiom,(
% 1.65/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.65/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.65/0.58  fof(f665,plain,(
% 1.65/0.58    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~spl10_61),
% 1.65/0.58    inference(avatar_component_clause,[],[f663])).
% 1.65/0.58  fof(f691,plain,(
% 1.65/0.58    ~spl10_66 | ~spl10_43 | spl10_49),
% 1.65/0.58    inference(avatar_split_clause,[],[f661,f466,f400,f688])).
% 1.65/0.58  fof(f400,plain,(
% 1.65/0.58    spl10_43 <=> k1_xboole_0 = sK0),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl10_43])])).
% 1.65/0.58  fof(f466,plain,(
% 1.65/0.58    spl10_49 <=> sK0 = k1_relset_1(sK0,k1_xboole_0,sK3)),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl10_49])])).
% 1.65/0.58  fof(f661,plain,(
% 1.65/0.58    k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) | (~spl10_43 | spl10_49)),
% 1.65/0.58    inference(backward_demodulation,[],[f467,f402])).
% 1.65/0.58  fof(f402,plain,(
% 1.65/0.58    k1_xboole_0 = sK0 | ~spl10_43),
% 1.65/0.58    inference(avatar_component_clause,[],[f400])).
% 1.65/0.58  fof(f467,plain,(
% 1.65/0.58    sK0 != k1_relset_1(sK0,k1_xboole_0,sK3) | spl10_49),
% 1.65/0.58    inference(avatar_component_clause,[],[f466])).
% 1.65/0.58  fof(f671,plain,(
% 1.65/0.58    spl10_62 | ~spl10_34 | ~spl10_43),
% 1.65/0.58    inference(avatar_split_clause,[],[f655,f400,f335,f668])).
% 1.65/0.58  fof(f335,plain,(
% 1.65/0.58    spl10_34 <=> v1_funct_2(sK3,sK0,k1_xboole_0)),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl10_34])])).
% 1.65/0.58  fof(f655,plain,(
% 1.65/0.58    v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | (~spl10_34 | ~spl10_43)),
% 1.65/0.58    inference(backward_demodulation,[],[f337,f402])).
% 1.65/0.58  fof(f337,plain,(
% 1.65/0.58    v1_funct_2(sK3,sK0,k1_xboole_0) | ~spl10_34),
% 1.65/0.58    inference(avatar_component_clause,[],[f335])).
% 1.65/0.58  fof(f666,plain,(
% 1.65/0.58    spl10_61 | ~spl10_33 | ~spl10_43),
% 1.65/0.58    inference(avatar_split_clause,[],[f654,f400,f330,f663])).
% 1.65/0.58  fof(f330,plain,(
% 1.65/0.58    spl10_33 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl10_33])])).
% 1.65/0.58  fof(f654,plain,(
% 1.65/0.58    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl10_33 | ~spl10_43)),
% 1.65/0.58    inference(backward_demodulation,[],[f332,f402])).
% 1.65/0.58  fof(f332,plain,(
% 1.65/0.58    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | ~spl10_33),
% 1.65/0.58    inference(avatar_component_clause,[],[f330])).
% 1.65/0.58  fof(f644,plain,(
% 1.65/0.58    ~spl10_34 | spl10_42 | spl10_43 | ~spl10_33),
% 1.65/0.58    inference(avatar_split_clause,[],[f635,f330,f400,f396,f335])).
% 1.65/0.58  fof(f635,plain,(
% 1.65/0.58    k1_xboole_0 = sK0 | k1_xboole_0 = sK3 | ~v1_funct_2(sK3,sK0,k1_xboole_0) | ~spl10_33),
% 1.65/0.58    inference(resolution,[],[f332,f74])).
% 1.65/0.58  fof(f74,plain,(
% 1.65/0.58    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | k1_xboole_0 = X0 | k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0)) )),
% 1.65/0.58    inference(equality_resolution,[],[f60])).
% 1.65/0.58  fof(f60,plain,(
% 1.65/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X1 | k1_xboole_0 = X0 | k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1)) )),
% 1.65/0.58    inference(cnf_transformation,[],[f27])).
% 1.65/0.58  fof(f634,plain,(
% 1.65/0.58    spl10_33 | ~spl10_1 | ~spl10_31),
% 1.65/0.58    inference(avatar_split_clause,[],[f323,f314,f78,f330])).
% 1.65/0.58  fof(f78,plain,(
% 1.65/0.58    spl10_1 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 1.65/0.58  fof(f314,plain,(
% 1.65/0.58    spl10_31 <=> k1_xboole_0 = sK1),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl10_31])])).
% 1.65/0.58  fof(f323,plain,(
% 1.65/0.58    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | (~spl10_1 | ~spl10_31)),
% 1.65/0.58    inference(backward_demodulation,[],[f80,f316])).
% 1.65/0.58  fof(f316,plain,(
% 1.65/0.58    k1_xboole_0 = sK1 | ~spl10_31),
% 1.65/0.58    inference(avatar_component_clause,[],[f314])).
% 1.65/0.58  fof(f80,plain,(
% 1.65/0.58    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl10_1),
% 1.65/0.58    inference(avatar_component_clause,[],[f78])).
% 1.65/0.58  fof(f617,plain,(
% 1.65/0.58    sK0 != k1_relset_1(sK0,sK1,sK3) | k1_relat_1(sK3) != k1_relset_1(sK0,sK1,sK3) | r2_hidden(sK6(sK3,sK2,sK4),sK0) | ~r2_hidden(sK6(sK3,sK2,sK4),k1_relat_1(sK3))),
% 1.65/0.58    introduced(theory_tautology_sat_conflict,[])).
% 1.65/0.58  fof(f616,plain,(
% 1.65/0.58    ~spl10_19 | ~spl10_26 | ~spl10_57),
% 1.65/0.58    inference(avatar_split_clause,[],[f615,f604,f273,f222])).
% 1.65/0.58  fof(f222,plain,(
% 1.65/0.58    spl10_19 <=> r2_hidden(sK6(sK3,sK2,sK4),sK2)),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl10_19])])).
% 1.65/0.58  fof(f273,plain,(
% 1.65/0.58    spl10_26 <=> sK4 = k1_funct_1(sK3,sK6(sK3,sK2,sK4))),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl10_26])])).
% 1.65/0.58  fof(f604,plain,(
% 1.65/0.58    spl10_57 <=> m1_subset_1(sK6(sK3,sK2,sK4),sK0)),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl10_57])])).
% 1.65/0.58  fof(f615,plain,(
% 1.65/0.58    ~r2_hidden(sK6(sK3,sK2,sK4),sK2) | (~spl10_26 | ~spl10_57)),
% 1.65/0.58    inference(trivial_inequality_removal,[],[f614])).
% 1.65/0.58  fof(f614,plain,(
% 1.65/0.58    sK4 != sK4 | ~r2_hidden(sK6(sK3,sK2,sK4),sK2) | (~spl10_26 | ~spl10_57)),
% 1.65/0.58    inference(forward_demodulation,[],[f613,f275])).
% 1.65/0.58  fof(f275,plain,(
% 1.65/0.58    sK4 = k1_funct_1(sK3,sK6(sK3,sK2,sK4)) | ~spl10_26),
% 1.65/0.58    inference(avatar_component_clause,[],[f273])).
% 1.65/0.58  fof(f613,plain,(
% 1.65/0.58    ~r2_hidden(sK6(sK3,sK2,sK4),sK2) | sK4 != k1_funct_1(sK3,sK6(sK3,sK2,sK4)) | ~spl10_57),
% 1.65/0.58    inference(resolution,[],[f606,f31])).
% 1.65/0.58  fof(f31,plain,(
% 1.65/0.58    ( ! [X5] : (~m1_subset_1(X5,sK0) | ~r2_hidden(X5,sK2) | sK4 != k1_funct_1(sK3,X5)) )),
% 1.65/0.58    inference(cnf_transformation,[],[f17])).
% 1.65/0.58  fof(f17,plain,(
% 1.65/0.58    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 1.65/0.58    inference(flattening,[],[f16])).
% 1.65/0.58  fof(f16,plain,(
% 1.65/0.58    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : ((k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2)) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 1.65/0.58    inference(ennf_transformation,[],[f15])).
% 1.65/0.58  fof(f15,negated_conjecture,(
% 1.65/0.58    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 1.65/0.58    inference(negated_conjecture,[],[f14])).
% 1.65/0.58  fof(f14,conjecture,(
% 1.65/0.58    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 1.65/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_funct_2)).
% 1.65/0.58  fof(f606,plain,(
% 1.65/0.58    m1_subset_1(sK6(sK3,sK2,sK4),sK0) | ~spl10_57),
% 1.65/0.58    inference(avatar_component_clause,[],[f604])).
% 1.65/0.58  fof(f607,plain,(
% 1.65/0.58    spl10_57 | ~spl10_39),
% 1.65/0.58    inference(avatar_split_clause,[],[f602,f365,f604])).
% 1.65/0.58  fof(f365,plain,(
% 1.65/0.58    spl10_39 <=> r2_hidden(sK6(sK3,sK2,sK4),sK0)),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl10_39])])).
% 1.65/0.58  fof(f602,plain,(
% 1.65/0.58    m1_subset_1(sK6(sK3,sK2,sK4),sK0) | ~spl10_39),
% 1.65/0.58    inference(resolution,[],[f442,f136])).
% 1.65/0.58  fof(f136,plain,(
% 1.65/0.58    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 1.65/0.58    inference(resolution,[],[f135,f50])).
% 1.65/0.58  fof(f50,plain,(
% 1.65/0.58    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.65/0.58    inference(cnf_transformation,[],[f3])).
% 1.65/0.58  fof(f3,axiom,(
% 1.65/0.58    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.65/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.65/0.58  fof(f135,plain,(
% 1.65/0.58    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 1.65/0.58    inference(duplicate_literal_removal,[],[f134])).
% 1.65/0.58  fof(f134,plain,(
% 1.65/0.58    ( ! [X0] : (r1_tarski(X0,X0) | r1_tarski(X0,X0)) )),
% 1.65/0.58    inference(resolution,[],[f49,f48])).
% 1.65/0.58  fof(f48,plain,(
% 1.65/0.58    ( ! [X0,X1] : (r2_hidden(sK8(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.65/0.58    inference(cnf_transformation,[],[f21])).
% 1.65/0.58  fof(f21,plain,(
% 1.65/0.58    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.65/0.58    inference(ennf_transformation,[],[f1])).
% 1.65/0.58  fof(f1,axiom,(
% 1.65/0.58    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.65/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.65/0.58  fof(f49,plain,(
% 1.65/0.58    ( ! [X0,X1] : (~r2_hidden(sK8(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.65/0.58    inference(cnf_transformation,[],[f21])).
% 1.65/0.58  fof(f442,plain,(
% 1.65/0.58    ( ! [X0] : (~m1_subset_1(sK0,k1_zfmisc_1(X0)) | m1_subset_1(sK6(sK3,sK2,sK4),X0)) ) | ~spl10_39),
% 1.65/0.58    inference(resolution,[],[f367,f65])).
% 1.65/0.58  fof(f65,plain,(
% 1.65/0.58    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2)) )),
% 1.65/0.58    inference(cnf_transformation,[],[f29])).
% 1.65/0.58  fof(f29,plain,(
% 1.65/0.58    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.65/0.58    inference(flattening,[],[f28])).
% 1.65/0.58  fof(f28,plain,(
% 1.65/0.58    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 1.65/0.58    inference(ennf_transformation,[],[f4])).
% 1.65/0.58  fof(f4,axiom,(
% 1.65/0.58    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 1.65/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 1.65/0.58  fof(f367,plain,(
% 1.65/0.58    r2_hidden(sK6(sK3,sK2,sK4),sK0) | ~spl10_39),
% 1.65/0.58    inference(avatar_component_clause,[],[f365])).
% 1.65/0.58  fof(f422,plain,(
% 1.65/0.58    spl10_12 | ~spl10_1),
% 1.65/0.58    inference(avatar_split_clause,[],[f413,f78,f159])).
% 1.65/0.58  fof(f159,plain,(
% 1.65/0.58    spl10_12 <=> k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3)),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).
% 1.65/0.58  fof(f413,plain,(
% 1.65/0.58    k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3) | ~spl10_1),
% 1.65/0.58    inference(resolution,[],[f80,f58])).
% 1.65/0.58  fof(f58,plain,(
% 1.65/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relat_1(X2) = k1_relset_1(X0,X1,X2)) )),
% 1.65/0.58    inference(cnf_transformation,[],[f25])).
% 1.65/0.58  fof(f25,plain,(
% 1.65/0.58    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.65/0.58    inference(ennf_transformation,[],[f11])).
% 1.65/0.58  fof(f11,axiom,(
% 1.65/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 1.65/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.65/0.58  fof(f421,plain,(
% 1.65/0.58    ~spl10_2 | spl10_44 | spl10_31 | ~spl10_1),
% 1.65/0.58    inference(avatar_split_clause,[],[f410,f78,f314,f418,f83])).
% 1.65/0.58  fof(f83,plain,(
% 1.65/0.58    spl10_2 <=> v1_funct_2(sK3,sK0,sK1)),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 1.65/0.58  fof(f418,plain,(
% 1.65/0.58    spl10_44 <=> sK0 = k1_relset_1(sK0,sK1,sK3)),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl10_44])])).
% 1.65/0.58  fof(f410,plain,(
% 1.65/0.58    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3) | ~v1_funct_2(sK3,sK0,sK1) | ~spl10_1),
% 1.65/0.58    inference(resolution,[],[f80,f64])).
% 1.65/0.58  fof(f64,plain,(
% 1.65/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 1.65/0.58    inference(cnf_transformation,[],[f27])).
% 1.65/0.58  fof(f380,plain,(
% 1.65/0.58    spl10_34 | ~spl10_2 | ~spl10_31),
% 1.65/0.58    inference(avatar_split_clause,[],[f324,f314,f83,f335])).
% 1.65/0.58  fof(f324,plain,(
% 1.65/0.58    v1_funct_2(sK3,sK0,k1_xboole_0) | (~spl10_2 | ~spl10_31)),
% 1.65/0.58    inference(backward_demodulation,[],[f85,f316])).
% 1.65/0.58  fof(f85,plain,(
% 1.65/0.58    v1_funct_2(sK3,sK0,sK1) | ~spl10_2),
% 1.65/0.58    inference(avatar_component_clause,[],[f83])).
% 1.65/0.58  fof(f276,plain,(
% 1.65/0.58    ~spl10_7 | spl10_26 | ~spl10_3 | ~spl10_15),
% 1.65/0.58    inference(avatar_split_clause,[],[f270,f193,f88,f273,f115])).
% 1.65/0.58  fof(f115,plain,(
% 1.65/0.58    spl10_7 <=> v1_relat_1(sK3)),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).
% 1.65/0.58  fof(f88,plain,(
% 1.65/0.58    spl10_3 <=> v1_funct_1(sK3)),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).
% 1.65/0.58  fof(f270,plain,(
% 1.65/0.58    ~v1_funct_1(sK3) | sK4 = k1_funct_1(sK3,sK6(sK3,sK2,sK4)) | ~v1_relat_1(sK3) | ~spl10_15),
% 1.65/0.58    inference(resolution,[],[f69,f195])).
% 1.65/0.58  fof(f69,plain,(
% 1.65/0.58    ( ! [X0,X3,X1] : (~r2_hidden(X3,k9_relat_1(X0,X1)) | ~v1_funct_1(X0) | k1_funct_1(X0,sK6(X0,X1,X3)) = X3 | ~v1_relat_1(X0)) )),
% 1.65/0.58    inference(equality_resolution,[],[f44])).
% 1.65/0.58  fof(f44,plain,(
% 1.65/0.58    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_funct_1(X0,sK6(X0,X1,X3)) = X3 | ~r2_hidden(X3,X2) | k9_relat_1(X0,X1) != X2) )),
% 1.65/0.58    inference(cnf_transformation,[],[f20])).
% 1.65/0.59  fof(f20,plain,(
% 1.65/0.59    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.65/0.59    inference(flattening,[],[f19])).
% 1.65/0.59  fof(f19,plain,(
% 1.65/0.59    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.65/0.59    inference(ennf_transformation,[],[f8])).
% 1.65/0.59  fof(f8,axiom,(
% 1.65/0.59    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))))),
% 1.65/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_funct_1)).
% 1.65/0.59  fof(f232,plain,(
% 1.65/0.59    ~spl10_7 | spl10_20 | ~spl10_3 | ~spl10_15),
% 1.65/0.59    inference(avatar_split_clause,[],[f227,f193,f88,f229,f115])).
% 1.65/0.59  fof(f229,plain,(
% 1.65/0.59    spl10_20 <=> r2_hidden(sK6(sK3,sK2,sK4),k1_relat_1(sK3))),
% 1.65/0.59    introduced(avatar_definition,[new_symbols(naming,[spl10_20])])).
% 1.65/0.59  fof(f227,plain,(
% 1.65/0.59    ~v1_funct_1(sK3) | r2_hidden(sK6(sK3,sK2,sK4),k1_relat_1(sK3)) | ~v1_relat_1(sK3) | ~spl10_15),
% 1.65/0.59    inference(resolution,[],[f71,f195])).
% 1.65/0.59  fof(f71,plain,(
% 1.65/0.59    ( ! [X0,X3,X1] : (~r2_hidden(X3,k9_relat_1(X0,X1)) | ~v1_funct_1(X0) | r2_hidden(sK6(X0,X1,X3),k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.65/0.59    inference(equality_resolution,[],[f42])).
% 1.65/0.59  fof(f42,plain,(
% 1.65/0.59    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | r2_hidden(sK6(X0,X1,X3),k1_relat_1(X0)) | ~r2_hidden(X3,X2) | k9_relat_1(X0,X1) != X2) )),
% 1.65/0.59    inference(cnf_transformation,[],[f20])).
% 1.65/0.59  fof(f225,plain,(
% 1.65/0.59    ~spl10_7 | spl10_19 | ~spl10_3 | ~spl10_15),
% 1.65/0.59    inference(avatar_split_clause,[],[f220,f193,f88,f222,f115])).
% 1.65/0.59  fof(f220,plain,(
% 1.65/0.59    ~v1_funct_1(sK3) | r2_hidden(sK6(sK3,sK2,sK4),sK2) | ~v1_relat_1(sK3) | ~spl10_15),
% 1.65/0.59    inference(resolution,[],[f70,f195])).
% 1.65/0.59  fof(f70,plain,(
% 1.65/0.59    ( ! [X0,X3,X1] : (~r2_hidden(X3,k9_relat_1(X0,X1)) | ~v1_funct_1(X0) | r2_hidden(sK6(X0,X1,X3),X1) | ~v1_relat_1(X0)) )),
% 1.65/0.59    inference(equality_resolution,[],[f43])).
% 1.65/0.59  fof(f43,plain,(
% 1.65/0.59    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | r2_hidden(sK6(X0,X1,X3),X1) | ~r2_hidden(X3,X2) | k9_relat_1(X0,X1) != X2) )),
% 1.65/0.59    inference(cnf_transformation,[],[f20])).
% 1.65/0.59  fof(f196,plain,(
% 1.65/0.59    spl10_15 | ~spl10_1 | ~spl10_4),
% 1.65/0.59    inference(avatar_split_clause,[],[f181,f93,f78,f193])).
% 1.65/0.59  fof(f93,plain,(
% 1.65/0.59    spl10_4 <=> r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))),
% 1.65/0.59    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).
% 1.65/0.59  fof(f181,plain,(
% 1.65/0.59    r2_hidden(sK4,k9_relat_1(sK3,sK2)) | (~spl10_1 | ~spl10_4)),
% 1.65/0.59    inference(backward_demodulation,[],[f95,f174])).
% 1.65/0.59  fof(f174,plain,(
% 1.65/0.59    ( ! [X0] : (k7_relset_1(sK0,sK1,sK3,X0) = k9_relat_1(sK3,X0)) ) | ~spl10_1),
% 1.65/0.59    inference(resolution,[],[f66,f80])).
% 1.65/0.59  fof(f66,plain,(
% 1.65/0.59    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 1.65/0.59    inference(cnf_transformation,[],[f30])).
% 1.65/0.59  fof(f30,plain,(
% 1.65/0.59    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.65/0.59    inference(ennf_transformation,[],[f12])).
% 1.65/0.59  fof(f12,axiom,(
% 1.65/0.59    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 1.65/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 1.65/0.59  fof(f95,plain,(
% 1.65/0.59    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) | ~spl10_4),
% 1.65/0.59    inference(avatar_component_clause,[],[f93])).
% 1.65/0.59  fof(f133,plain,(
% 1.65/0.59    spl10_8),
% 1.65/0.59    inference(avatar_contradiction_clause,[],[f132])).
% 1.65/0.59  fof(f132,plain,(
% 1.65/0.59    $false | spl10_8),
% 1.65/0.59    inference(resolution,[],[f121,f46])).
% 1.65/0.59  fof(f121,plain,(
% 1.65/0.59    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | spl10_8),
% 1.65/0.59    inference(avatar_component_clause,[],[f119])).
% 1.65/0.59  fof(f119,plain,(
% 1.65/0.59    spl10_8 <=> v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 1.65/0.59    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).
% 1.65/0.59  fof(f130,plain,(
% 1.65/0.59    spl10_9 | spl10_10),
% 1.65/0.59    inference(avatar_split_clause,[],[f113,f128,f124])).
% 1.65/0.59  fof(f113,plain,(
% 1.65/0.59    ( ! [X0] : (~v1_relat_1(X0) | v1_relat_1(k1_xboole_0)) )),
% 1.65/0.59    inference(resolution,[],[f37,f103])).
% 1.65/0.59  fof(f103,plain,(
% 1.65/0.59    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.65/0.59    inference(resolution,[],[f50,f36])).
% 1.65/0.59  fof(f37,plain,(
% 1.65/0.59    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 1.65/0.59    inference(cnf_transformation,[],[f18])).
% 1.65/0.59  fof(f18,plain,(
% 1.65/0.59    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.65/0.59    inference(ennf_transformation,[],[f5])).
% 1.65/0.59  fof(f5,axiom,(
% 1.65/0.59    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.65/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.65/0.59  fof(f122,plain,(
% 1.65/0.59    spl10_7 | ~spl10_8 | ~spl10_1),
% 1.65/0.59    inference(avatar_split_clause,[],[f112,f78,f119,f115])).
% 1.65/0.59  fof(f112,plain,(
% 1.65/0.59    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | v1_relat_1(sK3) | ~spl10_1),
% 1.65/0.59    inference(resolution,[],[f37,f80])).
% 1.65/0.59  fof(f96,plain,(
% 1.65/0.59    spl10_4),
% 1.65/0.59    inference(avatar_split_clause,[],[f32,f93])).
% 1.65/0.59  fof(f32,plain,(
% 1.65/0.59    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))),
% 1.65/0.59    inference(cnf_transformation,[],[f17])).
% 1.65/0.59  fof(f91,plain,(
% 1.65/0.59    spl10_3),
% 1.65/0.59    inference(avatar_split_clause,[],[f33,f88])).
% 1.65/0.59  fof(f33,plain,(
% 1.65/0.59    v1_funct_1(sK3)),
% 1.65/0.59    inference(cnf_transformation,[],[f17])).
% 1.65/0.59  fof(f86,plain,(
% 1.65/0.59    spl10_2),
% 1.65/0.59    inference(avatar_split_clause,[],[f34,f83])).
% 1.65/0.59  fof(f34,plain,(
% 1.65/0.59    v1_funct_2(sK3,sK0,sK1)),
% 1.65/0.59    inference(cnf_transformation,[],[f17])).
% 1.65/0.59  fof(f81,plain,(
% 1.65/0.59    spl10_1),
% 1.65/0.59    inference(avatar_split_clause,[],[f35,f78])).
% 1.65/0.59  fof(f35,plain,(
% 1.65/0.59    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.65/0.59    inference(cnf_transformation,[],[f17])).
% 1.65/0.59  % SZS output end Proof for theBenchmark
% 1.65/0.59  % (9883)------------------------------
% 1.65/0.59  % (9883)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.65/0.59  % (9883)Termination reason: Refutation
% 1.65/0.59  
% 1.65/0.59  % (9883)Memory used [KB]: 11385
% 1.65/0.59  % (9883)Time elapsed: 0.164 s
% 1.65/0.59  % (9883)------------------------------
% 1.65/0.59  % (9883)------------------------------
% 1.77/0.59  % (9865)Success in time 0.232 s
%------------------------------------------------------------------------------
