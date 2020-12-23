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
% DateTime   : Thu Dec  3 13:03:04 EST 2020

% Result     : Theorem 1.46s
% Output     : Refutation 1.46s
% Verified   : 
% Statistics : Number of formulae       :  248 ( 535 expanded)
%              Number of leaves         :   54 ( 202 expanded)
%              Depth                    :   11
%              Number of atoms          :  876 (2412 expanded)
%              Number of equality atoms :  184 ( 692 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f816,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f101,f110,f114,f119,f135,f137,f166,f245,f247,f265,f267,f269,f290,f292,f302,f340,f397,f402,f424,f434,f456,f476,f489,f501,f564,f592,f679,f692,f722,f727,f760,f763,f778,f784,f789,f793,f801,f813])).

fof(f813,plain,
    ( ~ spl4_36
    | ~ spl4_69 ),
    inference(avatar_contradiction_clause,[],[f805])).

fof(f805,plain,
    ( $false
    | ~ spl4_36
    | ~ spl4_69 ),
    inference(subsumption_resolution,[],[f50,f803])).

fof(f803,plain,
    ( sK3 = k2_funct_1(sK2)
    | ~ spl4_36
    | ~ spl4_69 ),
    inference(forward_demodulation,[],[f705,f443])).

fof(f443,plain,
    ( sK2 = k2_funct_1(sK3)
    | ~ spl4_36 ),
    inference(avatar_component_clause,[],[f441])).

fof(f441,plain,
    ( spl4_36
  <=> sK2 = k2_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f705,plain,
    ( sK3 = k2_funct_1(k2_funct_1(sK3))
    | ~ spl4_69 ),
    inference(avatar_component_clause,[],[f703])).

fof(f703,plain,
    ( spl4_69
  <=> sK3 = k2_funct_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_69])])).

fof(f50,plain,(
    sK3 != k2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
           => ( ( v2_funct_1(X2)
                & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
                & k2_relset_1(X0,X1,X2) = X1 )
             => ( k2_funct_1(X2) = X3
                | k1_xboole_0 = X1
                | k1_xboole_0 = X0 ) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( ( v2_funct_1(X2)
              & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
              & k2_relset_1(X0,X1,X2) = X1 )
           => ( k2_funct_1(X2) = X3
              | k1_xboole_0 = X1
              | k1_xboole_0 = X0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).

fof(f801,plain,
    ( ~ spl4_22
    | ~ spl4_36
    | spl4_73 ),
    inference(avatar_contradiction_clause,[],[f800])).

fof(f800,plain,
    ( $false
    | ~ spl4_22
    | ~ spl4_36
    | spl4_73 ),
    inference(subsumption_resolution,[],[f366,f795])).

fof(f795,plain,
    ( sK0 != k1_relat_1(sK2)
    | ~ spl4_36
    | spl4_73 ),
    inference(forward_demodulation,[],[f721,f443])).

fof(f721,plain,
    ( sK0 != k1_relat_1(k2_funct_1(sK3))
    | spl4_73 ),
    inference(avatar_component_clause,[],[f719])).

fof(f719,plain,
    ( spl4_73
  <=> sK0 = k1_relat_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_73])])).

fof(f366,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl4_22 ),
    inference(forward_demodulation,[],[f353,f79])).

fof(f79,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f57,f54])).

fof(f54,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f57,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f353,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k6_partfun1(sK0))
    | ~ spl4_22 ),
    inference(superposition,[],[f79,f300])).

fof(f300,plain,
    ( k6_partfun1(sK0) = k6_partfun1(k1_relat_1(sK2))
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f298])).

fof(f298,plain,
    ( spl4_22
  <=> k6_partfun1(sK0) = k6_partfun1(k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f793,plain,
    ( ~ spl4_6
    | ~ spl4_36
    | spl4_72 ),
    inference(avatar_contradiction_clause,[],[f792])).

fof(f792,plain,
    ( $false
    | ~ spl4_6
    | ~ spl4_36
    | spl4_72 ),
    inference(trivial_inequality_removal,[],[f791])).

fof(f791,plain,
    ( k6_partfun1(sK1) != k6_partfun1(sK1)
    | ~ spl4_6
    | ~ spl4_36
    | spl4_72 ),
    inference(forward_demodulation,[],[f790,f133])).

fof(f133,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f131])).

fof(f131,plain,
    ( spl4_6
  <=> sK1 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f790,plain,
    ( k6_partfun1(k2_relat_1(sK2)) != k6_partfun1(sK1)
    | ~ spl4_36
    | spl4_72 ),
    inference(forward_demodulation,[],[f717,f443])).

fof(f717,plain,
    ( k6_partfun1(sK1) != k6_partfun1(k2_relat_1(k2_funct_1(sK3)))
    | spl4_72 ),
    inference(avatar_component_clause,[],[f715])).

fof(f715,plain,
    ( spl4_72
  <=> k6_partfun1(sK1) = k6_partfun1(k2_relat_1(k2_funct_1(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_72])])).

fof(f789,plain,
    ( ~ spl4_36
    | spl4_71 ),
    inference(avatar_contradiction_clause,[],[f788])).

fof(f788,plain,
    ( $false
    | ~ spl4_36
    | spl4_71 ),
    inference(subsumption_resolution,[],[f47,f786])).

fof(f786,plain,
    ( ~ v2_funct_1(sK2)
    | ~ spl4_36
    | spl4_71 ),
    inference(forward_demodulation,[],[f713,f443])).

fof(f713,plain,
    ( ~ v2_funct_1(k2_funct_1(sK3))
    | spl4_71 ),
    inference(avatar_component_clause,[],[f711])).

fof(f711,plain,
    ( spl4_71
  <=> v2_funct_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_71])])).

fof(f47,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f784,plain,
    ( ~ spl4_36
    | spl4_70 ),
    inference(avatar_contradiction_clause,[],[f783])).

fof(f783,plain,
    ( $false
    | ~ spl4_36
    | spl4_70 ),
    inference(unit_resulting_resolution,[],[f64,f53,f779,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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

fof(f779,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl4_36
    | spl4_70 ),
    inference(forward_demodulation,[],[f709,f443])).

fof(f709,plain,
    ( ~ v1_relat_1(k2_funct_1(sK3))
    | spl4_70 ),
    inference(avatar_component_clause,[],[f707])).

fof(f707,plain,
    ( spl4_70
  <=> v1_relat_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_70])])).

fof(f53,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f20])).

fof(f64,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f778,plain,
    ( ~ spl4_36
    | spl4_67 ),
    inference(avatar_contradiction_clause,[],[f777])).

fof(f777,plain,
    ( $false
    | ~ spl4_36
    | spl4_67 ),
    inference(subsumption_resolution,[],[f51,f765])).

fof(f765,plain,
    ( ~ v1_funct_1(sK2)
    | ~ spl4_36
    | spl4_67 ),
    inference(superposition,[],[f696,f443])).

fof(f696,plain,
    ( ~ v1_funct_1(k2_funct_1(sK3))
    | spl4_67 ),
    inference(avatar_component_clause,[],[f694])).

fof(f694,plain,
    ( spl4_67
  <=> v1_funct_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_67])])).

fof(f51,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f763,plain,
    ( spl4_38
    | ~ spl4_43 ),
    inference(avatar_contradiction_clause,[],[f762])).

fof(f762,plain,
    ( $false
    | spl4_38
    | ~ spl4_43 ),
    inference(trivial_inequality_removal,[],[f761])).

fof(f761,plain,
    ( k6_partfun1(sK0) != k6_partfun1(sK0)
    | spl4_38
    | ~ spl4_43 ),
    inference(forward_demodulation,[],[f451,f499])).

fof(f499,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ spl4_43 ),
    inference(avatar_component_clause,[],[f497])).

fof(f497,plain,
    ( spl4_43
  <=> sK0 = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).

fof(f451,plain,
    ( k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3))
    | spl4_38 ),
    inference(avatar_component_clause,[],[f449])).

fof(f449,plain,
    ( spl4_38
  <=> k6_partfun1(sK0) = k6_partfun1(k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).

fof(f760,plain,
    ( spl4_39
    | ~ spl4_66 ),
    inference(avatar_contradiction_clause,[],[f757])).

fof(f757,plain,
    ( $false
    | spl4_39
    | ~ spl4_66 ),
    inference(subsumption_resolution,[],[f455,f755])).

fof(f755,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl4_66 ),
    inference(forward_demodulation,[],[f736,f79])).

fof(f736,plain,
    ( k1_relat_1(sK3) = k2_relat_1(k6_partfun1(sK1))
    | ~ spl4_66 ),
    inference(superposition,[],[f79,f690])).

fof(f690,plain,
    ( k6_partfun1(k1_relat_1(sK3)) = k6_partfun1(sK1)
    | ~ spl4_66 ),
    inference(avatar_component_clause,[],[f688])).

fof(f688,plain,
    ( spl4_66
  <=> k6_partfun1(k1_relat_1(sK3)) = k6_partfun1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_66])])).

fof(f455,plain,
    ( sK1 != k1_relat_1(sK3)
    | spl4_39 ),
    inference(avatar_component_clause,[],[f453])).

fof(f453,plain,
    ( spl4_39
  <=> sK1 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).

fof(f727,plain,
    ( ~ spl4_41
    | ~ spl4_15
    | ~ spl4_16
    | spl4_54
    | spl4_37
    | ~ spl4_35
    | ~ spl4_8
    | ~ spl4_57 ),
    inference(avatar_split_clause,[],[f724,f590,f163,f421,f445,f561,f231,f227,f473])).

fof(f473,plain,
    ( spl4_41
  <=> v1_funct_2(sK3,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).

fof(f227,plain,
    ( spl4_15
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f231,plain,
    ( spl4_16
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f561,plain,
    ( spl4_54
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_54])])).

fof(f445,plain,
    ( spl4_37
  <=> v2_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).

fof(f421,plain,
    ( spl4_35
  <=> v2_funct_1(k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).

fof(f163,plain,
    ( spl4_8
  <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f590,plain,
    ( spl4_57
  <=> ! [X1,X0] :
        ( ~ v1_funct_1(X0)
        | v2_funct_1(X0)
        | k1_xboole_0 = X1
        | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X1,sK2,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
        | ~ v1_funct_2(X0,sK1,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_57])])).

fof(f724,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | v2_funct_1(sK3)
    | k1_xboole_0 = sK0
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ spl4_8
    | ~ spl4_57 ),
    inference(superposition,[],[f591,f165])).

fof(f165,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f163])).

fof(f591,plain,
    ( ! [X0,X1] :
        ( ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X1,sK2,X0))
        | v2_funct_1(X0)
        | k1_xboole_0 = X1
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
        | ~ v1_funct_2(X0,sK1,X1) )
    | ~ spl4_57 ),
    inference(avatar_component_clause,[],[f590])).

fof(f722,plain,
    ( spl4_69
    | ~ spl4_70
    | ~ spl4_71
    | ~ spl4_16
    | ~ spl4_1
    | ~ spl4_67
    | ~ spl4_72
    | ~ spl4_73
    | ~ spl4_43
    | ~ spl4_53 ),
    inference(avatar_split_clause,[],[f701,f557,f497,f719,f715,f694,f94,f231,f711,f707,f703])).

fof(f94,plain,
    ( spl4_1
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f557,plain,
    ( spl4_53
  <=> k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_53])])).

fof(f701,plain,
    ( sK0 != k1_relat_1(k2_funct_1(sK3))
    | k6_partfun1(sK1) != k6_partfun1(k2_relat_1(k2_funct_1(sK3)))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | sK3 = k2_funct_1(k2_funct_1(sK3))
    | ~ spl4_43
    | ~ spl4_53 ),
    inference(forward_demodulation,[],[f685,f499])).

fof(f685,plain,
    ( k6_partfun1(sK1) != k6_partfun1(k2_relat_1(k2_funct_1(sK3)))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(k2_funct_1(sK3))
    | k2_relat_1(sK3) != k1_relat_1(k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | sK3 = k2_funct_1(k2_funct_1(sK3))
    | ~ spl4_53 ),
    inference(superposition,[],[f85,f559])).

fof(f559,plain,
    ( k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ spl4_53 ),
    inference(avatar_component_clause,[],[f557])).

fof(f85,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(X0)
      | k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k2_funct_1(X0) = X1 ) ),
    inference(definition_unfolding,[],[f63,f54])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(X0)
      | k1_relat_1(X0) != k2_relat_1(X1)
      | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
      | k2_funct_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0)
              & k1_relat_1(X0) = k2_relat_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_1)).

fof(f692,plain,
    ( ~ spl4_1
    | ~ spl4_37
    | ~ spl4_16
    | spl4_66
    | ~ spl4_53 ),
    inference(avatar_split_clause,[],[f683,f557,f688,f231,f445,f94])).

fof(f683,plain,
    ( k6_partfun1(k1_relat_1(sK3)) = k6_partfun1(sK1)
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_53 ),
    inference(superposition,[],[f83,f559])).

fof(f83,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f60,f54])).

fof(f60,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

fof(f679,plain,(
    ~ spl4_54 ),
    inference(avatar_contradiction_clause,[],[f662])).

fof(f662,plain,
    ( $false
    | ~ spl4_54 ),
    inference(subsumption_resolution,[],[f48,f563])).

fof(f563,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_54 ),
    inference(avatar_component_clause,[],[f561])).

fof(f48,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f20])).

fof(f592,plain,
    ( ~ spl4_13
    | spl4_57
    | ~ spl4_5
    | ~ spl4_21 ),
    inference(avatar_split_clause,[],[f588,f287,f127,f590,f214])).

fof(f214,plain,
    ( spl4_13
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f127,plain,
    ( spl4_5
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f287,plain,
    ( spl4_21
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f588,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(sK2,sK0,sK1)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,sK1,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
      | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X1,sK2,X0))
      | ~ v1_funct_1(sK2)
      | k1_xboole_0 = X1
      | v2_funct_1(X0) ) ),
    inference(trivial_inequality_removal,[],[f583])).

fof(f583,plain,(
    ! [X0,X1] :
      ( sK1 != sK1
      | ~ v1_funct_2(sK2,sK0,sK1)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,sK1,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
      | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X1,sK2,X0))
      | ~ v1_funct_1(sK2)
      | k1_xboole_0 = X1
      | v2_funct_1(X0) ) ),
    inference(superposition,[],[f72,f45])).

fof(f45,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f72,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X3) != X1
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,X1,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
      | ~ v1_funct_1(X3)
      | k1_xboole_0 = X2
      | v2_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ( v2_funct_1(X4)
            & v2_funct_1(X3) )
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | k2_relset_1(X0,X1,X3) != X1
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ( v2_funct_1(X4)
            & v2_funct_1(X3) )
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | k2_relset_1(X0,X1,X3) != X1
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
         => ( ( k2_relset_1(X0,X1,X3) = X1
              & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) )
           => ( ( v2_funct_1(X4)
                & v2_funct_1(X3) )
              | ( k1_xboole_0 != X1
                & k1_xboole_0 = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_funct_2)).

fof(f564,plain,
    ( spl4_53
    | spl4_54
    | ~ spl4_37
    | ~ spl4_16
    | ~ spl4_15
    | ~ spl4_41
    | ~ spl4_40 ),
    inference(avatar_split_clause,[],[f494,f469,f473,f227,f231,f445,f561,f557])).

fof(f469,plain,
    ( spl4_40
  <=> sK0 = k2_relset_1(sK1,sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).

fof(f494,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | k1_xboole_0 = sK0
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ spl4_40 ),
    inference(trivial_inequality_removal,[],[f492])).

fof(f492,plain,
    ( sK0 != sK0
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | k1_xboole_0 = sK0
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ spl4_40 ),
    inference(superposition,[],[f66,f471])).

fof(f471,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ spl4_40 ),
    inference(avatar_component_clause,[],[f469])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k1_xboole_0 = X1
      | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
            & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_2)).

fof(f501,plain,
    ( ~ spl4_15
    | spl4_43
    | ~ spl4_40 ),
    inference(avatar_split_clause,[],[f493,f469,f497,f227])).

fof(f493,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_40 ),
    inference(superposition,[],[f65,f471])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f489,plain,(
    spl4_41 ),
    inference(avatar_contradiction_clause,[],[f488])).

fof(f488,plain,
    ( $false
    | spl4_41 ),
    inference(subsumption_resolution,[],[f43,f475])).

fof(f475,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | spl4_41 ),
    inference(avatar_component_clause,[],[f473])).

fof(f43,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f476,plain,
    ( spl4_40
    | ~ spl4_16
    | ~ spl4_5
    | ~ spl4_21
    | ~ spl4_13
    | ~ spl4_15
    | ~ spl4_41 ),
    inference(avatar_split_clause,[],[f463,f473,f227,f214,f287,f127,f231,f469])).

fof(f463,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | sK0 = k2_relset_1(sK1,sK0,sK3) ),
    inference(resolution,[],[f68,f46])).

fof(f46,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X1,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_1(X2)
      | k2_relset_1(X0,X1,X2) = X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_relset_1(X0,X1,X2) = X1
          | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_relset_1(X0,X1,X2) = X1
          | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
           => k2_relset_1(X0,X1,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_funct_2)).

fof(f456,plain,
    ( spl4_36
    | ~ spl4_1
    | ~ spl4_37
    | ~ spl4_13
    | ~ spl4_3
    | ~ spl4_16
    | ~ spl4_38
    | ~ spl4_39
    | ~ spl4_6
    | ~ spl4_31 ),
    inference(avatar_split_clause,[],[f439,f385,f131,f453,f449,f231,f103,f214,f445,f94,f441])).

fof(f103,plain,
    ( spl4_3
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f385,plain,
    ( spl4_31
  <=> k6_partfun1(sK0) = k5_relat_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).

fof(f439,plain,
    ( sK1 != k1_relat_1(sK3)
    | k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | sK2 = k2_funct_1(sK3)
    | ~ spl4_6
    | ~ spl4_31 ),
    inference(forward_demodulation,[],[f437,f133])).

fof(f437,plain,
    ( k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK3)
    | k1_relat_1(sK3) != k2_relat_1(sK2)
    | ~ v1_relat_1(sK3)
    | sK2 = k2_funct_1(sK3)
    | ~ spl4_31 ),
    inference(superposition,[],[f85,f387])).

fof(f387,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ spl4_31 ),
    inference(avatar_component_clause,[],[f385])).

fof(f434,plain,(
    spl4_34 ),
    inference(avatar_contradiction_clause,[],[f429])).

fof(f429,plain,
    ( $false
    | spl4_34 ),
    inference(unit_resulting_resolution,[],[f64,f78,f417,f59])).

fof(f417,plain,
    ( ~ v1_relat_1(k6_partfun1(sK0))
    | spl4_34 ),
    inference(avatar_component_clause,[],[f415])).

fof(f415,plain,
    ( spl4_34
  <=> v1_relat_1(k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).

fof(f78,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f55,f54])).

fof(f55,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f10])).

% (29658)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
fof(f10,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

fof(f424,plain,
    ( spl4_35
    | ~ spl4_34
    | ~ spl4_32 ),
    inference(avatar_split_clause,[],[f404,f399,f415,f421])).

fof(f399,plain,
    ( spl4_32
  <=> v1_funct_1(k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f404,plain,
    ( ~ v1_relat_1(k6_partfun1(sK0))
    | v2_funct_1(k6_partfun1(sK0))
    | ~ spl4_32 ),
    inference(resolution,[],[f401,f150])).

fof(f150,plain,(
    ! [X1] :
      ( ~ v1_funct_1(k6_partfun1(X1))
      | ~ v1_relat_1(k6_partfun1(X1))
      | v2_funct_1(k6_partfun1(X1)) ) ),
    inference(trivial_inequality_removal,[],[f149])).

fof(f149,plain,(
    ! [X1] :
      ( k6_partfun1(X1) != k6_partfun1(X1)
      | ~ v1_funct_1(k6_partfun1(X1))
      | ~ v1_relat_1(k6_partfun1(X1))
      | v2_funct_1(k6_partfun1(X1)) ) ),
    inference(forward_demodulation,[],[f146,f80])).

fof(f80,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f56,f54])).

fof(f56,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f146,plain,(
    ! [X1] :
      ( k6_partfun1(X1) != k6_partfun1(k1_relat_1(k6_partfun1(X1)))
      | ~ v1_funct_1(k6_partfun1(X1))
      | ~ v1_relat_1(k6_partfun1(X1))
      | v2_funct_1(k6_partfun1(X1)) ) ),
    inference(duplicate_literal_removal,[],[f141])).

fof(f141,plain,(
    ! [X1] :
      ( k6_partfun1(X1) != k6_partfun1(k1_relat_1(k6_partfun1(X1)))
      | ~ v1_funct_1(k6_partfun1(X1))
      | ~ v1_relat_1(k6_partfun1(X1))
      | ~ v1_funct_1(k6_partfun1(X1))
      | ~ v1_relat_1(k6_partfun1(X1))
      | v2_funct_1(k6_partfun1(X1))
      | ~ v1_relat_1(k6_partfun1(X1)) ) ),
    inference(superposition,[],[f84,f115])).

fof(f115,plain,(
    ! [X0] :
      ( k6_partfun1(X0) = k5_relat_1(k6_partfun1(X0),k6_partfun1(X0))
      | ~ v1_relat_1(k6_partfun1(X0)) ) ),
    inference(superposition,[],[f81,f80])).

fof(f81,plain,(
    ! [X0] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f58,f54])).

fof(f58,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).

fof(f84,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X0)
      | v2_funct_1(X0) ) ),
    inference(definition_unfolding,[],[f62,f54])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1)
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | ! [X1] :
          ( k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | ! [X1] :
          ( k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( ? [X1] :
            ( k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,X1)
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
       => v2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_funct_1)).

fof(f401,plain,
    ( v1_funct_1(k6_partfun1(sK0))
    | ~ spl4_32 ),
    inference(avatar_component_clause,[],[f399])).

fof(f402,plain,
    ( ~ spl4_13
    | ~ spl4_15
    | ~ spl4_16
    | ~ spl4_5
    | spl4_32
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f395,f163,f399,f127,f231,f227,f214])).

fof(f395,plain,
    ( v1_funct_1(k6_partfun1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_8 ),
    inference(superposition,[],[f76,f165])).

fof(f76,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f41])).

% (29676)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% (29646)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% (29659)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
fof(f41,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f397,plain,
    ( ~ spl4_13
    | ~ spl4_15
    | ~ spl4_16
    | ~ spl4_5
    | spl4_31
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f394,f163,f385,f127,f231,f227,f214])).

fof(f394,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_8 ),
    inference(superposition,[],[f75,f165])).

fof(f75,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f340,plain,(
    ~ spl4_20 ),
    inference(avatar_contradiction_clause,[],[f329])).

fof(f329,plain,
    ( $false
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f49,f285])).

fof(f285,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f283])).

fof(f283,plain,
    ( spl4_20
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f49,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f20])).

fof(f302,plain,
    ( ~ spl4_3
    | ~ spl4_10
    | ~ spl4_13
    | spl4_22
    | ~ spl4_19 ),
    inference(avatar_split_clause,[],[f294,f279,f298,f214,f202,f103])).

fof(f202,plain,
    ( spl4_10
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f279,plain,
    ( spl4_19
  <=> k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f294,plain,
    ( k6_partfun1(sK0) = k6_partfun1(k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_19 ),
    inference(superposition,[],[f83,f281])).

fof(f281,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f279])).

fof(f292,plain,(
    spl4_21 ),
    inference(avatar_contradiction_clause,[],[f291])).

fof(f291,plain,
    ( $false
    | spl4_21 ),
    inference(subsumption_resolution,[],[f52,f289])).

fof(f289,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | spl4_21 ),
    inference(avatar_component_clause,[],[f287])).

fof(f52,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f290,plain,
    ( spl4_19
    | spl4_20
    | ~ spl4_10
    | ~ spl4_13
    | ~ spl4_5
    | ~ spl4_21 ),
    inference(avatar_split_clause,[],[f277,f287,f127,f214,f202,f283,f279])).

fof(f277,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k1_xboole_0 = sK1
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(trivial_inequality_removal,[],[f274])).

fof(f274,plain,
    ( sK1 != sK1
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k1_xboole_0 = sK1
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(superposition,[],[f66,f45])).

fof(f269,plain,(
    spl4_16 ),
    inference(avatar_contradiction_clause,[],[f268])).

fof(f268,plain,
    ( $false
    | spl4_16 ),
    inference(subsumption_resolution,[],[f42,f233])).

fof(f233,plain,
    ( ~ v1_funct_1(sK3)
    | spl4_16 ),
    inference(avatar_component_clause,[],[f231])).

fof(f42,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f20])).

fof(f267,plain,(
    spl4_15 ),
    inference(avatar_contradiction_clause,[],[f266])).

fof(f266,plain,
    ( $false
    | spl4_15 ),
    inference(subsumption_resolution,[],[f44,f229])).

fof(f229,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl4_15 ),
    inference(avatar_component_clause,[],[f227])).

fof(f44,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f20])).

fof(f265,plain,(
    spl4_7 ),
    inference(avatar_contradiction_clause,[],[f256])).

fof(f256,plain,
    ( $false
    | spl4_7 ),
    inference(unit_resulting_resolution,[],[f51,f42,f44,f53,f161,f77])).

fof(f77,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f161,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl4_7 ),
    inference(avatar_component_clause,[],[f159])).

fof(f159,plain,
    ( spl4_7
  <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f247,plain,(
    spl4_13 ),
    inference(avatar_contradiction_clause,[],[f246])).

fof(f246,plain,
    ( $false
    | spl4_13 ),
    inference(subsumption_resolution,[],[f51,f216])).

fof(f216,plain,
    ( ~ v1_funct_1(sK2)
    | spl4_13 ),
    inference(avatar_component_clause,[],[f214])).

fof(f245,plain,(
    spl4_10 ),
    inference(avatar_contradiction_clause,[],[f244])).

fof(f244,plain,
    ( $false
    | spl4_10 ),
    inference(subsumption_resolution,[],[f47,f204])).

fof(f204,plain,
    ( ~ v2_funct_1(sK2)
    | spl4_10 ),
    inference(avatar_component_clause,[],[f202])).

fof(f166,plain,
    ( ~ spl4_7
    | spl4_8 ),
    inference(avatar_split_clause,[],[f156,f163,f159])).

fof(f156,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
    | ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f152,f46])).

fof(f152,plain,(
    ! [X2,X1] :
      ( ~ r2_relset_1(X2,X2,X1,k6_partfun1(X2))
      | k6_partfun1(X2) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ) ),
    inference(resolution,[],[f74,f78])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f137,plain,(
    spl4_5 ),
    inference(avatar_contradiction_clause,[],[f136])).

fof(f136,plain,
    ( $false
    | spl4_5 ),
    inference(subsumption_resolution,[],[f53,f129])).

fof(f129,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl4_5 ),
    inference(avatar_component_clause,[],[f127])).

fof(f135,plain,
    ( ~ spl4_5
    | spl4_6 ),
    inference(avatar_split_clause,[],[f125,f131,f127])).

fof(f125,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f45,f65])).

fof(f119,plain,(
    spl4_4 ),
    inference(avatar_contradiction_clause,[],[f116])).

fof(f116,plain,
    ( $false
    | spl4_4 ),
    inference(unit_resulting_resolution,[],[f64,f109])).

fof(f109,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | spl4_4 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl4_4
  <=> v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f114,plain,(
    spl4_2 ),
    inference(avatar_contradiction_clause,[],[f111])).

fof(f111,plain,
    ( $false
    | spl4_2 ),
    inference(unit_resulting_resolution,[],[f64,f100])).

fof(f100,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | spl4_2 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl4_2
  <=> v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f110,plain,
    ( spl4_3
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f91,f107,f103])).

fof(f91,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK2) ),
    inference(resolution,[],[f59,f53])).

fof(f101,plain,
    ( spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f90,f98,f94])).

fof(f90,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | v1_relat_1(sK3) ),
    inference(resolution,[],[f59,f44])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:52:38 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.50  % (29661)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.51  % (29652)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (29651)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.52  % (29660)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.53  % (29649)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.35/0.54  % (29650)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.35/0.54  % (29663)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.35/0.54  % (29663)Refutation not found, incomplete strategy% (29663)------------------------------
% 1.35/0.54  % (29663)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.54  % (29663)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.54  
% 1.35/0.54  % (29663)Memory used [KB]: 10746
% 1.35/0.54  % (29663)Time elapsed: 0.126 s
% 1.35/0.54  % (29663)------------------------------
% 1.35/0.54  % (29663)------------------------------
% 1.35/0.54  % (29654)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.35/0.55  % (29675)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.35/0.55  % (29653)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.35/0.55  % (29673)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.35/0.55  % (29667)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.46/0.55  % (29664)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.46/0.55  % (29669)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.46/0.56  % (29660)Refutation found. Thanks to Tanya!
% 1.46/0.56  % SZS status Theorem for theBenchmark
% 1.46/0.56  % SZS output start Proof for theBenchmark
% 1.46/0.56  fof(f816,plain,(
% 1.46/0.56    $false),
% 1.46/0.56    inference(avatar_sat_refutation,[],[f101,f110,f114,f119,f135,f137,f166,f245,f247,f265,f267,f269,f290,f292,f302,f340,f397,f402,f424,f434,f456,f476,f489,f501,f564,f592,f679,f692,f722,f727,f760,f763,f778,f784,f789,f793,f801,f813])).
% 1.46/0.56  fof(f813,plain,(
% 1.46/0.56    ~spl4_36 | ~spl4_69),
% 1.46/0.56    inference(avatar_contradiction_clause,[],[f805])).
% 1.46/0.56  fof(f805,plain,(
% 1.46/0.56    $false | (~spl4_36 | ~spl4_69)),
% 1.46/0.56    inference(subsumption_resolution,[],[f50,f803])).
% 1.46/0.56  fof(f803,plain,(
% 1.46/0.56    sK3 = k2_funct_1(sK2) | (~spl4_36 | ~spl4_69)),
% 1.46/0.56    inference(forward_demodulation,[],[f705,f443])).
% 1.46/0.56  fof(f443,plain,(
% 1.46/0.56    sK2 = k2_funct_1(sK3) | ~spl4_36),
% 1.46/0.56    inference(avatar_component_clause,[],[f441])).
% 1.46/0.56  fof(f441,plain,(
% 1.46/0.56    spl4_36 <=> sK2 = k2_funct_1(sK3)),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).
% 1.46/0.56  fof(f705,plain,(
% 1.46/0.56    sK3 = k2_funct_1(k2_funct_1(sK3)) | ~spl4_69),
% 1.46/0.56    inference(avatar_component_clause,[],[f703])).
% 1.46/0.56  fof(f703,plain,(
% 1.46/0.56    spl4_69 <=> sK3 = k2_funct_1(k2_funct_1(sK3))),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_69])])).
% 1.46/0.56  fof(f50,plain,(
% 1.46/0.56    sK3 != k2_funct_1(sK2)),
% 1.46/0.56    inference(cnf_transformation,[],[f20])).
% 1.46/0.56  fof(f20,plain,(
% 1.46/0.56    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.46/0.56    inference(flattening,[],[f19])).
% 1.46/0.56  fof(f19,plain,(
% 1.46/0.56    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.46/0.56    inference(ennf_transformation,[],[f18])).
% 1.46/0.56  fof(f18,negated_conjecture,(
% 1.46/0.56    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.46/0.56    inference(negated_conjecture,[],[f17])).
% 1.46/0.56  fof(f17,conjecture,(
% 1.46/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.46/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).
% 1.46/0.56  fof(f801,plain,(
% 1.46/0.56    ~spl4_22 | ~spl4_36 | spl4_73),
% 1.46/0.56    inference(avatar_contradiction_clause,[],[f800])).
% 1.46/0.56  fof(f800,plain,(
% 1.46/0.56    $false | (~spl4_22 | ~spl4_36 | spl4_73)),
% 1.46/0.56    inference(subsumption_resolution,[],[f366,f795])).
% 1.46/0.56  fof(f795,plain,(
% 1.46/0.56    sK0 != k1_relat_1(sK2) | (~spl4_36 | spl4_73)),
% 1.46/0.56    inference(forward_demodulation,[],[f721,f443])).
% 1.46/0.56  fof(f721,plain,(
% 1.46/0.56    sK0 != k1_relat_1(k2_funct_1(sK3)) | spl4_73),
% 1.46/0.56    inference(avatar_component_clause,[],[f719])).
% 1.46/0.56  fof(f719,plain,(
% 1.46/0.56    spl4_73 <=> sK0 = k1_relat_1(k2_funct_1(sK3))),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_73])])).
% 1.46/0.56  fof(f366,plain,(
% 1.46/0.56    sK0 = k1_relat_1(sK2) | ~spl4_22),
% 1.46/0.56    inference(forward_demodulation,[],[f353,f79])).
% 1.46/0.56  fof(f79,plain,(
% 1.46/0.56    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 1.46/0.56    inference(definition_unfolding,[],[f57,f54])).
% 1.46/0.56  fof(f54,plain,(
% 1.46/0.56    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f13])).
% 1.46/0.56  fof(f13,axiom,(
% 1.46/0.56    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.46/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.46/0.56  fof(f57,plain,(
% 1.46/0.56    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 1.46/0.56    inference(cnf_transformation,[],[f3])).
% 1.46/0.56  fof(f3,axiom,(
% 1.46/0.56    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.46/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 1.46/0.56  fof(f353,plain,(
% 1.46/0.56    k1_relat_1(sK2) = k2_relat_1(k6_partfun1(sK0)) | ~spl4_22),
% 1.46/0.56    inference(superposition,[],[f79,f300])).
% 1.46/0.56  fof(f300,plain,(
% 1.46/0.56    k6_partfun1(sK0) = k6_partfun1(k1_relat_1(sK2)) | ~spl4_22),
% 1.46/0.56    inference(avatar_component_clause,[],[f298])).
% 1.46/0.56  fof(f298,plain,(
% 1.46/0.56    spl4_22 <=> k6_partfun1(sK0) = k6_partfun1(k1_relat_1(sK2))),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 1.46/0.56  fof(f793,plain,(
% 1.46/0.56    ~spl4_6 | ~spl4_36 | spl4_72),
% 1.46/0.56    inference(avatar_contradiction_clause,[],[f792])).
% 1.46/0.56  fof(f792,plain,(
% 1.46/0.56    $false | (~spl4_6 | ~spl4_36 | spl4_72)),
% 1.46/0.56    inference(trivial_inequality_removal,[],[f791])).
% 1.46/0.56  fof(f791,plain,(
% 1.46/0.56    k6_partfun1(sK1) != k6_partfun1(sK1) | (~spl4_6 | ~spl4_36 | spl4_72)),
% 1.46/0.56    inference(forward_demodulation,[],[f790,f133])).
% 1.46/0.56  fof(f133,plain,(
% 1.46/0.56    sK1 = k2_relat_1(sK2) | ~spl4_6),
% 1.46/0.56    inference(avatar_component_clause,[],[f131])).
% 1.46/0.56  fof(f131,plain,(
% 1.46/0.56    spl4_6 <=> sK1 = k2_relat_1(sK2)),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.46/0.56  fof(f790,plain,(
% 1.46/0.56    k6_partfun1(k2_relat_1(sK2)) != k6_partfun1(sK1) | (~spl4_36 | spl4_72)),
% 1.46/0.56    inference(forward_demodulation,[],[f717,f443])).
% 1.46/0.56  fof(f717,plain,(
% 1.46/0.56    k6_partfun1(sK1) != k6_partfun1(k2_relat_1(k2_funct_1(sK3))) | spl4_72),
% 1.46/0.56    inference(avatar_component_clause,[],[f715])).
% 1.46/0.56  fof(f715,plain,(
% 1.46/0.56    spl4_72 <=> k6_partfun1(sK1) = k6_partfun1(k2_relat_1(k2_funct_1(sK3)))),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_72])])).
% 1.46/0.56  fof(f789,plain,(
% 1.46/0.56    ~spl4_36 | spl4_71),
% 1.46/0.56    inference(avatar_contradiction_clause,[],[f788])).
% 1.46/0.56  fof(f788,plain,(
% 1.46/0.56    $false | (~spl4_36 | spl4_71)),
% 1.46/0.56    inference(subsumption_resolution,[],[f47,f786])).
% 1.46/0.56  fof(f786,plain,(
% 1.46/0.56    ~v2_funct_1(sK2) | (~spl4_36 | spl4_71)),
% 1.46/0.56    inference(forward_demodulation,[],[f713,f443])).
% 1.46/0.56  fof(f713,plain,(
% 1.46/0.56    ~v2_funct_1(k2_funct_1(sK3)) | spl4_71),
% 1.46/0.56    inference(avatar_component_clause,[],[f711])).
% 1.46/0.56  fof(f711,plain,(
% 1.46/0.56    spl4_71 <=> v2_funct_1(k2_funct_1(sK3))),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_71])])).
% 1.46/0.56  fof(f47,plain,(
% 1.46/0.56    v2_funct_1(sK2)),
% 1.46/0.56    inference(cnf_transformation,[],[f20])).
% 1.46/0.56  fof(f784,plain,(
% 1.46/0.56    ~spl4_36 | spl4_70),
% 1.46/0.56    inference(avatar_contradiction_clause,[],[f783])).
% 1.46/0.56  fof(f783,plain,(
% 1.46/0.56    $false | (~spl4_36 | spl4_70)),
% 1.46/0.56    inference(unit_resulting_resolution,[],[f64,f53,f779,f59])).
% 1.46/0.56  fof(f59,plain,(
% 1.46/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f22])).
% 1.46/0.56  fof(f22,plain,(
% 1.46/0.56    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.46/0.56    inference(ennf_transformation,[],[f1])).
% 1.46/0.56  fof(f1,axiom,(
% 1.46/0.56    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.46/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.46/0.56  fof(f779,plain,(
% 1.46/0.56    ~v1_relat_1(sK2) | (~spl4_36 | spl4_70)),
% 1.46/0.56    inference(forward_demodulation,[],[f709,f443])).
% 1.46/0.56  fof(f709,plain,(
% 1.46/0.56    ~v1_relat_1(k2_funct_1(sK3)) | spl4_70),
% 1.46/0.56    inference(avatar_component_clause,[],[f707])).
% 1.46/0.56  fof(f707,plain,(
% 1.46/0.56    spl4_70 <=> v1_relat_1(k2_funct_1(sK3))),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_70])])).
% 1.46/0.56  fof(f53,plain,(
% 1.46/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.46/0.56    inference(cnf_transformation,[],[f20])).
% 1.46/0.56  fof(f64,plain,(
% 1.46/0.56    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.46/0.56    inference(cnf_transformation,[],[f2])).
% 1.46/0.56  fof(f2,axiom,(
% 1.46/0.56    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.46/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.46/0.56  fof(f778,plain,(
% 1.46/0.56    ~spl4_36 | spl4_67),
% 1.46/0.56    inference(avatar_contradiction_clause,[],[f777])).
% 1.46/0.56  fof(f777,plain,(
% 1.46/0.56    $false | (~spl4_36 | spl4_67)),
% 1.46/0.56    inference(subsumption_resolution,[],[f51,f765])).
% 1.46/0.56  fof(f765,plain,(
% 1.46/0.56    ~v1_funct_1(sK2) | (~spl4_36 | spl4_67)),
% 1.46/0.56    inference(superposition,[],[f696,f443])).
% 1.46/0.56  fof(f696,plain,(
% 1.46/0.56    ~v1_funct_1(k2_funct_1(sK3)) | spl4_67),
% 1.46/0.56    inference(avatar_component_clause,[],[f694])).
% 1.46/0.56  fof(f694,plain,(
% 1.46/0.56    spl4_67 <=> v1_funct_1(k2_funct_1(sK3))),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_67])])).
% 1.46/0.56  fof(f51,plain,(
% 1.46/0.56    v1_funct_1(sK2)),
% 1.46/0.56    inference(cnf_transformation,[],[f20])).
% 1.46/0.56  fof(f763,plain,(
% 1.46/0.56    spl4_38 | ~spl4_43),
% 1.46/0.56    inference(avatar_contradiction_clause,[],[f762])).
% 1.46/0.56  fof(f762,plain,(
% 1.46/0.56    $false | (spl4_38 | ~spl4_43)),
% 1.46/0.56    inference(trivial_inequality_removal,[],[f761])).
% 1.46/0.56  fof(f761,plain,(
% 1.46/0.56    k6_partfun1(sK0) != k6_partfun1(sK0) | (spl4_38 | ~spl4_43)),
% 1.46/0.56    inference(forward_demodulation,[],[f451,f499])).
% 1.46/0.56  fof(f499,plain,(
% 1.46/0.56    sK0 = k2_relat_1(sK3) | ~spl4_43),
% 1.46/0.56    inference(avatar_component_clause,[],[f497])).
% 1.46/0.56  fof(f497,plain,(
% 1.46/0.56    spl4_43 <=> sK0 = k2_relat_1(sK3)),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).
% 1.46/0.56  fof(f451,plain,(
% 1.46/0.56    k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3)) | spl4_38),
% 1.46/0.56    inference(avatar_component_clause,[],[f449])).
% 1.46/0.56  fof(f449,plain,(
% 1.46/0.56    spl4_38 <=> k6_partfun1(sK0) = k6_partfun1(k2_relat_1(sK3))),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).
% 1.46/0.56  fof(f760,plain,(
% 1.46/0.56    spl4_39 | ~spl4_66),
% 1.46/0.56    inference(avatar_contradiction_clause,[],[f757])).
% 1.46/0.56  fof(f757,plain,(
% 1.46/0.56    $false | (spl4_39 | ~spl4_66)),
% 1.46/0.56    inference(subsumption_resolution,[],[f455,f755])).
% 1.46/0.56  fof(f755,plain,(
% 1.46/0.56    sK1 = k1_relat_1(sK3) | ~spl4_66),
% 1.46/0.56    inference(forward_demodulation,[],[f736,f79])).
% 1.46/0.56  fof(f736,plain,(
% 1.46/0.56    k1_relat_1(sK3) = k2_relat_1(k6_partfun1(sK1)) | ~spl4_66),
% 1.46/0.56    inference(superposition,[],[f79,f690])).
% 1.46/0.56  fof(f690,plain,(
% 1.46/0.56    k6_partfun1(k1_relat_1(sK3)) = k6_partfun1(sK1) | ~spl4_66),
% 1.46/0.56    inference(avatar_component_clause,[],[f688])).
% 1.46/0.56  fof(f688,plain,(
% 1.46/0.56    spl4_66 <=> k6_partfun1(k1_relat_1(sK3)) = k6_partfun1(sK1)),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_66])])).
% 1.46/0.56  fof(f455,plain,(
% 1.46/0.56    sK1 != k1_relat_1(sK3) | spl4_39),
% 1.46/0.56    inference(avatar_component_clause,[],[f453])).
% 1.46/0.56  fof(f453,plain,(
% 1.46/0.56    spl4_39 <=> sK1 = k1_relat_1(sK3)),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).
% 1.46/0.56  fof(f727,plain,(
% 1.46/0.56    ~spl4_41 | ~spl4_15 | ~spl4_16 | spl4_54 | spl4_37 | ~spl4_35 | ~spl4_8 | ~spl4_57),
% 1.46/0.56    inference(avatar_split_clause,[],[f724,f590,f163,f421,f445,f561,f231,f227,f473])).
% 1.46/0.56  fof(f473,plain,(
% 1.46/0.56    spl4_41 <=> v1_funct_2(sK3,sK1,sK0)),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).
% 1.46/0.56  fof(f227,plain,(
% 1.46/0.56    spl4_15 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 1.46/0.56  fof(f231,plain,(
% 1.46/0.56    spl4_16 <=> v1_funct_1(sK3)),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 1.46/0.56  fof(f561,plain,(
% 1.46/0.56    spl4_54 <=> k1_xboole_0 = sK0),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_54])])).
% 1.46/0.56  fof(f445,plain,(
% 1.46/0.56    spl4_37 <=> v2_funct_1(sK3)),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).
% 1.46/0.56  fof(f421,plain,(
% 1.46/0.56    spl4_35 <=> v2_funct_1(k6_partfun1(sK0))),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).
% 1.46/0.56  fof(f163,plain,(
% 1.46/0.56    spl4_8 <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 1.46/0.56  fof(f590,plain,(
% 1.46/0.56    spl4_57 <=> ! [X1,X0] : (~v1_funct_1(X0) | v2_funct_1(X0) | k1_xboole_0 = X1 | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X1,sK2,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) | ~v1_funct_2(X0,sK1,X1))),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_57])])).
% 1.46/0.56  fof(f724,plain,(
% 1.46/0.56    ~v2_funct_1(k6_partfun1(sK0)) | v2_funct_1(sK3) | k1_xboole_0 = sK0 | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | (~spl4_8 | ~spl4_57)),
% 1.46/0.56    inference(superposition,[],[f591,f165])).
% 1.46/0.56  fof(f165,plain,(
% 1.46/0.56    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) | ~spl4_8),
% 1.46/0.56    inference(avatar_component_clause,[],[f163])).
% 1.46/0.56  fof(f591,plain,(
% 1.46/0.56    ( ! [X0,X1] : (~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X1,sK2,X0)) | v2_funct_1(X0) | k1_xboole_0 = X1 | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) | ~v1_funct_2(X0,sK1,X1)) ) | ~spl4_57),
% 1.46/0.56    inference(avatar_component_clause,[],[f590])).
% 1.46/0.56  fof(f722,plain,(
% 1.46/0.56    spl4_69 | ~spl4_70 | ~spl4_71 | ~spl4_16 | ~spl4_1 | ~spl4_67 | ~spl4_72 | ~spl4_73 | ~spl4_43 | ~spl4_53),
% 1.46/0.56    inference(avatar_split_clause,[],[f701,f557,f497,f719,f715,f694,f94,f231,f711,f707,f703])).
% 1.46/0.56  fof(f94,plain,(
% 1.46/0.56    spl4_1 <=> v1_relat_1(sK3)),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.46/0.56  fof(f557,plain,(
% 1.46/0.56    spl4_53 <=> k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_53])])).
% 1.46/0.56  fof(f701,plain,(
% 1.46/0.56    sK0 != k1_relat_1(k2_funct_1(sK3)) | k6_partfun1(sK1) != k6_partfun1(k2_relat_1(k2_funct_1(sK3))) | ~v1_funct_1(k2_funct_1(sK3)) | ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v2_funct_1(k2_funct_1(sK3)) | ~v1_relat_1(k2_funct_1(sK3)) | sK3 = k2_funct_1(k2_funct_1(sK3)) | (~spl4_43 | ~spl4_53)),
% 1.46/0.56    inference(forward_demodulation,[],[f685,f499])).
% 1.46/0.56  fof(f685,plain,(
% 1.46/0.56    k6_partfun1(sK1) != k6_partfun1(k2_relat_1(k2_funct_1(sK3))) | ~v1_funct_1(k2_funct_1(sK3)) | ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v2_funct_1(k2_funct_1(sK3)) | k2_relat_1(sK3) != k1_relat_1(k2_funct_1(sK3)) | ~v1_relat_1(k2_funct_1(sK3)) | sK3 = k2_funct_1(k2_funct_1(sK3)) | ~spl4_53),
% 1.46/0.56    inference(superposition,[],[f85,f559])).
% 1.46/0.56  fof(f559,plain,(
% 1.46/0.56    k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~spl4_53),
% 1.46/0.56    inference(avatar_component_clause,[],[f557])).
% 1.46/0.56  fof(f85,plain,(
% 1.46/0.56    ( ! [X0,X1] : (k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v1_relat_1(X0) | k2_funct_1(X0) = X1) )),
% 1.46/0.56    inference(definition_unfolding,[],[f63,f54])).
% 1.46/0.56  fof(f63,plain,(
% 1.46/0.56    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(X0) | k1_relat_1(X0) != k2_relat_1(X1) | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k2_funct_1(X0) = X1) )),
% 1.46/0.56    inference(cnf_transformation,[],[f28])).
% 1.46/0.56  fof(f28,plain,(
% 1.46/0.56    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.46/0.56    inference(flattening,[],[f27])).
% 1.46/0.56  fof(f27,plain,(
% 1.46/0.56    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.46/0.56    inference(ennf_transformation,[],[f7])).
% 1.46/0.56  fof(f7,axiom,(
% 1.46/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 1.46/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_1)).
% 1.46/0.56  fof(f692,plain,(
% 1.46/0.56    ~spl4_1 | ~spl4_37 | ~spl4_16 | spl4_66 | ~spl4_53),
% 1.46/0.56    inference(avatar_split_clause,[],[f683,f557,f688,f231,f445,f94])).
% 1.46/0.56  fof(f683,plain,(
% 1.46/0.56    k6_partfun1(k1_relat_1(sK3)) = k6_partfun1(sK1) | ~v1_funct_1(sK3) | ~v2_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl4_53),
% 1.46/0.56    inference(superposition,[],[f83,f559])).
% 1.46/0.56  fof(f83,plain,(
% 1.46/0.56    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.46/0.56    inference(definition_unfolding,[],[f60,f54])).
% 1.46/0.56  fof(f60,plain,(
% 1.46/0.56    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) )),
% 1.46/0.56    inference(cnf_transformation,[],[f24])).
% 1.46/0.56  fof(f24,plain,(
% 1.46/0.56    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.46/0.56    inference(flattening,[],[f23])).
% 1.46/0.56  fof(f23,plain,(
% 1.46/0.56    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.46/0.56    inference(ennf_transformation,[],[f6])).
% 1.46/0.56  fof(f6,axiom,(
% 1.46/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)))))),
% 1.46/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).
% 1.46/0.56  fof(f679,plain,(
% 1.46/0.56    ~spl4_54),
% 1.46/0.56    inference(avatar_contradiction_clause,[],[f662])).
% 1.46/0.56  fof(f662,plain,(
% 1.46/0.56    $false | ~spl4_54),
% 1.46/0.56    inference(subsumption_resolution,[],[f48,f563])).
% 1.46/0.56  fof(f563,plain,(
% 1.46/0.56    k1_xboole_0 = sK0 | ~spl4_54),
% 1.46/0.56    inference(avatar_component_clause,[],[f561])).
% 1.46/0.56  fof(f48,plain,(
% 1.46/0.56    k1_xboole_0 != sK0),
% 1.46/0.56    inference(cnf_transformation,[],[f20])).
% 1.46/0.56  fof(f592,plain,(
% 1.46/0.56    ~spl4_13 | spl4_57 | ~spl4_5 | ~spl4_21),
% 1.46/0.56    inference(avatar_split_clause,[],[f588,f287,f127,f590,f214])).
% 1.46/0.56  fof(f214,plain,(
% 1.46/0.56    spl4_13 <=> v1_funct_1(sK2)),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 1.46/0.56  fof(f127,plain,(
% 1.46/0.56    spl4_5 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.46/0.56  fof(f287,plain,(
% 1.46/0.56    spl4_21 <=> v1_funct_2(sK2,sK0,sK1)),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 1.46/0.56  fof(f588,plain,(
% 1.46/0.56    ( ! [X0,X1] : (~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(X0) | ~v1_funct_2(X0,sK1,X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X1,sK2,X0)) | ~v1_funct_1(sK2) | k1_xboole_0 = X1 | v2_funct_1(X0)) )),
% 1.46/0.56    inference(trivial_inequality_removal,[],[f583])).
% 1.46/0.56  fof(f583,plain,(
% 1.46/0.56    ( ! [X0,X1] : (sK1 != sK1 | ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(X0) | ~v1_funct_2(X0,sK1,X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X1,sK2,X0)) | ~v1_funct_1(sK2) | k1_xboole_0 = X1 | v2_funct_1(X0)) )),
% 1.46/0.56    inference(superposition,[],[f72,f45])).
% 1.46/0.56  fof(f45,plain,(
% 1.46/0.56    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 1.46/0.56    inference(cnf_transformation,[],[f20])).
% 1.46/0.56  fof(f72,plain,(
% 1.46/0.56    ( ! [X4,X2,X0,X3,X1] : (k2_relset_1(X0,X1,X3) != X1 | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X1,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~v1_funct_1(X3) | k1_xboole_0 = X2 | v2_funct_1(X4)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f35])).
% 1.46/0.56  fof(f35,plain,(
% 1.46/0.56    ! [X0,X1,X2,X3] : (! [X4] : ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.46/0.56    inference(flattening,[],[f34])).
% 1.46/0.56  fof(f34,plain,(
% 1.46/0.56    ! [X0,X1,X2,X3] : (! [X4] : ((((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | (k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.46/0.56    inference(ennf_transformation,[],[f15])).
% 1.46/0.56  fof(f15,axiom,(
% 1.46/0.56    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) => ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 1.46/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_funct_2)).
% 1.46/0.56  fof(f564,plain,(
% 1.46/0.56    spl4_53 | spl4_54 | ~spl4_37 | ~spl4_16 | ~spl4_15 | ~spl4_41 | ~spl4_40),
% 1.46/0.56    inference(avatar_split_clause,[],[f494,f469,f473,f227,f231,f445,f561,f557])).
% 1.46/0.56  fof(f469,plain,(
% 1.46/0.56    spl4_40 <=> sK0 = k2_relset_1(sK1,sK0,sK3)),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).
% 1.46/0.56  fof(f494,plain,(
% 1.46/0.56    ~v1_funct_2(sK3,sK1,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~v2_funct_1(sK3) | k1_xboole_0 = sK0 | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~spl4_40),
% 1.46/0.56    inference(trivial_inequality_removal,[],[f492])).
% 1.46/0.56  fof(f492,plain,(
% 1.46/0.56    sK0 != sK0 | ~v1_funct_2(sK3,sK1,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~v2_funct_1(sK3) | k1_xboole_0 = sK0 | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~spl4_40),
% 1.46/0.56    inference(superposition,[],[f66,f471])).
% 1.46/0.56  fof(f471,plain,(
% 1.46/0.56    sK0 = k2_relset_1(sK1,sK0,sK3) | ~spl4_40),
% 1.46/0.56    inference(avatar_component_clause,[],[f469])).
% 1.46/0.56  fof(f66,plain,(
% 1.46/0.56    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v2_funct_1(X2) | k1_xboole_0 = X1 | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) )),
% 1.46/0.56    inference(cnf_transformation,[],[f31])).
% 1.46/0.56  fof(f31,plain,(
% 1.46/0.56    ! [X0,X1,X2] : ((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.46/0.56    inference(flattening,[],[f30])).
% 1.46/0.56  fof(f30,plain,(
% 1.46/0.56    ! [X0,X1,X2] : ((((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.46/0.56    inference(ennf_transformation,[],[f16])).
% 1.46/0.56  fof(f16,axiom,(
% 1.46/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1)))),
% 1.46/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_2)).
% 1.46/0.56  fof(f501,plain,(
% 1.46/0.56    ~spl4_15 | spl4_43 | ~spl4_40),
% 1.46/0.56    inference(avatar_split_clause,[],[f493,f469,f497,f227])).
% 1.46/0.56  fof(f493,plain,(
% 1.46/0.56    sK0 = k2_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_40),
% 1.46/0.56    inference(superposition,[],[f65,f471])).
% 1.46/0.56  fof(f65,plain,(
% 1.46/0.56    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.46/0.56    inference(cnf_transformation,[],[f29])).
% 1.46/0.56  fof(f29,plain,(
% 1.46/0.56    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.46/0.56    inference(ennf_transformation,[],[f8])).
% 1.46/0.56  fof(f8,axiom,(
% 1.46/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.46/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.46/0.56  fof(f489,plain,(
% 1.46/0.56    spl4_41),
% 1.46/0.56    inference(avatar_contradiction_clause,[],[f488])).
% 1.46/0.56  fof(f488,plain,(
% 1.46/0.56    $false | spl4_41),
% 1.46/0.56    inference(subsumption_resolution,[],[f43,f475])).
% 1.46/0.56  fof(f475,plain,(
% 1.46/0.56    ~v1_funct_2(sK3,sK1,sK0) | spl4_41),
% 1.46/0.56    inference(avatar_component_clause,[],[f473])).
% 1.46/0.56  fof(f43,plain,(
% 1.46/0.56    v1_funct_2(sK3,sK1,sK0)),
% 1.46/0.56    inference(cnf_transformation,[],[f20])).
% 1.46/0.56  fof(f476,plain,(
% 1.46/0.56    spl4_40 | ~spl4_16 | ~spl4_5 | ~spl4_21 | ~spl4_13 | ~spl4_15 | ~spl4_41),
% 1.46/0.56    inference(avatar_split_clause,[],[f463,f473,f227,f214,f287,f127,f231,f469])).
% 1.46/0.56  fof(f463,plain,(
% 1.46/0.56    ~v1_funct_2(sK3,sK1,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | sK0 = k2_relset_1(sK1,sK0,sK3)),
% 1.46/0.56    inference(resolution,[],[f68,f46])).
% 1.46/0.56  fof(f46,plain,(
% 1.46/0.56    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 1.46/0.56    inference(cnf_transformation,[],[f20])).
% 1.46/0.56  fof(f68,plain,(
% 1.46/0.56    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_1(X2) | k2_relset_1(X0,X1,X2) = X1) )),
% 1.46/0.56    inference(cnf_transformation,[],[f33])).
% 1.46/0.56  fof(f33,plain,(
% 1.46/0.56    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.46/0.56    inference(flattening,[],[f32])).
% 1.46/0.56  fof(f32,plain,(
% 1.46/0.56    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.46/0.56    inference(ennf_transformation,[],[f14])).
% 1.46/0.56  fof(f14,axiom,(
% 1.46/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 1.46/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_funct_2)).
% 1.46/0.56  fof(f456,plain,(
% 1.46/0.56    spl4_36 | ~spl4_1 | ~spl4_37 | ~spl4_13 | ~spl4_3 | ~spl4_16 | ~spl4_38 | ~spl4_39 | ~spl4_6 | ~spl4_31),
% 1.46/0.56    inference(avatar_split_clause,[],[f439,f385,f131,f453,f449,f231,f103,f214,f445,f94,f441])).
% 1.46/0.56  fof(f103,plain,(
% 1.46/0.56    spl4_3 <=> v1_relat_1(sK2)),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.46/0.56  fof(f385,plain,(
% 1.46/0.56    spl4_31 <=> k6_partfun1(sK0) = k5_relat_1(sK2,sK3)),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).
% 1.46/0.56  fof(f439,plain,(
% 1.46/0.56    sK1 != k1_relat_1(sK3) | k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v2_funct_1(sK3) | ~v1_relat_1(sK3) | sK2 = k2_funct_1(sK3) | (~spl4_6 | ~spl4_31)),
% 1.46/0.56    inference(forward_demodulation,[],[f437,f133])).
% 1.46/0.56  fof(f437,plain,(
% 1.46/0.56    k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v2_funct_1(sK3) | k1_relat_1(sK3) != k2_relat_1(sK2) | ~v1_relat_1(sK3) | sK2 = k2_funct_1(sK3) | ~spl4_31),
% 1.46/0.56    inference(superposition,[],[f85,f387])).
% 1.46/0.56  fof(f387,plain,(
% 1.46/0.56    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~spl4_31),
% 1.46/0.56    inference(avatar_component_clause,[],[f385])).
% 1.46/0.56  fof(f434,plain,(
% 1.46/0.56    spl4_34),
% 1.46/0.56    inference(avatar_contradiction_clause,[],[f429])).
% 1.46/0.56  fof(f429,plain,(
% 1.46/0.56    $false | spl4_34),
% 1.46/0.56    inference(unit_resulting_resolution,[],[f64,f78,f417,f59])).
% 1.46/0.56  fof(f417,plain,(
% 1.46/0.56    ~v1_relat_1(k6_partfun1(sK0)) | spl4_34),
% 1.46/0.56    inference(avatar_component_clause,[],[f415])).
% 1.46/0.56  fof(f415,plain,(
% 1.46/0.56    spl4_34 <=> v1_relat_1(k6_partfun1(sK0))),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).
% 1.46/0.56  fof(f78,plain,(
% 1.46/0.56    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.46/0.56    inference(definition_unfolding,[],[f55,f54])).
% 1.46/0.56  fof(f55,plain,(
% 1.46/0.56    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.46/0.56    inference(cnf_transformation,[],[f10])).
% 1.46/0.56  % (29658)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.46/0.56  fof(f10,axiom,(
% 1.46/0.56    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 1.46/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).
% 1.46/0.56  fof(f424,plain,(
% 1.46/0.56    spl4_35 | ~spl4_34 | ~spl4_32),
% 1.46/0.56    inference(avatar_split_clause,[],[f404,f399,f415,f421])).
% 1.46/0.56  fof(f399,plain,(
% 1.46/0.56    spl4_32 <=> v1_funct_1(k6_partfun1(sK0))),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).
% 1.46/0.56  fof(f404,plain,(
% 1.46/0.56    ~v1_relat_1(k6_partfun1(sK0)) | v2_funct_1(k6_partfun1(sK0)) | ~spl4_32),
% 1.46/0.56    inference(resolution,[],[f401,f150])).
% 1.46/0.56  fof(f150,plain,(
% 1.46/0.56    ( ! [X1] : (~v1_funct_1(k6_partfun1(X1)) | ~v1_relat_1(k6_partfun1(X1)) | v2_funct_1(k6_partfun1(X1))) )),
% 1.46/0.56    inference(trivial_inequality_removal,[],[f149])).
% 1.46/0.56  fof(f149,plain,(
% 1.46/0.56    ( ! [X1] : (k6_partfun1(X1) != k6_partfun1(X1) | ~v1_funct_1(k6_partfun1(X1)) | ~v1_relat_1(k6_partfun1(X1)) | v2_funct_1(k6_partfun1(X1))) )),
% 1.46/0.56    inference(forward_demodulation,[],[f146,f80])).
% 1.46/0.56  fof(f80,plain,(
% 1.46/0.56    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 1.46/0.56    inference(definition_unfolding,[],[f56,f54])).
% 1.46/0.56  fof(f56,plain,(
% 1.46/0.56    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.46/0.56    inference(cnf_transformation,[],[f3])).
% 1.46/0.56  fof(f146,plain,(
% 1.46/0.56    ( ! [X1] : (k6_partfun1(X1) != k6_partfun1(k1_relat_1(k6_partfun1(X1))) | ~v1_funct_1(k6_partfun1(X1)) | ~v1_relat_1(k6_partfun1(X1)) | v2_funct_1(k6_partfun1(X1))) )),
% 1.46/0.56    inference(duplicate_literal_removal,[],[f141])).
% 1.46/0.56  fof(f141,plain,(
% 1.46/0.56    ( ! [X1] : (k6_partfun1(X1) != k6_partfun1(k1_relat_1(k6_partfun1(X1))) | ~v1_funct_1(k6_partfun1(X1)) | ~v1_relat_1(k6_partfun1(X1)) | ~v1_funct_1(k6_partfun1(X1)) | ~v1_relat_1(k6_partfun1(X1)) | v2_funct_1(k6_partfun1(X1)) | ~v1_relat_1(k6_partfun1(X1))) )),
% 1.46/0.56    inference(superposition,[],[f84,f115])).
% 1.46/0.56  fof(f115,plain,(
% 1.46/0.56    ( ! [X0] : (k6_partfun1(X0) = k5_relat_1(k6_partfun1(X0),k6_partfun1(X0)) | ~v1_relat_1(k6_partfun1(X0))) )),
% 1.46/0.56    inference(superposition,[],[f81,f80])).
% 1.46/0.56  fof(f81,plain,(
% 1.46/0.56    ( ! [X0] : (k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0)) )),
% 1.46/0.56    inference(definition_unfolding,[],[f58,f54])).
% 1.46/0.56  fof(f58,plain,(
% 1.46/0.56    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0) )),
% 1.46/0.56    inference(cnf_transformation,[],[f21])).
% 1.46/0.56  fof(f21,plain,(
% 1.46/0.56    ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0))),
% 1.46/0.56    inference(ennf_transformation,[],[f4])).
% 1.46/0.56  fof(f4,axiom,(
% 1.46/0.56    ! [X0] : (v1_relat_1(X0) => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0)),
% 1.46/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).
% 1.46/0.56  fof(f84,plain,(
% 1.46/0.56    ( ! [X0,X1] : (k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X0) | v2_funct_1(X0)) )),
% 1.46/0.56    inference(definition_unfolding,[],[f62,f54])).
% 1.46/0.56  fof(f62,plain,(
% 1.46/0.56    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1) | v2_funct_1(X0)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f26])).
% 1.46/0.56  fof(f26,plain,(
% 1.46/0.56    ! [X0] : (v2_funct_1(X0) | ! [X1] : (k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.46/0.56    inference(flattening,[],[f25])).
% 1.46/0.56  fof(f25,plain,(
% 1.46/0.56    ! [X0] : ((v2_funct_1(X0) | ! [X1] : (k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.46/0.56    inference(ennf_transformation,[],[f5])).
% 1.46/0.56  fof(f5,axiom,(
% 1.46/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,X1) & v1_funct_1(X1) & v1_relat_1(X1)) => v2_funct_1(X0)))),
% 1.46/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_funct_1)).
% 1.46/0.56  fof(f401,plain,(
% 1.46/0.56    v1_funct_1(k6_partfun1(sK0)) | ~spl4_32),
% 1.46/0.56    inference(avatar_component_clause,[],[f399])).
% 1.46/0.56  fof(f402,plain,(
% 1.46/0.56    ~spl4_13 | ~spl4_15 | ~spl4_16 | ~spl4_5 | spl4_32 | ~spl4_8),
% 1.46/0.56    inference(avatar_split_clause,[],[f395,f163,f399,f127,f231,f227,f214])).
% 1.46/0.56  fof(f395,plain,(
% 1.46/0.56    v1_funct_1(k6_partfun1(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK2) | ~spl4_8),
% 1.46/0.56    inference(superposition,[],[f76,f165])).
% 1.46/0.56  fof(f76,plain,(
% 1.46/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X4)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f41])).
% 1.46/0.56  % (29676)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.46/0.56  % (29646)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.46/0.56  % (29659)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.46/0.56  fof(f41,plain,(
% 1.46/0.56    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.46/0.56    inference(flattening,[],[f40])).
% 1.46/0.56  fof(f40,plain,(
% 1.46/0.56    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.46/0.56    inference(ennf_transformation,[],[f11])).
% 1.46/0.56  fof(f11,axiom,(
% 1.46/0.56    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 1.46/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 1.46/0.56  fof(f397,plain,(
% 1.46/0.56    ~spl4_13 | ~spl4_15 | ~spl4_16 | ~spl4_5 | spl4_31 | ~spl4_8),
% 1.46/0.56    inference(avatar_split_clause,[],[f394,f163,f385,f127,f231,f227,f214])).
% 1.46/0.56  fof(f394,plain,(
% 1.46/0.56    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK2) | ~spl4_8),
% 1.46/0.56    inference(superposition,[],[f75,f165])).
% 1.46/0.56  fof(f75,plain,(
% 1.46/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X4)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f39])).
% 1.46/0.56  fof(f39,plain,(
% 1.46/0.56    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.46/0.56    inference(flattening,[],[f38])).
% 1.46/0.56  fof(f38,plain,(
% 1.46/0.56    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.46/0.56    inference(ennf_transformation,[],[f12])).
% 1.46/0.56  fof(f12,axiom,(
% 1.46/0.56    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.46/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 1.46/0.56  fof(f340,plain,(
% 1.46/0.56    ~spl4_20),
% 1.46/0.56    inference(avatar_contradiction_clause,[],[f329])).
% 1.46/0.56  fof(f329,plain,(
% 1.46/0.56    $false | ~spl4_20),
% 1.46/0.56    inference(subsumption_resolution,[],[f49,f285])).
% 1.46/0.56  fof(f285,plain,(
% 1.46/0.56    k1_xboole_0 = sK1 | ~spl4_20),
% 1.46/0.56    inference(avatar_component_clause,[],[f283])).
% 1.46/0.56  fof(f283,plain,(
% 1.46/0.56    spl4_20 <=> k1_xboole_0 = sK1),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 1.46/0.56  fof(f49,plain,(
% 1.46/0.56    k1_xboole_0 != sK1),
% 1.46/0.56    inference(cnf_transformation,[],[f20])).
% 1.46/0.56  fof(f302,plain,(
% 1.46/0.56    ~spl4_3 | ~spl4_10 | ~spl4_13 | spl4_22 | ~spl4_19),
% 1.46/0.56    inference(avatar_split_clause,[],[f294,f279,f298,f214,f202,f103])).
% 1.46/0.56  fof(f202,plain,(
% 1.46/0.56    spl4_10 <=> v2_funct_1(sK2)),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 1.46/0.56  fof(f279,plain,(
% 1.46/0.56    spl4_19 <=> k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 1.46/0.56  fof(f294,plain,(
% 1.46/0.56    k6_partfun1(sK0) = k6_partfun1(k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl4_19),
% 1.46/0.56    inference(superposition,[],[f83,f281])).
% 1.46/0.56  fof(f281,plain,(
% 1.46/0.56    k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~spl4_19),
% 1.46/0.56    inference(avatar_component_clause,[],[f279])).
% 1.46/0.56  fof(f292,plain,(
% 1.46/0.56    spl4_21),
% 1.46/0.56    inference(avatar_contradiction_clause,[],[f291])).
% 1.46/0.56  fof(f291,plain,(
% 1.46/0.56    $false | spl4_21),
% 1.46/0.56    inference(subsumption_resolution,[],[f52,f289])).
% 1.46/0.56  fof(f289,plain,(
% 1.46/0.56    ~v1_funct_2(sK2,sK0,sK1) | spl4_21),
% 1.46/0.56    inference(avatar_component_clause,[],[f287])).
% 1.46/0.56  fof(f52,plain,(
% 1.46/0.56    v1_funct_2(sK2,sK0,sK1)),
% 1.46/0.56    inference(cnf_transformation,[],[f20])).
% 1.46/0.56  fof(f290,plain,(
% 1.46/0.56    spl4_19 | spl4_20 | ~spl4_10 | ~spl4_13 | ~spl4_5 | ~spl4_21),
% 1.46/0.56    inference(avatar_split_clause,[],[f277,f287,f127,f214,f202,f283,f279])).
% 1.46/0.56  fof(f277,plain,(
% 1.46/0.56    ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | k1_xboole_0 = sK1 | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 1.46/0.56    inference(trivial_inequality_removal,[],[f274])).
% 1.46/0.56  fof(f274,plain,(
% 1.46/0.56    sK1 != sK1 | ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | k1_xboole_0 = sK1 | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 1.46/0.56    inference(superposition,[],[f66,f45])).
% 1.46/0.56  fof(f269,plain,(
% 1.46/0.56    spl4_16),
% 1.46/0.56    inference(avatar_contradiction_clause,[],[f268])).
% 1.46/0.56  fof(f268,plain,(
% 1.46/0.56    $false | spl4_16),
% 1.46/0.56    inference(subsumption_resolution,[],[f42,f233])).
% 1.46/0.56  fof(f233,plain,(
% 1.46/0.56    ~v1_funct_1(sK3) | spl4_16),
% 1.46/0.56    inference(avatar_component_clause,[],[f231])).
% 1.46/0.56  fof(f42,plain,(
% 1.46/0.56    v1_funct_1(sK3)),
% 1.46/0.56    inference(cnf_transformation,[],[f20])).
% 1.46/0.56  fof(f267,plain,(
% 1.46/0.56    spl4_15),
% 1.46/0.56    inference(avatar_contradiction_clause,[],[f266])).
% 1.46/0.56  fof(f266,plain,(
% 1.46/0.56    $false | spl4_15),
% 1.46/0.56    inference(subsumption_resolution,[],[f44,f229])).
% 1.46/0.56  fof(f229,plain,(
% 1.46/0.56    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl4_15),
% 1.46/0.56    inference(avatar_component_clause,[],[f227])).
% 1.46/0.56  fof(f44,plain,(
% 1.46/0.56    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.46/0.56    inference(cnf_transformation,[],[f20])).
% 1.46/0.56  fof(f265,plain,(
% 1.46/0.56    spl4_7),
% 1.46/0.56    inference(avatar_contradiction_clause,[],[f256])).
% 1.46/0.56  fof(f256,plain,(
% 1.46/0.56    $false | spl4_7),
% 1.46/0.56    inference(unit_resulting_resolution,[],[f51,f42,f44,f53,f161,f77])).
% 1.46/0.56  fof(f77,plain,(
% 1.46/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X4)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f41])).
% 1.46/0.56  fof(f161,plain,(
% 1.46/0.56    ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl4_7),
% 1.46/0.56    inference(avatar_component_clause,[],[f159])).
% 1.46/0.56  fof(f159,plain,(
% 1.46/0.56    spl4_7 <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 1.46/0.56  fof(f247,plain,(
% 1.46/0.56    spl4_13),
% 1.46/0.56    inference(avatar_contradiction_clause,[],[f246])).
% 1.46/0.56  fof(f246,plain,(
% 1.46/0.56    $false | spl4_13),
% 1.46/0.56    inference(subsumption_resolution,[],[f51,f216])).
% 1.46/0.56  fof(f216,plain,(
% 1.46/0.56    ~v1_funct_1(sK2) | spl4_13),
% 1.46/0.56    inference(avatar_component_clause,[],[f214])).
% 1.46/0.56  fof(f245,plain,(
% 1.46/0.56    spl4_10),
% 1.46/0.56    inference(avatar_contradiction_clause,[],[f244])).
% 1.46/0.56  fof(f244,plain,(
% 1.46/0.56    $false | spl4_10),
% 1.46/0.56    inference(subsumption_resolution,[],[f47,f204])).
% 1.46/0.56  fof(f204,plain,(
% 1.46/0.56    ~v2_funct_1(sK2) | spl4_10),
% 1.46/0.56    inference(avatar_component_clause,[],[f202])).
% 1.46/0.56  fof(f166,plain,(
% 1.46/0.56    ~spl4_7 | spl4_8),
% 1.46/0.56    inference(avatar_split_clause,[],[f156,f163,f159])).
% 1.46/0.56  fof(f156,plain,(
% 1.46/0.56    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) | ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.46/0.56    inference(resolution,[],[f152,f46])).
% 1.46/0.56  fof(f152,plain,(
% 1.46/0.56    ( ! [X2,X1] : (~r2_relset_1(X2,X2,X1,k6_partfun1(X2)) | k6_partfun1(X2) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))) )),
% 1.46/0.56    inference(resolution,[],[f74,f78])).
% 1.46/0.56  fof(f74,plain,(
% 1.46/0.56    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 = X3 | ~r2_relset_1(X0,X1,X2,X3)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f37])).
% 1.46/0.56  fof(f37,plain,(
% 1.46/0.56    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.46/0.56    inference(flattening,[],[f36])).
% 1.46/0.56  fof(f36,plain,(
% 1.46/0.56    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.46/0.56    inference(ennf_transformation,[],[f9])).
% 1.46/0.56  fof(f9,axiom,(
% 1.46/0.56    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.46/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.46/0.56  fof(f137,plain,(
% 1.46/0.56    spl4_5),
% 1.46/0.56    inference(avatar_contradiction_clause,[],[f136])).
% 1.46/0.56  fof(f136,plain,(
% 1.46/0.56    $false | spl4_5),
% 1.46/0.56    inference(subsumption_resolution,[],[f53,f129])).
% 1.46/0.56  fof(f129,plain,(
% 1.46/0.56    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl4_5),
% 1.46/0.56    inference(avatar_component_clause,[],[f127])).
% 1.46/0.56  fof(f135,plain,(
% 1.46/0.56    ~spl4_5 | spl4_6),
% 1.46/0.56    inference(avatar_split_clause,[],[f125,f131,f127])).
% 1.46/0.56  fof(f125,plain,(
% 1.46/0.56    sK1 = k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.46/0.56    inference(superposition,[],[f45,f65])).
% 1.46/0.56  fof(f119,plain,(
% 1.46/0.56    spl4_4),
% 1.46/0.56    inference(avatar_contradiction_clause,[],[f116])).
% 1.46/0.56  fof(f116,plain,(
% 1.46/0.56    $false | spl4_4),
% 1.46/0.56    inference(unit_resulting_resolution,[],[f64,f109])).
% 1.46/0.56  fof(f109,plain,(
% 1.46/0.56    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | spl4_4),
% 1.46/0.56    inference(avatar_component_clause,[],[f107])).
% 1.46/0.56  fof(f107,plain,(
% 1.46/0.56    spl4_4 <=> v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.46/0.56  fof(f114,plain,(
% 1.46/0.56    spl4_2),
% 1.46/0.56    inference(avatar_contradiction_clause,[],[f111])).
% 1.46/0.56  fof(f111,plain,(
% 1.46/0.56    $false | spl4_2),
% 1.46/0.56    inference(unit_resulting_resolution,[],[f64,f100])).
% 1.46/0.56  fof(f100,plain,(
% 1.46/0.56    ~v1_relat_1(k2_zfmisc_1(sK1,sK0)) | spl4_2),
% 1.46/0.56    inference(avatar_component_clause,[],[f98])).
% 1.46/0.56  fof(f98,plain,(
% 1.46/0.56    spl4_2 <=> v1_relat_1(k2_zfmisc_1(sK1,sK0))),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.46/0.56  fof(f110,plain,(
% 1.46/0.56    spl4_3 | ~spl4_4),
% 1.46/0.56    inference(avatar_split_clause,[],[f91,f107,f103])).
% 1.46/0.56  fof(f91,plain,(
% 1.46/0.56    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | v1_relat_1(sK2)),
% 1.46/0.56    inference(resolution,[],[f59,f53])).
% 1.46/0.56  fof(f101,plain,(
% 1.46/0.56    spl4_1 | ~spl4_2),
% 1.46/0.56    inference(avatar_split_clause,[],[f90,f98,f94])).
% 1.46/0.56  fof(f90,plain,(
% 1.46/0.56    ~v1_relat_1(k2_zfmisc_1(sK1,sK0)) | v1_relat_1(sK3)),
% 1.46/0.56    inference(resolution,[],[f59,f44])).
% 1.46/0.56  % SZS output end Proof for theBenchmark
% 1.46/0.56  % (29660)------------------------------
% 1.46/0.56  % (29660)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.56  % (29660)Termination reason: Refutation
% 1.46/0.56  
% 1.46/0.56  % (29660)Memory used [KB]: 6908
% 1.46/0.56  % (29660)Time elapsed: 0.119 s
% 1.46/0.56  % (29660)------------------------------
% 1.46/0.56  % (29660)------------------------------
% 1.46/0.56  % (29642)Success in time 0.202 s
%------------------------------------------------------------------------------
