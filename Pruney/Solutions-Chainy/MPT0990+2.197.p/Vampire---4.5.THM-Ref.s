%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:03:03 EST 2020

% Result     : Theorem 1.53s
% Output     : Refutation 1.53s
% Verified   : 
% Statistics : Number of formulae       :  226 ( 478 expanded)
%              Number of leaves         :   51 ( 179 expanded)
%              Depth                    :    8
%              Number of atoms          :  790 (2258 expanded)
%              Number of equality atoms :  169 ( 658 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f703,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f95,f104,f108,f112,f128,f130,f148,f179,f181,f183,f229,f236,f262,f283,f285,f287,f296,f344,f415,f428,f440,f489,f544,f574,f586,f616,f624,f632,f651,f654,f667,f673,f678,f682,f690,f700])).

fof(f700,plain,
    ( ~ spl4_20
    | ~ spl4_64 ),
    inference(avatar_contradiction_clause,[],[f693])).

fof(f693,plain,
    ( $false
    | ~ spl4_20
    | ~ spl4_64 ),
    inference(subsumption_resolution,[],[f46,f692])).

fof(f692,plain,
    ( sK3 = k2_funct_1(sK2)
    | ~ spl4_20
    | ~ spl4_64 ),
    inference(forward_demodulation,[],[f599,f249])).

fof(f249,plain,
    ( sK2 = k2_funct_1(sK3)
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f247])).

fof(f247,plain,
    ( spl4_20
  <=> sK2 = k2_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f599,plain,
    ( sK3 = k2_funct_1(k2_funct_1(sK3))
    | ~ spl4_64 ),
    inference(avatar_component_clause,[],[f597])).

fof(f597,plain,
    ( spl4_64
  <=> sK3 = k2_funct_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_64])])).

fof(f46,plain,(
    sK3 != k2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f19])).

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
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
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
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).

fof(f690,plain,
    ( ~ spl4_20
    | ~ spl4_28
    | spl4_68 ),
    inference(avatar_contradiction_clause,[],[f689])).

fof(f689,plain,
    ( $false
    | ~ spl4_20
    | ~ spl4_28
    | spl4_68 ),
    inference(subsumption_resolution,[],[f354,f684])).

fof(f684,plain,
    ( sK0 != k1_relat_1(sK2)
    | ~ spl4_20
    | spl4_68 ),
    inference(forward_demodulation,[],[f615,f249])).

fof(f615,plain,
    ( sK0 != k1_relat_1(k2_funct_1(sK3))
    | spl4_68 ),
    inference(avatar_component_clause,[],[f613])).

fof(f613,plain,
    ( spl4_68
  <=> sK0 = k1_relat_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_68])])).

fof(f354,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl4_28 ),
    inference(forward_demodulation,[],[f348,f75])).

fof(f75,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f55,f51])).

fof(f51,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f55,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f348,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k6_partfun1(sK0))
    | ~ spl4_28 ),
    inference(superposition,[],[f75,f294])).

fof(f294,plain,
    ( k6_partfun1(sK0) = k6_partfun1(k1_relat_1(sK2))
    | ~ spl4_28 ),
    inference(avatar_component_clause,[],[f292])).

fof(f292,plain,
    ( spl4_28
  <=> k6_partfun1(sK0) = k6_partfun1(k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f682,plain,
    ( ~ spl4_6
    | ~ spl4_20
    | spl4_67 ),
    inference(avatar_contradiction_clause,[],[f681])).

fof(f681,plain,
    ( $false
    | ~ spl4_6
    | ~ spl4_20
    | spl4_67 ),
    inference(trivial_inequality_removal,[],[f680])).

fof(f680,plain,
    ( k6_partfun1(sK1) != k6_partfun1(sK1)
    | ~ spl4_6
    | ~ spl4_20
    | spl4_67 ),
    inference(forward_demodulation,[],[f679,f126])).

fof(f126,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl4_6
  <=> sK1 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f679,plain,
    ( k6_partfun1(k2_relat_1(sK2)) != k6_partfun1(sK1)
    | ~ spl4_20
    | spl4_67 ),
    inference(forward_demodulation,[],[f611,f249])).

fof(f611,plain,
    ( k6_partfun1(sK1) != k6_partfun1(k2_relat_1(k2_funct_1(sK3)))
    | spl4_67 ),
    inference(avatar_component_clause,[],[f609])).

fof(f609,plain,
    ( spl4_67
  <=> k6_partfun1(sK1) = k6_partfun1(k2_relat_1(k2_funct_1(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_67])])).

fof(f678,plain,
    ( ~ spl4_20
    | spl4_66 ),
    inference(avatar_contradiction_clause,[],[f677])).

fof(f677,plain,
    ( $false
    | ~ spl4_20
    | spl4_66 ),
    inference(subsumption_resolution,[],[f43,f675])).

fof(f675,plain,
    ( ~ v2_funct_1(sK2)
    | ~ spl4_20
    | spl4_66 ),
    inference(forward_demodulation,[],[f607,f249])).

fof(f607,plain,
    ( ~ v2_funct_1(k2_funct_1(sK3))
    | spl4_66 ),
    inference(avatar_component_clause,[],[f605])).

fof(f605,plain,
    ( spl4_66
  <=> v2_funct_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_66])])).

fof(f43,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f673,plain,
    ( ~ spl4_20
    | spl4_65 ),
    inference(avatar_contradiction_clause,[],[f672])).

fof(f672,plain,
    ( $false
    | ~ spl4_20
    | spl4_65 ),
    inference(unit_resulting_resolution,[],[f60,f49,f668,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

% (15802)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f668,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl4_20
    | spl4_65 ),
    inference(forward_demodulation,[],[f603,f249])).

fof(f603,plain,
    ( ~ v1_relat_1(k2_funct_1(sK3))
    | spl4_65 ),
    inference(avatar_component_clause,[],[f601])).

fof(f601,plain,
    ( spl4_65
  <=> v1_relat_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_65])])).

fof(f49,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f19])).

fof(f60,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f667,plain,
    ( ~ spl4_20
    | spl4_62 ),
    inference(avatar_contradiction_clause,[],[f666])).

fof(f666,plain,
    ( $false
    | ~ spl4_20
    | spl4_62 ),
    inference(subsumption_resolution,[],[f47,f655])).

fof(f655,plain,
    ( ~ v1_funct_1(sK2)
    | ~ spl4_20
    | spl4_62 ),
    inference(superposition,[],[f590,f249])).

fof(f590,plain,
    ( ~ v1_funct_1(k2_funct_1(sK3))
    | spl4_62 ),
    inference(avatar_component_clause,[],[f588])).

fof(f588,plain,
    ( spl4_62
  <=> v1_funct_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_62])])).

fof(f47,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f654,plain,
    ( spl4_22
    | ~ spl4_42 ),
    inference(avatar_contradiction_clause,[],[f653])).

fof(f653,plain,
    ( $false
    | spl4_22
    | ~ spl4_42 ),
    inference(trivial_inequality_removal,[],[f652])).

fof(f652,plain,
    ( k6_partfun1(sK0) != k6_partfun1(sK0)
    | spl4_22
    | ~ spl4_42 ),
    inference(forward_demodulation,[],[f257,f438])).

fof(f438,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ spl4_42 ),
    inference(avatar_component_clause,[],[f436])).

fof(f436,plain,
    ( spl4_42
  <=> sK0 = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).

fof(f257,plain,
    ( k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3))
    | spl4_22 ),
    inference(avatar_component_clause,[],[f255])).

fof(f255,plain,
    ( spl4_22
  <=> k6_partfun1(sK0) = k6_partfun1(k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f651,plain,
    ( spl4_23
    | ~ spl4_61 ),
    inference(avatar_contradiction_clause,[],[f650])).

fof(f650,plain,
    ( $false
    | spl4_23
    | ~ spl4_61 ),
    inference(subsumption_resolution,[],[f261,f648])).

fof(f648,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl4_61 ),
    inference(forward_demodulation,[],[f637,f75])).

fof(f637,plain,
    ( k1_relat_1(sK3) = k2_relat_1(k6_partfun1(sK1))
    | ~ spl4_61 ),
    inference(superposition,[],[f75,f584])).

fof(f584,plain,
    ( k6_partfun1(k1_relat_1(sK3)) = k6_partfun1(sK1)
    | ~ spl4_61 ),
    inference(avatar_component_clause,[],[f582])).

fof(f582,plain,
    ( spl4_61
  <=> k6_partfun1(k1_relat_1(sK3)) = k6_partfun1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_61])])).

fof(f261,plain,
    ( sK1 != k1_relat_1(sK3)
    | spl4_23 ),
    inference(avatar_component_clause,[],[f259])).

fof(f259,plain,
    ( spl4_23
  <=> sK1 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f632,plain,(
    spl4_69 ),
    inference(avatar_contradiction_clause,[],[f629])).

fof(f629,plain,
    ( $false
    | spl4_69 ),
    inference(unit_resulting_resolution,[],[f74,f623])).

fof(f623,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | spl4_69 ),
    inference(avatar_component_clause,[],[f621])).

fof(f621,plain,
    ( spl4_69
  <=> v2_funct_1(k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_69])])).

fof(f74,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f50,f51])).

fof(f50,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_funct_1)).

fof(f624,plain,
    ( ~ spl4_40
    | ~ spl4_10
    | ~ spl4_11
    | spl4_48
    | spl4_21
    | ~ spl4_69
    | ~ spl4_8
    | ~ spl4_58 ),
    inference(avatar_split_clause,[],[f617,f542,f145,f621,f251,f486,f165,f161,f412])).

fof(f412,plain,
    ( spl4_40
  <=> v1_funct_2(sK3,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).

fof(f161,plain,
    ( spl4_10
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f165,plain,
    ( spl4_11
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f486,plain,
    ( spl4_48
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_48])])).

fof(f251,plain,
    ( spl4_21
  <=> v2_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f145,plain,
    ( spl4_8
  <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f542,plain,
    ( spl4_58
  <=> ! [X1,X0] :
        ( ~ v1_funct_1(X0)
        | v2_funct_1(X0)
        | k1_xboole_0 = X1
        | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X1,sK2,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
        | ~ v1_funct_2(X0,sK1,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_58])])).

fof(f617,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | v2_funct_1(sK3)
    | k1_xboole_0 = sK0
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ spl4_8
    | ~ spl4_58 ),
    inference(superposition,[],[f543,f147])).

fof(f147,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f145])).

fof(f543,plain,
    ( ! [X0,X1] :
        ( ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X1,sK2,X0))
        | v2_funct_1(X0)
        | k1_xboole_0 = X1
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
        | ~ v1_funct_2(X0,sK1,X1) )
    | ~ spl4_58 ),
    inference(avatar_component_clause,[],[f542])).

fof(f616,plain,
    ( spl4_64
    | ~ spl4_65
    | ~ spl4_66
    | ~ spl4_11
    | ~ spl4_1
    | ~ spl4_62
    | ~ spl4_67
    | ~ spl4_68
    | ~ spl4_42
    | ~ spl4_47 ),
    inference(avatar_split_clause,[],[f595,f482,f436,f613,f609,f588,f88,f165,f605,f601,f597])).

fof(f88,plain,
    ( spl4_1
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f482,plain,
    ( spl4_47
  <=> k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_47])])).

fof(f595,plain,
    ( sK0 != k1_relat_1(k2_funct_1(sK3))
    | k6_partfun1(sK1) != k6_partfun1(k2_relat_1(k2_funct_1(sK3)))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | sK3 = k2_funct_1(k2_funct_1(sK3))
    | ~ spl4_42
    | ~ spl4_47 ),
    inference(forward_demodulation,[],[f580,f438])).

fof(f580,plain,
    ( k6_partfun1(sK1) != k6_partfun1(k2_relat_1(k2_funct_1(sK3)))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(k2_funct_1(sK3))
    | k2_relat_1(sK3) != k1_relat_1(k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | sK3 = k2_funct_1(k2_funct_1(sK3))
    | ~ spl4_47 ),
    inference(superposition,[],[f79,f484])).

fof(f484,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
    | ~ spl4_47 ),
    inference(avatar_component_clause,[],[f482])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(X0)
      | k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k2_funct_1(X0) = X1 ) ),
    inference(definition_unfolding,[],[f59,f51])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(X0)
      | k1_relat_1(X0) != k2_relat_1(X1)
      | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
      | k2_funct_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_1)).

fof(f586,plain,
    ( ~ spl4_1
    | ~ spl4_21
    | ~ spl4_11
    | spl4_61
    | ~ spl4_47 ),
    inference(avatar_split_clause,[],[f578,f482,f582,f165,f251,f88])).

fof(f578,plain,
    ( k6_partfun1(k1_relat_1(sK3)) = k6_partfun1(sK1)
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_47 ),
    inference(superposition,[],[f78,f484])).

fof(f78,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f57,f51])).

fof(f57,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

fof(f574,plain,(
    ~ spl4_48 ),
    inference(avatar_contradiction_clause,[],[f555])).

fof(f555,plain,
    ( $false
    | ~ spl4_48 ),
    inference(subsumption_resolution,[],[f44,f488])).

fof(f488,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_48 ),
    inference(avatar_component_clause,[],[f486])).

fof(f44,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f19])).

fof(f544,plain,
    ( ~ spl4_9
    | spl4_58
    | ~ spl4_5
    | ~ spl4_27 ),
    inference(avatar_split_clause,[],[f540,f280,f120,f542,f157])).

fof(f157,plain,
    ( spl4_9
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f120,plain,
    ( spl4_5
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f280,plain,
    ( spl4_27
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f540,plain,(
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
    inference(trivial_inequality_removal,[],[f535])).

fof(f535,plain,(
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
    inference(superposition,[],[f68,f41])).

fof(f41,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f68,plain,(
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
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_funct_2)).

fof(f489,plain,
    ( spl4_47
    | spl4_48
    | ~ spl4_21
    | ~ spl4_11
    | ~ spl4_10
    | ~ spl4_40
    | ~ spl4_39 ),
    inference(avatar_split_clause,[],[f433,f408,f412,f161,f165,f251,f486,f482])).

fof(f408,plain,
    ( spl4_39
  <=> sK0 = k2_relset_1(sK1,sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).

fof(f433,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | k1_xboole_0 = sK0
    | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
    | ~ spl4_39 ),
    inference(trivial_inequality_removal,[],[f431])).

fof(f431,plain,
    ( sK0 != sK0
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | k1_xboole_0 = sK0
    | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
    | ~ spl4_39 ),
    inference(superposition,[],[f62,f410])).

fof(f410,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ spl4_39 ),
    inference(avatar_component_clause,[],[f408])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k1_xboole_0 = X1
      | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
            & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).

fof(f440,plain,
    ( ~ spl4_10
    | spl4_42
    | ~ spl4_39 ),
    inference(avatar_split_clause,[],[f432,f408,f436,f161])).

fof(f432,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_39 ),
    inference(superposition,[],[f61,f410])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f428,plain,(
    spl4_40 ),
    inference(avatar_contradiction_clause,[],[f427])).

fof(f427,plain,
    ( $false
    | spl4_40 ),
    inference(subsumption_resolution,[],[f39,f414])).

fof(f414,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | spl4_40 ),
    inference(avatar_component_clause,[],[f412])).

fof(f39,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f415,plain,
    ( spl4_39
    | ~ spl4_11
    | ~ spl4_5
    | ~ spl4_27
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_40 ),
    inference(avatar_split_clause,[],[f402,f412,f161,f157,f280,f120,f165,f408])).

fof(f402,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | sK0 = k2_relset_1(sK1,sK0,sK3) ),
    inference(resolution,[],[f64,f42])).

fof(f42,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X1,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_1(X2)
      | k2_relset_1(X0,X1,X2) = X1 ) ),
    inference(cnf_transformation,[],[f29])).

% (15804)Refutation not found, incomplete strategy% (15804)------------------------------
% (15804)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (15804)Termination reason: Refutation not found, incomplete strategy

% (15804)Memory used [KB]: 10746
% (15804)Time elapsed: 0.165 s
% (15804)------------------------------
% (15804)------------------------------
fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_2)).

fof(f344,plain,(
    ~ spl4_25 ),
    inference(avatar_contradiction_clause,[],[f332])).

fof(f332,plain,
    ( $false
    | ~ spl4_25 ),
    inference(subsumption_resolution,[],[f45,f274])).

fof(f274,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f272])).

fof(f272,plain,
    ( spl4_25
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f45,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f19])).

fof(f296,plain,
    ( ~ spl4_3
    | ~ spl4_26
    | ~ spl4_9
    | spl4_28
    | ~ spl4_24 ),
    inference(avatar_split_clause,[],[f289,f268,f292,f157,f276,f97])).

fof(f97,plain,
    ( spl4_3
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f276,plain,
    ( spl4_26
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f268,plain,
    ( spl4_24
  <=> k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f289,plain,
    ( k6_partfun1(sK0) = k6_partfun1(k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_24 ),
    inference(superposition,[],[f78,f270])).

fof(f270,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f268])).

fof(f287,plain,(
    spl4_27 ),
    inference(avatar_contradiction_clause,[],[f286])).

fof(f286,plain,
    ( $false
    | spl4_27 ),
    inference(subsumption_resolution,[],[f48,f282])).

fof(f282,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | spl4_27 ),
    inference(avatar_component_clause,[],[f280])).

fof(f48,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f285,plain,(
    spl4_26 ),
    inference(avatar_contradiction_clause,[],[f284])).

fof(f284,plain,
    ( $false
    | spl4_26 ),
    inference(subsumption_resolution,[],[f43,f278])).

fof(f278,plain,
    ( ~ v2_funct_1(sK2)
    | spl4_26 ),
    inference(avatar_component_clause,[],[f276])).

fof(f283,plain,
    ( spl4_24
    | spl4_25
    | ~ spl4_26
    | ~ spl4_9
    | ~ spl4_5
    | ~ spl4_27 ),
    inference(avatar_split_clause,[],[f266,f280,f120,f157,f276,f272,f268])).

fof(f266,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k1_xboole_0 = sK1
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(trivial_inequality_removal,[],[f263])).

fof(f263,plain,
    ( sK1 != sK1
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k1_xboole_0 = sK1
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(superposition,[],[f62,f41])).

fof(f262,plain,
    ( spl4_20
    | ~ spl4_1
    | ~ spl4_21
    | ~ spl4_9
    | ~ spl4_3
    | ~ spl4_11
    | ~ spl4_22
    | ~ spl4_23
    | ~ spl4_6
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f245,f190,f124,f259,f255,f165,f97,f157,f251,f88,f247])).

fof(f190,plain,
    ( spl4_14
  <=> k6_partfun1(sK0) = k5_relat_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f245,plain,
    ( sK1 != k1_relat_1(sK3)
    | k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | sK2 = k2_funct_1(sK3)
    | ~ spl4_6
    | ~ spl4_14 ),
    inference(forward_demodulation,[],[f244,f126])).

fof(f244,plain,
    ( k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK3)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_relat_1(sK3)
    | sK2 = k2_funct_1(sK3)
    | ~ spl4_14 ),
    inference(superposition,[],[f79,f192])).

fof(f192,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f190])).

fof(f236,plain,
    ( ~ spl4_9
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_5
    | spl4_14
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f233,f145,f190,f120,f165,f161,f157])).

fof(f233,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_8 ),
    inference(superposition,[],[f71,f147])).

fof(f71,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
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
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f229,plain,(
    spl4_7 ),
    inference(avatar_contradiction_clause,[],[f218])).

fof(f218,plain,
    ( $false
    | spl4_7 ),
    inference(unit_resulting_resolution,[],[f47,f38,f40,f49,f143,f73])).

fof(f73,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f143,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl4_7 ),
    inference(avatar_component_clause,[],[f141])).

fof(f141,plain,
    ( spl4_7
  <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f40,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f19])).

fof(f38,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f19])).

fof(f183,plain,(
    spl4_11 ),
    inference(avatar_contradiction_clause,[],[f182])).

fof(f182,plain,
    ( $false
    | spl4_11 ),
    inference(subsumption_resolution,[],[f38,f167])).

fof(f167,plain,
    ( ~ v1_funct_1(sK3)
    | spl4_11 ),
    inference(avatar_component_clause,[],[f165])).

fof(f181,plain,(
    spl4_10 ),
    inference(avatar_contradiction_clause,[],[f180])).

fof(f180,plain,
    ( $false
    | spl4_10 ),
    inference(subsumption_resolution,[],[f40,f163])).

fof(f163,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl4_10 ),
    inference(avatar_component_clause,[],[f161])).

fof(f179,plain,(
    spl4_9 ),
    inference(avatar_contradiction_clause,[],[f178])).

fof(f178,plain,
    ( $false
    | spl4_9 ),
    inference(subsumption_resolution,[],[f47,f159])).

fof(f159,plain,
    ( ~ v1_funct_1(sK2)
    | spl4_9 ),
    inference(avatar_component_clause,[],[f157])).

fof(f148,plain,
    ( ~ spl4_7
    | spl4_8 ),
    inference(avatar_split_clause,[],[f138,f145,f141])).

fof(f138,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
    | ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f134,f42])).

fof(f134,plain,(
    ! [X2,X1] :
      ( ~ r2_relset_1(X2,X2,X1,k6_partfun1(X2))
      | k6_partfun1(X2) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ) ),
    inference(resolution,[],[f70,f53])).

fof(f53,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f130,plain,(
    spl4_5 ),
    inference(avatar_contradiction_clause,[],[f129])).

fof(f129,plain,
    ( $false
    | spl4_5 ),
    inference(subsumption_resolution,[],[f49,f122])).

fof(f122,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl4_5 ),
    inference(avatar_component_clause,[],[f120])).

fof(f128,plain,
    ( ~ spl4_5
    | spl4_6 ),
    inference(avatar_split_clause,[],[f118,f124,f120])).

fof(f118,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f41,f61])).

fof(f112,plain,(
    spl4_4 ),
    inference(avatar_contradiction_clause,[],[f109])).

fof(f109,plain,
    ( $false
    | spl4_4 ),
    inference(unit_resulting_resolution,[],[f60,f103])).

fof(f103,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | spl4_4 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl4_4
  <=> v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f108,plain,(
    spl4_2 ),
    inference(avatar_contradiction_clause,[],[f105])).

fof(f105,plain,
    ( $false
    | spl4_2 ),
    inference(unit_resulting_resolution,[],[f60,f94])).

fof(f94,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | spl4_2 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl4_2
  <=> v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f104,plain,
    ( spl4_3
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f85,f101,f97])).

fof(f85,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK2) ),
    inference(resolution,[],[f56,f49])).

fof(f95,plain,
    ( spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f84,f92,f88])).

fof(f84,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | v1_relat_1(sK3) ),
    inference(resolution,[],[f56,f40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:59:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.51  % (15791)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.51  % (15796)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.52  % (15801)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.52  % (15797)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.52  % (15787)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.52  % (15808)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.52  % (15805)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.53  % (15788)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.33/0.53  % (15792)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.33/0.53  % (15811)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.33/0.53  % (15813)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.33/0.53  % (15789)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.33/0.54  % (15803)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.33/0.54  % (15817)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.33/0.54  % (15795)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.33/0.54  % (15804)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.33/0.54  % (15790)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.33/0.54  % (15798)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.33/0.54  % (15818)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.33/0.54  % (15794)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.33/0.54  % (15812)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.53/0.55  % (15809)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.53/0.55  % (15806)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.53/0.55  % (15799)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.53/0.55  % (15810)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.53/0.55  % (15801)Refutation found. Thanks to Tanya!
% 1.53/0.55  % SZS status Theorem for theBenchmark
% 1.53/0.55  % (15800)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.53/0.56  % (15814)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.53/0.56  % (15807)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.53/0.56  % (15816)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.53/0.56  % SZS output start Proof for theBenchmark
% 1.53/0.56  fof(f703,plain,(
% 1.53/0.56    $false),
% 1.53/0.56    inference(avatar_sat_refutation,[],[f95,f104,f108,f112,f128,f130,f148,f179,f181,f183,f229,f236,f262,f283,f285,f287,f296,f344,f415,f428,f440,f489,f544,f574,f586,f616,f624,f632,f651,f654,f667,f673,f678,f682,f690,f700])).
% 1.53/0.56  fof(f700,plain,(
% 1.53/0.56    ~spl4_20 | ~spl4_64),
% 1.53/0.56    inference(avatar_contradiction_clause,[],[f693])).
% 1.53/0.56  fof(f693,plain,(
% 1.53/0.56    $false | (~spl4_20 | ~spl4_64)),
% 1.53/0.56    inference(subsumption_resolution,[],[f46,f692])).
% 1.53/0.56  fof(f692,plain,(
% 1.53/0.56    sK3 = k2_funct_1(sK2) | (~spl4_20 | ~spl4_64)),
% 1.53/0.56    inference(forward_demodulation,[],[f599,f249])).
% 1.53/0.56  fof(f249,plain,(
% 1.53/0.56    sK2 = k2_funct_1(sK3) | ~spl4_20),
% 1.53/0.56    inference(avatar_component_clause,[],[f247])).
% 1.53/0.56  fof(f247,plain,(
% 1.53/0.56    spl4_20 <=> sK2 = k2_funct_1(sK3)),
% 1.53/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 1.53/0.56  fof(f599,plain,(
% 1.53/0.56    sK3 = k2_funct_1(k2_funct_1(sK3)) | ~spl4_64),
% 1.53/0.56    inference(avatar_component_clause,[],[f597])).
% 1.53/0.56  fof(f597,plain,(
% 1.53/0.56    spl4_64 <=> sK3 = k2_funct_1(k2_funct_1(sK3))),
% 1.53/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_64])])).
% 1.53/0.56  fof(f46,plain,(
% 1.53/0.56    sK3 != k2_funct_1(sK2)),
% 1.53/0.56    inference(cnf_transformation,[],[f19])).
% 1.53/0.56  fof(f19,plain,(
% 1.53/0.56    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.53/0.56    inference(flattening,[],[f18])).
% 1.53/0.56  fof(f18,plain,(
% 1.53/0.56    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.53/0.56    inference(ennf_transformation,[],[f17])).
% 1.53/0.56  fof(f17,negated_conjecture,(
% 1.53/0.56    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.53/0.56    inference(negated_conjecture,[],[f16])).
% 1.53/0.56  fof(f16,conjecture,(
% 1.53/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.53/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).
% 1.53/0.56  fof(f690,plain,(
% 1.53/0.56    ~spl4_20 | ~spl4_28 | spl4_68),
% 1.53/0.56    inference(avatar_contradiction_clause,[],[f689])).
% 1.53/0.56  fof(f689,plain,(
% 1.53/0.56    $false | (~spl4_20 | ~spl4_28 | spl4_68)),
% 1.53/0.56    inference(subsumption_resolution,[],[f354,f684])).
% 1.53/0.56  fof(f684,plain,(
% 1.53/0.56    sK0 != k1_relat_1(sK2) | (~spl4_20 | spl4_68)),
% 1.53/0.56    inference(forward_demodulation,[],[f615,f249])).
% 1.53/0.56  fof(f615,plain,(
% 1.53/0.56    sK0 != k1_relat_1(k2_funct_1(sK3)) | spl4_68),
% 1.53/0.56    inference(avatar_component_clause,[],[f613])).
% 1.53/0.56  fof(f613,plain,(
% 1.53/0.56    spl4_68 <=> sK0 = k1_relat_1(k2_funct_1(sK3))),
% 1.53/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_68])])).
% 1.53/0.56  fof(f354,plain,(
% 1.53/0.56    sK0 = k1_relat_1(sK2) | ~spl4_28),
% 1.53/0.56    inference(forward_demodulation,[],[f348,f75])).
% 1.53/0.56  fof(f75,plain,(
% 1.53/0.56    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 1.53/0.56    inference(definition_unfolding,[],[f55,f51])).
% 1.53/0.56  fof(f51,plain,(
% 1.53/0.56    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.53/0.56    inference(cnf_transformation,[],[f12])).
% 1.53/0.56  fof(f12,axiom,(
% 1.53/0.56    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.53/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.53/0.56  fof(f55,plain,(
% 1.53/0.56    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 1.53/0.56    inference(cnf_transformation,[],[f3])).
% 1.53/0.56  fof(f3,axiom,(
% 1.53/0.56    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.53/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 1.53/0.56  fof(f348,plain,(
% 1.53/0.56    k1_relat_1(sK2) = k2_relat_1(k6_partfun1(sK0)) | ~spl4_28),
% 1.53/0.56    inference(superposition,[],[f75,f294])).
% 1.53/0.56  fof(f294,plain,(
% 1.53/0.56    k6_partfun1(sK0) = k6_partfun1(k1_relat_1(sK2)) | ~spl4_28),
% 1.53/0.56    inference(avatar_component_clause,[],[f292])).
% 1.53/0.56  fof(f292,plain,(
% 1.53/0.56    spl4_28 <=> k6_partfun1(sK0) = k6_partfun1(k1_relat_1(sK2))),
% 1.53/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 1.53/0.56  fof(f682,plain,(
% 1.53/0.56    ~spl4_6 | ~spl4_20 | spl4_67),
% 1.53/0.56    inference(avatar_contradiction_clause,[],[f681])).
% 1.53/0.56  fof(f681,plain,(
% 1.53/0.56    $false | (~spl4_6 | ~spl4_20 | spl4_67)),
% 1.53/0.56    inference(trivial_inequality_removal,[],[f680])).
% 1.53/0.56  fof(f680,plain,(
% 1.53/0.56    k6_partfun1(sK1) != k6_partfun1(sK1) | (~spl4_6 | ~spl4_20 | spl4_67)),
% 1.53/0.56    inference(forward_demodulation,[],[f679,f126])).
% 1.53/0.56  fof(f126,plain,(
% 1.53/0.56    sK1 = k2_relat_1(sK2) | ~spl4_6),
% 1.53/0.56    inference(avatar_component_clause,[],[f124])).
% 1.53/0.56  fof(f124,plain,(
% 1.53/0.56    spl4_6 <=> sK1 = k2_relat_1(sK2)),
% 1.53/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.53/0.56  fof(f679,plain,(
% 1.53/0.56    k6_partfun1(k2_relat_1(sK2)) != k6_partfun1(sK1) | (~spl4_20 | spl4_67)),
% 1.53/0.56    inference(forward_demodulation,[],[f611,f249])).
% 1.53/0.56  fof(f611,plain,(
% 1.53/0.56    k6_partfun1(sK1) != k6_partfun1(k2_relat_1(k2_funct_1(sK3))) | spl4_67),
% 1.53/0.56    inference(avatar_component_clause,[],[f609])).
% 1.53/0.56  fof(f609,plain,(
% 1.53/0.56    spl4_67 <=> k6_partfun1(sK1) = k6_partfun1(k2_relat_1(k2_funct_1(sK3)))),
% 1.53/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_67])])).
% 1.53/0.56  fof(f678,plain,(
% 1.53/0.56    ~spl4_20 | spl4_66),
% 1.53/0.56    inference(avatar_contradiction_clause,[],[f677])).
% 1.53/0.56  fof(f677,plain,(
% 1.53/0.56    $false | (~spl4_20 | spl4_66)),
% 1.53/0.56    inference(subsumption_resolution,[],[f43,f675])).
% 1.53/0.56  fof(f675,plain,(
% 1.53/0.56    ~v2_funct_1(sK2) | (~spl4_20 | spl4_66)),
% 1.53/0.56    inference(forward_demodulation,[],[f607,f249])).
% 1.53/0.56  fof(f607,plain,(
% 1.53/0.56    ~v2_funct_1(k2_funct_1(sK3)) | spl4_66),
% 1.53/0.56    inference(avatar_component_clause,[],[f605])).
% 1.53/0.56  fof(f605,plain,(
% 1.53/0.56    spl4_66 <=> v2_funct_1(k2_funct_1(sK3))),
% 1.53/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_66])])).
% 1.53/0.56  fof(f43,plain,(
% 1.53/0.56    v2_funct_1(sK2)),
% 1.53/0.56    inference(cnf_transformation,[],[f19])).
% 1.53/0.56  fof(f673,plain,(
% 1.53/0.56    ~spl4_20 | spl4_65),
% 1.53/0.56    inference(avatar_contradiction_clause,[],[f672])).
% 1.53/0.56  fof(f672,plain,(
% 1.53/0.56    $false | (~spl4_20 | spl4_65)),
% 1.53/0.56    inference(unit_resulting_resolution,[],[f60,f49,f668,f56])).
% 1.53/0.56  fof(f56,plain,(
% 1.53/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 1.53/0.56    inference(cnf_transformation,[],[f20])).
% 1.53/0.56  fof(f20,plain,(
% 1.53/0.56    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.53/0.56    inference(ennf_transformation,[],[f1])).
% 1.53/0.56  % (15802)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.53/0.56  fof(f1,axiom,(
% 1.53/0.56    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.53/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.53/0.56  fof(f668,plain,(
% 1.53/0.56    ~v1_relat_1(sK2) | (~spl4_20 | spl4_65)),
% 1.53/0.56    inference(forward_demodulation,[],[f603,f249])).
% 1.53/0.56  fof(f603,plain,(
% 1.53/0.56    ~v1_relat_1(k2_funct_1(sK3)) | spl4_65),
% 1.53/0.56    inference(avatar_component_clause,[],[f601])).
% 1.53/0.56  fof(f601,plain,(
% 1.53/0.56    spl4_65 <=> v1_relat_1(k2_funct_1(sK3))),
% 1.53/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_65])])).
% 1.53/0.56  fof(f49,plain,(
% 1.53/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.53/0.56    inference(cnf_transformation,[],[f19])).
% 1.53/0.56  fof(f60,plain,(
% 1.53/0.56    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.53/0.56    inference(cnf_transformation,[],[f2])).
% 1.53/0.56  fof(f2,axiom,(
% 1.53/0.56    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.53/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.53/0.56  fof(f667,plain,(
% 1.53/0.56    ~spl4_20 | spl4_62),
% 1.53/0.56    inference(avatar_contradiction_clause,[],[f666])).
% 1.53/0.56  fof(f666,plain,(
% 1.53/0.56    $false | (~spl4_20 | spl4_62)),
% 1.53/0.56    inference(subsumption_resolution,[],[f47,f655])).
% 1.53/0.56  fof(f655,plain,(
% 1.53/0.56    ~v1_funct_1(sK2) | (~spl4_20 | spl4_62)),
% 1.53/0.56    inference(superposition,[],[f590,f249])).
% 1.53/0.56  fof(f590,plain,(
% 1.53/0.56    ~v1_funct_1(k2_funct_1(sK3)) | spl4_62),
% 1.53/0.56    inference(avatar_component_clause,[],[f588])).
% 1.53/0.56  fof(f588,plain,(
% 1.53/0.56    spl4_62 <=> v1_funct_1(k2_funct_1(sK3))),
% 1.53/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_62])])).
% 1.53/0.56  fof(f47,plain,(
% 1.53/0.56    v1_funct_1(sK2)),
% 1.53/0.56    inference(cnf_transformation,[],[f19])).
% 1.53/0.56  fof(f654,plain,(
% 1.53/0.56    spl4_22 | ~spl4_42),
% 1.53/0.56    inference(avatar_contradiction_clause,[],[f653])).
% 1.53/0.56  fof(f653,plain,(
% 1.53/0.56    $false | (spl4_22 | ~spl4_42)),
% 1.53/0.56    inference(trivial_inequality_removal,[],[f652])).
% 1.53/0.56  fof(f652,plain,(
% 1.53/0.56    k6_partfun1(sK0) != k6_partfun1(sK0) | (spl4_22 | ~spl4_42)),
% 1.53/0.56    inference(forward_demodulation,[],[f257,f438])).
% 1.53/0.56  fof(f438,plain,(
% 1.53/0.56    sK0 = k2_relat_1(sK3) | ~spl4_42),
% 1.53/0.56    inference(avatar_component_clause,[],[f436])).
% 1.53/0.56  fof(f436,plain,(
% 1.53/0.56    spl4_42 <=> sK0 = k2_relat_1(sK3)),
% 1.53/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).
% 1.53/0.56  fof(f257,plain,(
% 1.53/0.56    k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3)) | spl4_22),
% 1.53/0.56    inference(avatar_component_clause,[],[f255])).
% 1.53/0.56  fof(f255,plain,(
% 1.53/0.56    spl4_22 <=> k6_partfun1(sK0) = k6_partfun1(k2_relat_1(sK3))),
% 1.53/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 1.53/0.56  fof(f651,plain,(
% 1.53/0.56    spl4_23 | ~spl4_61),
% 1.53/0.56    inference(avatar_contradiction_clause,[],[f650])).
% 1.53/0.56  fof(f650,plain,(
% 1.53/0.56    $false | (spl4_23 | ~spl4_61)),
% 1.53/0.56    inference(subsumption_resolution,[],[f261,f648])).
% 1.53/0.56  fof(f648,plain,(
% 1.53/0.56    sK1 = k1_relat_1(sK3) | ~spl4_61),
% 1.53/0.56    inference(forward_demodulation,[],[f637,f75])).
% 1.53/0.56  fof(f637,plain,(
% 1.53/0.56    k1_relat_1(sK3) = k2_relat_1(k6_partfun1(sK1)) | ~spl4_61),
% 1.53/0.56    inference(superposition,[],[f75,f584])).
% 1.53/0.56  fof(f584,plain,(
% 1.53/0.56    k6_partfun1(k1_relat_1(sK3)) = k6_partfun1(sK1) | ~spl4_61),
% 1.53/0.56    inference(avatar_component_clause,[],[f582])).
% 1.53/0.56  fof(f582,plain,(
% 1.53/0.56    spl4_61 <=> k6_partfun1(k1_relat_1(sK3)) = k6_partfun1(sK1)),
% 1.53/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_61])])).
% 1.53/0.56  fof(f261,plain,(
% 1.53/0.56    sK1 != k1_relat_1(sK3) | spl4_23),
% 1.53/0.56    inference(avatar_component_clause,[],[f259])).
% 1.53/0.56  fof(f259,plain,(
% 1.53/0.56    spl4_23 <=> sK1 = k1_relat_1(sK3)),
% 1.53/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 1.53/0.56  fof(f632,plain,(
% 1.53/0.56    spl4_69),
% 1.53/0.56    inference(avatar_contradiction_clause,[],[f629])).
% 1.53/0.56  fof(f629,plain,(
% 1.53/0.56    $false | spl4_69),
% 1.53/0.56    inference(unit_resulting_resolution,[],[f74,f623])).
% 1.53/0.56  fof(f623,plain,(
% 1.53/0.56    ~v2_funct_1(k6_partfun1(sK0)) | spl4_69),
% 1.53/0.56    inference(avatar_component_clause,[],[f621])).
% 1.53/0.56  fof(f621,plain,(
% 1.53/0.56    spl4_69 <=> v2_funct_1(k6_partfun1(sK0))),
% 1.53/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_69])])).
% 1.53/0.56  fof(f74,plain,(
% 1.53/0.56    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 1.53/0.56    inference(definition_unfolding,[],[f50,f51])).
% 1.53/0.56  fof(f50,plain,(
% 1.53/0.56    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 1.53/0.56    inference(cnf_transformation,[],[f4])).
% 1.53/0.56  fof(f4,axiom,(
% 1.53/0.56    ! [X0] : v2_funct_1(k6_relat_1(X0))),
% 1.53/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_funct_1)).
% 1.53/0.56  fof(f624,plain,(
% 1.53/0.56    ~spl4_40 | ~spl4_10 | ~spl4_11 | spl4_48 | spl4_21 | ~spl4_69 | ~spl4_8 | ~spl4_58),
% 1.53/0.56    inference(avatar_split_clause,[],[f617,f542,f145,f621,f251,f486,f165,f161,f412])).
% 1.53/0.56  fof(f412,plain,(
% 1.53/0.56    spl4_40 <=> v1_funct_2(sK3,sK1,sK0)),
% 1.53/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).
% 1.53/0.56  fof(f161,plain,(
% 1.53/0.56    spl4_10 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.53/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 1.53/0.56  fof(f165,plain,(
% 1.53/0.56    spl4_11 <=> v1_funct_1(sK3)),
% 1.53/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 1.53/0.56  fof(f486,plain,(
% 1.53/0.56    spl4_48 <=> k1_xboole_0 = sK0),
% 1.53/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_48])])).
% 1.53/0.56  fof(f251,plain,(
% 1.53/0.56    spl4_21 <=> v2_funct_1(sK3)),
% 1.53/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 1.53/0.56  fof(f145,plain,(
% 1.53/0.56    spl4_8 <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)),
% 1.53/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 1.53/0.56  fof(f542,plain,(
% 1.53/0.56    spl4_58 <=> ! [X1,X0] : (~v1_funct_1(X0) | v2_funct_1(X0) | k1_xboole_0 = X1 | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X1,sK2,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) | ~v1_funct_2(X0,sK1,X1))),
% 1.53/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_58])])).
% 1.53/0.56  fof(f617,plain,(
% 1.53/0.56    ~v2_funct_1(k6_partfun1(sK0)) | v2_funct_1(sK3) | k1_xboole_0 = sK0 | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | (~spl4_8 | ~spl4_58)),
% 1.53/0.56    inference(superposition,[],[f543,f147])).
% 1.53/0.56  fof(f147,plain,(
% 1.53/0.56    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) | ~spl4_8),
% 1.53/0.56    inference(avatar_component_clause,[],[f145])).
% 1.53/0.56  fof(f543,plain,(
% 1.53/0.56    ( ! [X0,X1] : (~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X1,sK2,X0)) | v2_funct_1(X0) | k1_xboole_0 = X1 | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) | ~v1_funct_2(X0,sK1,X1)) ) | ~spl4_58),
% 1.53/0.56    inference(avatar_component_clause,[],[f542])).
% 1.53/0.56  fof(f616,plain,(
% 1.53/0.56    spl4_64 | ~spl4_65 | ~spl4_66 | ~spl4_11 | ~spl4_1 | ~spl4_62 | ~spl4_67 | ~spl4_68 | ~spl4_42 | ~spl4_47),
% 1.53/0.56    inference(avatar_split_clause,[],[f595,f482,f436,f613,f609,f588,f88,f165,f605,f601,f597])).
% 1.53/0.56  fof(f88,plain,(
% 1.53/0.56    spl4_1 <=> v1_relat_1(sK3)),
% 1.53/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.53/0.56  fof(f482,plain,(
% 1.53/0.56    spl4_47 <=> k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)),
% 1.53/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_47])])).
% 1.53/0.56  fof(f595,plain,(
% 1.53/0.56    sK0 != k1_relat_1(k2_funct_1(sK3)) | k6_partfun1(sK1) != k6_partfun1(k2_relat_1(k2_funct_1(sK3))) | ~v1_funct_1(k2_funct_1(sK3)) | ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v2_funct_1(k2_funct_1(sK3)) | ~v1_relat_1(k2_funct_1(sK3)) | sK3 = k2_funct_1(k2_funct_1(sK3)) | (~spl4_42 | ~spl4_47)),
% 1.53/0.56    inference(forward_demodulation,[],[f580,f438])).
% 1.53/0.56  fof(f580,plain,(
% 1.53/0.56    k6_partfun1(sK1) != k6_partfun1(k2_relat_1(k2_funct_1(sK3))) | ~v1_funct_1(k2_funct_1(sK3)) | ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v2_funct_1(k2_funct_1(sK3)) | k2_relat_1(sK3) != k1_relat_1(k2_funct_1(sK3)) | ~v1_relat_1(k2_funct_1(sK3)) | sK3 = k2_funct_1(k2_funct_1(sK3)) | ~spl4_47),
% 1.53/0.56    inference(superposition,[],[f79,f484])).
% 1.53/0.56  fof(f484,plain,(
% 1.53/0.56    k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) | ~spl4_47),
% 1.53/0.56    inference(avatar_component_clause,[],[f482])).
% 1.53/0.56  fof(f79,plain,(
% 1.53/0.56    ( ! [X0,X1] : (k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v1_relat_1(X0) | k2_funct_1(X0) = X1) )),
% 1.53/0.56    inference(definition_unfolding,[],[f59,f51])).
% 1.53/0.56  fof(f59,plain,(
% 1.53/0.56    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(X0) | k1_relat_1(X0) != k2_relat_1(X1) | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k2_funct_1(X0) = X1) )),
% 1.53/0.56    inference(cnf_transformation,[],[f24])).
% 1.53/0.56  fof(f24,plain,(
% 1.53/0.56    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.53/0.56    inference(flattening,[],[f23])).
% 1.53/0.56  fof(f23,plain,(
% 1.53/0.56    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.53/0.56    inference(ennf_transformation,[],[f6])).
% 1.53/0.56  fof(f6,axiom,(
% 1.53/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 1.53/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_1)).
% 1.53/0.56  fof(f586,plain,(
% 1.53/0.56    ~spl4_1 | ~spl4_21 | ~spl4_11 | spl4_61 | ~spl4_47),
% 1.53/0.56    inference(avatar_split_clause,[],[f578,f482,f582,f165,f251,f88])).
% 1.53/0.56  fof(f578,plain,(
% 1.53/0.56    k6_partfun1(k1_relat_1(sK3)) = k6_partfun1(sK1) | ~v1_funct_1(sK3) | ~v2_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl4_47),
% 1.53/0.56    inference(superposition,[],[f78,f484])).
% 1.53/0.56  fof(f78,plain,(
% 1.53/0.56    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.53/0.56    inference(definition_unfolding,[],[f57,f51])).
% 1.53/0.56  fof(f57,plain,(
% 1.53/0.56    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) )),
% 1.53/0.56    inference(cnf_transformation,[],[f22])).
% 1.53/0.56  fof(f22,plain,(
% 1.53/0.56    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.53/0.56    inference(flattening,[],[f21])).
% 1.53/0.56  fof(f21,plain,(
% 1.53/0.56    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.53/0.56    inference(ennf_transformation,[],[f5])).
% 1.53/0.56  fof(f5,axiom,(
% 1.53/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 1.53/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).
% 1.53/0.56  fof(f574,plain,(
% 1.53/0.56    ~spl4_48),
% 1.53/0.56    inference(avatar_contradiction_clause,[],[f555])).
% 1.53/0.56  fof(f555,plain,(
% 1.53/0.56    $false | ~spl4_48),
% 1.53/0.56    inference(subsumption_resolution,[],[f44,f488])).
% 1.53/0.56  fof(f488,plain,(
% 1.53/0.56    k1_xboole_0 = sK0 | ~spl4_48),
% 1.53/0.56    inference(avatar_component_clause,[],[f486])).
% 1.53/0.56  fof(f44,plain,(
% 1.53/0.56    k1_xboole_0 != sK0),
% 1.53/0.56    inference(cnf_transformation,[],[f19])).
% 1.53/0.56  fof(f544,plain,(
% 1.53/0.56    ~spl4_9 | spl4_58 | ~spl4_5 | ~spl4_27),
% 1.53/0.56    inference(avatar_split_clause,[],[f540,f280,f120,f542,f157])).
% 1.53/0.56  fof(f157,plain,(
% 1.53/0.56    spl4_9 <=> v1_funct_1(sK2)),
% 1.53/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 1.53/0.56  fof(f120,plain,(
% 1.53/0.56    spl4_5 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.53/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.53/0.56  fof(f280,plain,(
% 1.53/0.56    spl4_27 <=> v1_funct_2(sK2,sK0,sK1)),
% 1.53/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).
% 1.53/0.56  fof(f540,plain,(
% 1.53/0.56    ( ! [X0,X1] : (~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(X0) | ~v1_funct_2(X0,sK1,X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X1,sK2,X0)) | ~v1_funct_1(sK2) | k1_xboole_0 = X1 | v2_funct_1(X0)) )),
% 1.53/0.56    inference(trivial_inequality_removal,[],[f535])).
% 1.53/0.56  fof(f535,plain,(
% 1.53/0.56    ( ! [X0,X1] : (sK1 != sK1 | ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(X0) | ~v1_funct_2(X0,sK1,X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X1,sK2,X0)) | ~v1_funct_1(sK2) | k1_xboole_0 = X1 | v2_funct_1(X0)) )),
% 1.53/0.56    inference(superposition,[],[f68,f41])).
% 1.53/0.56  fof(f41,plain,(
% 1.53/0.56    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 1.53/0.56    inference(cnf_transformation,[],[f19])).
% 1.53/0.56  fof(f68,plain,(
% 1.53/0.56    ( ! [X4,X2,X0,X3,X1] : (k2_relset_1(X0,X1,X3) != X1 | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X1,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~v1_funct_1(X3) | k1_xboole_0 = X2 | v2_funct_1(X4)) )),
% 1.53/0.56    inference(cnf_transformation,[],[f31])).
% 1.53/0.56  fof(f31,plain,(
% 1.53/0.56    ! [X0,X1,X2,X3] : (! [X4] : ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.53/0.56    inference(flattening,[],[f30])).
% 1.53/0.56  fof(f30,plain,(
% 1.53/0.56    ! [X0,X1,X2,X3] : (! [X4] : ((((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | (k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.53/0.56    inference(ennf_transformation,[],[f14])).
% 1.53/0.56  fof(f14,axiom,(
% 1.53/0.56    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) => ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 1.53/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_funct_2)).
% 1.53/0.56  fof(f489,plain,(
% 1.53/0.56    spl4_47 | spl4_48 | ~spl4_21 | ~spl4_11 | ~spl4_10 | ~spl4_40 | ~spl4_39),
% 1.53/0.56    inference(avatar_split_clause,[],[f433,f408,f412,f161,f165,f251,f486,f482])).
% 1.53/0.56  fof(f408,plain,(
% 1.53/0.56    spl4_39 <=> sK0 = k2_relset_1(sK1,sK0,sK3)),
% 1.53/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).
% 1.53/0.56  fof(f433,plain,(
% 1.53/0.56    ~v1_funct_2(sK3,sK1,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~v2_funct_1(sK3) | k1_xboole_0 = sK0 | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) | ~spl4_39),
% 1.53/0.56    inference(trivial_inequality_removal,[],[f431])).
% 1.53/0.56  fof(f431,plain,(
% 1.53/0.56    sK0 != sK0 | ~v1_funct_2(sK3,sK1,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~v2_funct_1(sK3) | k1_xboole_0 = sK0 | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) | ~spl4_39),
% 1.53/0.56    inference(superposition,[],[f62,f410])).
% 1.53/0.56  fof(f410,plain,(
% 1.53/0.56    sK0 = k2_relset_1(sK1,sK0,sK3) | ~spl4_39),
% 1.53/0.56    inference(avatar_component_clause,[],[f408])).
% 1.53/0.56  fof(f62,plain,(
% 1.53/0.56    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v2_funct_1(X2) | k1_xboole_0 = X1 | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) )),
% 1.53/0.56    inference(cnf_transformation,[],[f27])).
% 1.53/0.56  fof(f27,plain,(
% 1.53/0.56    ! [X0,X1,X2] : ((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.53/0.56    inference(flattening,[],[f26])).
% 1.53/0.56  fof(f26,plain,(
% 1.53/0.56    ! [X0,X1,X2] : ((((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.53/0.56    inference(ennf_transformation,[],[f15])).
% 1.53/0.56  fof(f15,axiom,(
% 1.53/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1)))),
% 1.53/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).
% 1.53/0.56  fof(f440,plain,(
% 1.53/0.56    ~spl4_10 | spl4_42 | ~spl4_39),
% 1.53/0.56    inference(avatar_split_clause,[],[f432,f408,f436,f161])).
% 1.53/0.56  fof(f432,plain,(
% 1.53/0.56    sK0 = k2_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_39),
% 1.53/0.56    inference(superposition,[],[f61,f410])).
% 1.53/0.56  fof(f61,plain,(
% 1.53/0.56    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.53/0.56    inference(cnf_transformation,[],[f25])).
% 1.53/0.56  fof(f25,plain,(
% 1.53/0.56    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.53/0.56    inference(ennf_transformation,[],[f7])).
% 1.53/0.56  fof(f7,axiom,(
% 1.53/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.53/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.53/0.56  fof(f428,plain,(
% 1.53/0.56    spl4_40),
% 1.53/0.56    inference(avatar_contradiction_clause,[],[f427])).
% 1.53/0.56  fof(f427,plain,(
% 1.53/0.56    $false | spl4_40),
% 1.53/0.56    inference(subsumption_resolution,[],[f39,f414])).
% 1.53/0.56  fof(f414,plain,(
% 1.53/0.56    ~v1_funct_2(sK3,sK1,sK0) | spl4_40),
% 1.53/0.56    inference(avatar_component_clause,[],[f412])).
% 1.53/0.56  fof(f39,plain,(
% 1.53/0.56    v1_funct_2(sK3,sK1,sK0)),
% 1.53/0.56    inference(cnf_transformation,[],[f19])).
% 1.53/0.56  fof(f415,plain,(
% 1.53/0.56    spl4_39 | ~spl4_11 | ~spl4_5 | ~spl4_27 | ~spl4_9 | ~spl4_10 | ~spl4_40),
% 1.53/0.56    inference(avatar_split_clause,[],[f402,f412,f161,f157,f280,f120,f165,f408])).
% 1.53/0.56  fof(f402,plain,(
% 1.53/0.56    ~v1_funct_2(sK3,sK1,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | sK0 = k2_relset_1(sK1,sK0,sK3)),
% 1.53/0.56    inference(resolution,[],[f64,f42])).
% 1.53/0.56  fof(f42,plain,(
% 1.53/0.56    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 1.53/0.56    inference(cnf_transformation,[],[f19])).
% 1.53/0.56  fof(f64,plain,(
% 1.53/0.56    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_1(X2) | k2_relset_1(X0,X1,X2) = X1) )),
% 1.53/0.56    inference(cnf_transformation,[],[f29])).
% 1.53/0.56  % (15804)Refutation not found, incomplete strategy% (15804)------------------------------
% 1.53/0.56  % (15804)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.56  % (15804)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.56  
% 1.53/0.56  % (15804)Memory used [KB]: 10746
% 1.53/0.56  % (15804)Time elapsed: 0.165 s
% 1.53/0.56  % (15804)------------------------------
% 1.53/0.56  % (15804)------------------------------
% 1.53/0.56  fof(f29,plain,(
% 1.53/0.56    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.53/0.56    inference(flattening,[],[f28])).
% 1.53/0.56  fof(f28,plain,(
% 1.53/0.56    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.53/0.56    inference(ennf_transformation,[],[f13])).
% 1.53/0.56  fof(f13,axiom,(
% 1.53/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 1.53/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_2)).
% 1.53/0.56  fof(f344,plain,(
% 1.53/0.56    ~spl4_25),
% 1.53/0.56    inference(avatar_contradiction_clause,[],[f332])).
% 1.53/0.56  fof(f332,plain,(
% 1.53/0.56    $false | ~spl4_25),
% 1.53/0.56    inference(subsumption_resolution,[],[f45,f274])).
% 1.53/0.56  fof(f274,plain,(
% 1.53/0.56    k1_xboole_0 = sK1 | ~spl4_25),
% 1.53/0.56    inference(avatar_component_clause,[],[f272])).
% 1.53/0.56  fof(f272,plain,(
% 1.53/0.56    spl4_25 <=> k1_xboole_0 = sK1),
% 1.53/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 1.53/0.56  fof(f45,plain,(
% 1.53/0.56    k1_xboole_0 != sK1),
% 1.53/0.56    inference(cnf_transformation,[],[f19])).
% 1.53/0.56  fof(f296,plain,(
% 1.53/0.56    ~spl4_3 | ~spl4_26 | ~spl4_9 | spl4_28 | ~spl4_24),
% 1.53/0.56    inference(avatar_split_clause,[],[f289,f268,f292,f157,f276,f97])).
% 1.53/0.56  fof(f97,plain,(
% 1.53/0.56    spl4_3 <=> v1_relat_1(sK2)),
% 1.53/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.53/0.56  fof(f276,plain,(
% 1.53/0.56    spl4_26 <=> v2_funct_1(sK2)),
% 1.53/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 1.53/0.56  fof(f268,plain,(
% 1.53/0.56    spl4_24 <=> k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 1.53/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 1.53/0.57  fof(f289,plain,(
% 1.53/0.57    k6_partfun1(sK0) = k6_partfun1(k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl4_24),
% 1.53/0.57    inference(superposition,[],[f78,f270])).
% 1.53/0.57  fof(f270,plain,(
% 1.53/0.57    k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~spl4_24),
% 1.53/0.57    inference(avatar_component_clause,[],[f268])).
% 1.53/0.57  fof(f287,plain,(
% 1.53/0.57    spl4_27),
% 1.53/0.57    inference(avatar_contradiction_clause,[],[f286])).
% 1.53/0.57  fof(f286,plain,(
% 1.53/0.57    $false | spl4_27),
% 1.53/0.57    inference(subsumption_resolution,[],[f48,f282])).
% 1.53/0.57  fof(f282,plain,(
% 1.53/0.57    ~v1_funct_2(sK2,sK0,sK1) | spl4_27),
% 1.53/0.57    inference(avatar_component_clause,[],[f280])).
% 1.53/0.57  fof(f48,plain,(
% 1.53/0.57    v1_funct_2(sK2,sK0,sK1)),
% 1.53/0.57    inference(cnf_transformation,[],[f19])).
% 1.53/0.57  fof(f285,plain,(
% 1.53/0.57    spl4_26),
% 1.53/0.57    inference(avatar_contradiction_clause,[],[f284])).
% 1.53/0.57  fof(f284,plain,(
% 1.53/0.57    $false | spl4_26),
% 1.53/0.57    inference(subsumption_resolution,[],[f43,f278])).
% 1.53/0.57  fof(f278,plain,(
% 1.53/0.57    ~v2_funct_1(sK2) | spl4_26),
% 1.53/0.57    inference(avatar_component_clause,[],[f276])).
% 1.53/0.57  fof(f283,plain,(
% 1.53/0.57    spl4_24 | spl4_25 | ~spl4_26 | ~spl4_9 | ~spl4_5 | ~spl4_27),
% 1.53/0.57    inference(avatar_split_clause,[],[f266,f280,f120,f157,f276,f272,f268])).
% 1.53/0.57  fof(f266,plain,(
% 1.53/0.57    ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | k1_xboole_0 = sK1 | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 1.53/0.57    inference(trivial_inequality_removal,[],[f263])).
% 1.53/0.57  fof(f263,plain,(
% 1.53/0.57    sK1 != sK1 | ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | k1_xboole_0 = sK1 | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 1.53/0.57    inference(superposition,[],[f62,f41])).
% 1.53/0.57  fof(f262,plain,(
% 1.53/0.57    spl4_20 | ~spl4_1 | ~spl4_21 | ~spl4_9 | ~spl4_3 | ~spl4_11 | ~spl4_22 | ~spl4_23 | ~spl4_6 | ~spl4_14),
% 1.53/0.57    inference(avatar_split_clause,[],[f245,f190,f124,f259,f255,f165,f97,f157,f251,f88,f247])).
% 1.53/0.57  fof(f190,plain,(
% 1.53/0.57    spl4_14 <=> k6_partfun1(sK0) = k5_relat_1(sK2,sK3)),
% 1.53/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 1.53/0.57  fof(f245,plain,(
% 1.53/0.57    sK1 != k1_relat_1(sK3) | k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v2_funct_1(sK3) | ~v1_relat_1(sK3) | sK2 = k2_funct_1(sK3) | (~spl4_6 | ~spl4_14)),
% 1.53/0.57    inference(forward_demodulation,[],[f244,f126])).
% 1.53/0.57  fof(f244,plain,(
% 1.53/0.57    k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v2_funct_1(sK3) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v1_relat_1(sK3) | sK2 = k2_funct_1(sK3) | ~spl4_14),
% 1.53/0.57    inference(superposition,[],[f79,f192])).
% 1.53/0.57  fof(f192,plain,(
% 1.53/0.57    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~spl4_14),
% 1.53/0.57    inference(avatar_component_clause,[],[f190])).
% 1.53/0.57  fof(f236,plain,(
% 1.53/0.57    ~spl4_9 | ~spl4_10 | ~spl4_11 | ~spl4_5 | spl4_14 | ~spl4_8),
% 1.53/0.57    inference(avatar_split_clause,[],[f233,f145,f190,f120,f165,f161,f157])).
% 1.53/0.57  fof(f233,plain,(
% 1.53/0.57    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK2) | ~spl4_8),
% 1.53/0.57    inference(superposition,[],[f71,f147])).
% 1.53/0.57  fof(f71,plain,(
% 1.53/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X4)) )),
% 1.53/0.57    inference(cnf_transformation,[],[f35])).
% 1.53/0.57  fof(f35,plain,(
% 1.53/0.57    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.53/0.57    inference(flattening,[],[f34])).
% 1.53/0.57  fof(f34,plain,(
% 1.53/0.57    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.53/0.57    inference(ennf_transformation,[],[f11])).
% 1.53/0.57  fof(f11,axiom,(
% 1.53/0.57    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.53/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 1.53/0.57  fof(f229,plain,(
% 1.53/0.57    spl4_7),
% 1.53/0.57    inference(avatar_contradiction_clause,[],[f218])).
% 1.53/0.57  fof(f218,plain,(
% 1.53/0.57    $false | spl4_7),
% 1.53/0.57    inference(unit_resulting_resolution,[],[f47,f38,f40,f49,f143,f73])).
% 1.53/0.57  fof(f73,plain,(
% 1.53/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X4)) )),
% 1.53/0.57    inference(cnf_transformation,[],[f37])).
% 1.53/0.57  fof(f37,plain,(
% 1.53/0.57    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.53/0.57    inference(flattening,[],[f36])).
% 1.53/0.57  fof(f36,plain,(
% 1.53/0.57    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.53/0.57    inference(ennf_transformation,[],[f9])).
% 1.53/0.57  fof(f9,axiom,(
% 1.53/0.57    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 1.53/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 1.53/0.57  fof(f143,plain,(
% 1.53/0.57    ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl4_7),
% 1.53/0.57    inference(avatar_component_clause,[],[f141])).
% 1.53/0.57  fof(f141,plain,(
% 1.53/0.57    spl4_7 <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.53/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 1.53/0.57  fof(f40,plain,(
% 1.53/0.57    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.53/0.57    inference(cnf_transformation,[],[f19])).
% 1.53/0.57  fof(f38,plain,(
% 1.53/0.57    v1_funct_1(sK3)),
% 1.53/0.57    inference(cnf_transformation,[],[f19])).
% 1.53/0.57  fof(f183,plain,(
% 1.53/0.57    spl4_11),
% 1.53/0.57    inference(avatar_contradiction_clause,[],[f182])).
% 1.53/0.57  fof(f182,plain,(
% 1.53/0.57    $false | spl4_11),
% 1.53/0.57    inference(subsumption_resolution,[],[f38,f167])).
% 1.53/0.57  fof(f167,plain,(
% 1.53/0.57    ~v1_funct_1(sK3) | spl4_11),
% 1.53/0.57    inference(avatar_component_clause,[],[f165])).
% 1.53/0.57  fof(f181,plain,(
% 1.53/0.57    spl4_10),
% 1.53/0.57    inference(avatar_contradiction_clause,[],[f180])).
% 1.53/0.57  fof(f180,plain,(
% 1.53/0.57    $false | spl4_10),
% 1.53/0.57    inference(subsumption_resolution,[],[f40,f163])).
% 1.53/0.57  fof(f163,plain,(
% 1.53/0.57    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl4_10),
% 1.53/0.57    inference(avatar_component_clause,[],[f161])).
% 1.53/0.57  fof(f179,plain,(
% 1.53/0.57    spl4_9),
% 1.53/0.57    inference(avatar_contradiction_clause,[],[f178])).
% 1.53/0.57  fof(f178,plain,(
% 1.53/0.57    $false | spl4_9),
% 1.53/0.57    inference(subsumption_resolution,[],[f47,f159])).
% 1.53/0.57  fof(f159,plain,(
% 1.53/0.57    ~v1_funct_1(sK2) | spl4_9),
% 1.53/0.57    inference(avatar_component_clause,[],[f157])).
% 1.53/0.57  fof(f148,plain,(
% 1.53/0.57    ~spl4_7 | spl4_8),
% 1.53/0.57    inference(avatar_split_clause,[],[f138,f145,f141])).
% 1.53/0.57  fof(f138,plain,(
% 1.53/0.57    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) | ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.53/0.57    inference(resolution,[],[f134,f42])).
% 1.53/0.57  fof(f134,plain,(
% 1.53/0.57    ( ! [X2,X1] : (~r2_relset_1(X2,X2,X1,k6_partfun1(X2)) | k6_partfun1(X2) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))) )),
% 1.53/0.57    inference(resolution,[],[f70,f53])).
% 1.53/0.57  fof(f53,plain,(
% 1.53/0.57    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.53/0.57    inference(cnf_transformation,[],[f10])).
% 1.53/0.57  fof(f10,axiom,(
% 1.53/0.57    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 1.53/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 1.53/0.57  fof(f70,plain,(
% 1.53/0.57    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 = X3 | ~r2_relset_1(X0,X1,X2,X3)) )),
% 1.53/0.57    inference(cnf_transformation,[],[f33])).
% 1.53/0.57  fof(f33,plain,(
% 1.53/0.57    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.53/0.57    inference(flattening,[],[f32])).
% 1.53/0.57  fof(f32,plain,(
% 1.53/0.57    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.53/0.57    inference(ennf_transformation,[],[f8])).
% 1.53/0.57  fof(f8,axiom,(
% 1.53/0.57    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.53/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.53/0.57  fof(f130,plain,(
% 1.53/0.57    spl4_5),
% 1.53/0.57    inference(avatar_contradiction_clause,[],[f129])).
% 1.53/0.57  fof(f129,plain,(
% 1.53/0.57    $false | spl4_5),
% 1.53/0.57    inference(subsumption_resolution,[],[f49,f122])).
% 1.53/0.57  fof(f122,plain,(
% 1.53/0.57    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl4_5),
% 1.53/0.57    inference(avatar_component_clause,[],[f120])).
% 1.53/0.57  fof(f128,plain,(
% 1.53/0.57    ~spl4_5 | spl4_6),
% 1.53/0.57    inference(avatar_split_clause,[],[f118,f124,f120])).
% 1.53/0.57  fof(f118,plain,(
% 1.53/0.57    sK1 = k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.53/0.57    inference(superposition,[],[f41,f61])).
% 1.53/0.57  fof(f112,plain,(
% 1.53/0.57    spl4_4),
% 1.53/0.57    inference(avatar_contradiction_clause,[],[f109])).
% 1.53/0.57  fof(f109,plain,(
% 1.53/0.57    $false | spl4_4),
% 1.53/0.57    inference(unit_resulting_resolution,[],[f60,f103])).
% 1.53/0.57  fof(f103,plain,(
% 1.53/0.57    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | spl4_4),
% 1.53/0.57    inference(avatar_component_clause,[],[f101])).
% 1.53/0.57  fof(f101,plain,(
% 1.53/0.57    spl4_4 <=> v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 1.53/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.53/0.57  fof(f108,plain,(
% 1.53/0.57    spl4_2),
% 1.53/0.57    inference(avatar_contradiction_clause,[],[f105])).
% 1.53/0.57  fof(f105,plain,(
% 1.53/0.57    $false | spl4_2),
% 1.53/0.57    inference(unit_resulting_resolution,[],[f60,f94])).
% 1.53/0.57  fof(f94,plain,(
% 1.53/0.57    ~v1_relat_1(k2_zfmisc_1(sK1,sK0)) | spl4_2),
% 1.53/0.57    inference(avatar_component_clause,[],[f92])).
% 1.53/0.57  fof(f92,plain,(
% 1.53/0.57    spl4_2 <=> v1_relat_1(k2_zfmisc_1(sK1,sK0))),
% 1.53/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.53/0.57  fof(f104,plain,(
% 1.53/0.57    spl4_3 | ~spl4_4),
% 1.53/0.57    inference(avatar_split_clause,[],[f85,f101,f97])).
% 1.53/0.57  fof(f85,plain,(
% 1.53/0.57    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | v1_relat_1(sK2)),
% 1.53/0.57    inference(resolution,[],[f56,f49])).
% 1.53/0.57  fof(f95,plain,(
% 1.53/0.57    spl4_1 | ~spl4_2),
% 1.53/0.57    inference(avatar_split_clause,[],[f84,f92,f88])).
% 1.53/0.57  fof(f84,plain,(
% 1.53/0.57    ~v1_relat_1(k2_zfmisc_1(sK1,sK0)) | v1_relat_1(sK3)),
% 1.53/0.57    inference(resolution,[],[f56,f40])).
% 1.53/0.57  % SZS output end Proof for theBenchmark
% 1.53/0.57  % (15801)------------------------------
% 1.53/0.57  % (15801)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.57  % (15801)Termination reason: Refutation
% 1.53/0.57  
% 1.53/0.57  % (15801)Memory used [KB]: 6780
% 1.53/0.57  % (15801)Time elapsed: 0.147 s
% 1.53/0.57  % (15801)------------------------------
% 1.53/0.57  % (15801)------------------------------
% 1.53/0.57  % (15783)Success in time 0.21 s
%------------------------------------------------------------------------------
