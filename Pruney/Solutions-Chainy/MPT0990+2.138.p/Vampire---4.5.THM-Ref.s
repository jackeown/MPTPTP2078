%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:52 EST 2020

% Result     : Theorem 1.76s
% Output     : Refutation 1.76s
% Verified   : 
% Statistics : Number of formulae       :  254 ( 526 expanded)
%              Number of leaves         :   58 ( 201 expanded)
%              Depth                    :    8
%              Number of atoms          :  895 (2472 expanded)
%              Number of equality atoms :  171 ( 672 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f770,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f110,f119,f123,f128,f143,f145,f163,f199,f201,f203,f205,f222,f249,f281,f283,f285,f308,f343,f346,f355,f359,f424,f431,f443,f491,f588,f596,f601,f627,f665,f672,f675,f678,f700,f704,f707,f720,f724,f751,f766])).

fof(f766,plain,
    ( ~ spl4_16
    | ~ spl4_71 ),
    inference(avatar_contradiction_clause,[],[f754])).

fof(f754,plain,
    ( $false
    | ~ spl4_16
    | ~ spl4_71 ),
    inference(subsumption_resolution,[],[f53,f753])).

fof(f753,plain,
    ( sK3 = k2_funct_1(sK2)
    | ~ spl4_16
    | ~ spl4_71 ),
    inference(forward_demodulation,[],[f648,f236])).

fof(f236,plain,
    ( sK2 = k2_funct_1(sK3)
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f234])).

fof(f234,plain,
    ( spl4_16
  <=> sK2 = k2_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f648,plain,
    ( sK3 = k2_funct_1(k2_funct_1(sK3))
    | ~ spl4_71 ),
    inference(avatar_component_clause,[],[f646])).

fof(f646,plain,
    ( spl4_71
  <=> sK3 = k2_funct_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_71])])).

fof(f53,plain,(
    sK3 != k2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
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
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
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

fof(f751,plain,
    ( ~ spl4_16
    | ~ spl4_20
    | spl4_75 ),
    inference(avatar_contradiction_clause,[],[f750])).

fof(f750,plain,
    ( $false
    | ~ spl4_16
    | ~ spl4_20
    | spl4_75 ),
    inference(subsumption_resolution,[],[f255,f726])).

fof(f726,plain,
    ( sK0 != k1_relat_1(sK2)
    | ~ spl4_16
    | spl4_75 ),
    inference(forward_demodulation,[],[f664,f236])).

fof(f664,plain,
    ( sK0 != k1_relat_1(k2_funct_1(sK3))
    | spl4_75 ),
    inference(avatar_component_clause,[],[f662])).

fof(f662,plain,
    ( spl4_75
  <=> sK0 = k1_relat_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_75])])).

fof(f255,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f253])).

fof(f253,plain,
    ( spl4_20
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f724,plain,
    ( ~ spl4_6
    | ~ spl4_16
    | spl4_74 ),
    inference(avatar_contradiction_clause,[],[f723])).

fof(f723,plain,
    ( $false
    | ~ spl4_6
    | ~ spl4_16
    | spl4_74 ),
    inference(trivial_inequality_removal,[],[f722])).

fof(f722,plain,
    ( k6_partfun1(sK1) != k6_partfun1(sK1)
    | ~ spl4_6
    | ~ spl4_16
    | spl4_74 ),
    inference(forward_demodulation,[],[f721,f141])).

fof(f141,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f139])).

fof(f139,plain,
    ( spl4_6
  <=> sK1 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f721,plain,
    ( k6_partfun1(k2_relat_1(sK2)) != k6_partfun1(sK1)
    | ~ spl4_16
    | spl4_74 ),
    inference(forward_demodulation,[],[f660,f236])).

fof(f660,plain,
    ( k6_partfun1(sK1) != k6_partfun1(k2_relat_1(k2_funct_1(sK3)))
    | spl4_74 ),
    inference(avatar_component_clause,[],[f658])).

fof(f658,plain,
    ( spl4_74
  <=> k6_partfun1(sK1) = k6_partfun1(k2_relat_1(k2_funct_1(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_74])])).

fof(f720,plain,
    ( ~ spl4_16
    | spl4_73 ),
    inference(avatar_contradiction_clause,[],[f719])).

fof(f719,plain,
    ( $false
    | ~ spl4_16
    | spl4_73 ),
    inference(subsumption_resolution,[],[f50,f708])).

fof(f708,plain,
    ( ~ v2_funct_1(sK2)
    | ~ spl4_16
    | spl4_73 ),
    inference(superposition,[],[f656,f236])).

fof(f656,plain,
    ( ~ v2_funct_1(k2_funct_1(sK3))
    | spl4_73 ),
    inference(avatar_component_clause,[],[f654])).

fof(f654,plain,
    ( spl4_73
  <=> v2_funct_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_73])])).

fof(f50,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f707,plain,
    ( spl4_18
    | ~ spl4_43 ),
    inference(avatar_contradiction_clause,[],[f706])).

fof(f706,plain,
    ( $false
    | spl4_18
    | ~ spl4_43 ),
    inference(trivial_inequality_removal,[],[f705])).

fof(f705,plain,
    ( k6_partfun1(sK0) != k6_partfun1(sK0)
    | spl4_18
    | ~ spl4_43 ),
    inference(forward_demodulation,[],[f244,f441])).

fof(f441,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ spl4_43 ),
    inference(avatar_component_clause,[],[f439])).

fof(f439,plain,
    ( spl4_43
  <=> sK0 = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).

fof(f244,plain,
    ( k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3))
    | spl4_18 ),
    inference(avatar_component_clause,[],[f242])).

fof(f242,plain,
    ( spl4_18
  <=> k6_partfun1(sK0) = k6_partfun1(k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f704,plain,(
    spl4_79 ),
    inference(avatar_contradiction_clause,[],[f701])).

fof(f701,plain,
    ( $false
    | spl4_79 ),
    inference(unit_resulting_resolution,[],[f93,f699])).

fof(f699,plain,
    ( ~ r1_tarski(sK0,sK0)
    | spl4_79 ),
    inference(avatar_component_clause,[],[f697])).

fof(f697,plain,
    ( spl4_79
  <=> r1_tarski(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_79])])).

fof(f93,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f700,plain,
    ( ~ spl4_1
    | ~ spl4_17
    | ~ spl4_11
    | ~ spl4_79
    | ~ spl4_43
    | spl4_76 ),
    inference(avatar_split_clause,[],[f695,f669,f439,f697,f177,f238,f103])).

fof(f103,plain,
    ( spl4_1
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f238,plain,
    ( spl4_17
  <=> v2_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f177,plain,
    ( spl4_11
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f669,plain,
    ( spl4_76
  <=> r1_tarski(sK0,k1_relat_1(k2_funct_1(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_76])])).

fof(f695,plain,
    ( ~ r1_tarski(sK0,sK0)
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_43
    | spl4_76 ),
    inference(forward_demodulation,[],[f694,f441])).

fof(f694,plain,
    ( ~ r1_tarski(sK0,k2_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | spl4_76 ),
    inference(superposition,[],[f671,f68])).

fof(f68,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f671,plain,
    ( ~ r1_tarski(sK0,k1_relat_1(k2_funct_1(sK3)))
    | spl4_76 ),
    inference(avatar_component_clause,[],[f669])).

fof(f678,plain,
    ( ~ spl4_1
    | spl4_72 ),
    inference(avatar_contradiction_clause,[],[f676])).

fof(f676,plain,
    ( $false
    | ~ spl4_1
    | spl4_72 ),
    inference(unit_resulting_resolution,[],[f105,f45,f652,f66])).

fof(f66,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f652,plain,
    ( ~ v1_relat_1(k2_funct_1(sK3))
    | spl4_72 ),
    inference(avatar_component_clause,[],[f650])).

fof(f650,plain,
    ( spl4_72
  <=> v1_relat_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_72])])).

fof(f45,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f22])).

% (14165)Refutation not found, incomplete strategy% (14165)------------------------------
% (14165)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (14165)Termination reason: Refutation not found, incomplete strategy

% (14165)Memory used [KB]: 11001
% (14165)Time elapsed: 0.205 s
% (14165)------------------------------
% (14165)------------------------------
% (14154)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% (14153)Refutation not found, incomplete strategy% (14153)------------------------------
% (14153)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (14153)Termination reason: Refutation not found, incomplete strategy

% (14153)Memory used [KB]: 10746
% (14153)Time elapsed: 0.182 s
% (14153)------------------------------
% (14153)------------------------------
fof(f105,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f103])).

fof(f675,plain,
    ( ~ spl4_1
    | spl4_69 ),
    inference(avatar_contradiction_clause,[],[f673])).

fof(f673,plain,
    ( $false
    | ~ spl4_1
    | spl4_69 ),
    inference(unit_resulting_resolution,[],[f105,f45,f639,f67])).

fof(f67,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f639,plain,
    ( ~ v1_funct_1(k2_funct_1(sK3))
    | spl4_69 ),
    inference(avatar_component_clause,[],[f637])).

fof(f637,plain,
    ( spl4_69
  <=> v1_funct_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_69])])).

fof(f672,plain,
    ( ~ spl4_1
    | ~ spl4_72
    | spl4_19
    | ~ spl4_76
    | ~ spl4_43
    | ~ spl4_67 ),
    inference(avatar_split_clause,[],[f667,f598,f439,f669,f246,f650,f103])).

fof(f246,plain,
    ( spl4_19
  <=> sK1 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f598,plain,
    ( spl4_67
  <=> k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_67])])).

fof(f667,plain,
    ( ~ r1_tarski(sK0,k1_relat_1(k2_funct_1(sK3)))
    | sK1 = k1_relat_1(sK3)
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ spl4_43
    | ~ spl4_67 ),
    inference(forward_demodulation,[],[f666,f441])).

fof(f666,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ r1_tarski(k2_relat_1(sK3),k1_relat_1(k2_funct_1(sK3)))
    | ~ v1_relat_1(sK3)
    | ~ spl4_67 ),
    inference(forward_demodulation,[],[f635,f91])).

fof(f91,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f62,f57])).

fof(f57,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f62,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f635,plain,
    ( k1_relat_1(sK3) = k1_relat_1(k6_partfun1(sK1))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ r1_tarski(k2_relat_1(sK3),k1_relat_1(k2_funct_1(sK3)))
    | ~ v1_relat_1(sK3)
    | ~ spl4_67 ),
    inference(superposition,[],[f64,f600])).

fof(f600,plain,
    ( k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ spl4_67 ),
    inference(avatar_component_clause,[],[f598])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
           => k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).

fof(f665,plain,
    ( spl4_71
    | ~ spl4_72
    | ~ spl4_73
    | ~ spl4_11
    | ~ spl4_1
    | ~ spl4_69
    | ~ spl4_74
    | ~ spl4_75
    | ~ spl4_43
    | ~ spl4_67 ),
    inference(avatar_split_clause,[],[f644,f598,f439,f662,f658,f637,f103,f177,f654,f650,f646])).

fof(f644,plain,
    ( sK0 != k1_relat_1(k2_funct_1(sK3))
    | k6_partfun1(sK1) != k6_partfun1(k2_relat_1(k2_funct_1(sK3)))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | sK3 = k2_funct_1(k2_funct_1(sK3))
    | ~ spl4_43
    | ~ spl4_67 ),
    inference(forward_demodulation,[],[f634,f441])).

fof(f634,plain,
    ( k6_partfun1(sK1) != k6_partfun1(k2_relat_1(k2_funct_1(sK3)))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(k2_funct_1(sK3))
    | k2_relat_1(sK3) != k1_relat_1(k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | sK3 = k2_funct_1(k2_funct_1(sK3))
    | ~ spl4_67 ),
    inference(superposition,[],[f92,f600])).

fof(f92,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(X0)
      | k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k2_funct_1(X0) = X1 ) ),
    inference(definition_unfolding,[],[f70,f57])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(X0)
      | k1_relat_1(X0) != k2_relat_1(X1)
      | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
      | k2_funct_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0))
              & k1_relat_1(X0) = k2_relat_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_1)).

fof(f627,plain,(
    ~ spl4_50 ),
    inference(avatar_contradiction_clause,[],[f607])).

fof(f607,plain,
    ( $false
    | ~ spl4_50 ),
    inference(subsumption_resolution,[],[f51,f498])).

fof(f498,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_50 ),
    inference(avatar_component_clause,[],[f496])).

fof(f496,plain,
    ( spl4_50
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_50])])).

fof(f51,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f22])).

fof(f601,plain,
    ( spl4_67
    | spl4_50
    | ~ spl4_17
    | ~ spl4_11
    | ~ spl4_10
    | ~ spl4_41
    | ~ spl4_40 ),
    inference(avatar_split_clause,[],[f436,f417,f421,f173,f177,f238,f496,f598])).

fof(f173,plain,
    ( spl4_10
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f421,plain,
    ( spl4_41
  <=> v1_funct_2(sK3,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).

fof(f417,plain,
    ( spl4_40
  <=> sK0 = k2_relset_1(sK1,sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).

fof(f436,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | k1_xboole_0 = sK0
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ spl4_40 ),
    inference(trivial_inequality_removal,[],[f434])).

fof(f434,plain,
    ( sK0 != sK0
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | k1_xboole_0 = sK0
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ spl4_40 ),
    inference(superposition,[],[f76,f419])).

fof(f419,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ spl4_40 ),
    inference(avatar_component_clause,[],[f417])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k1_xboole_0 = X1
      | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
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

fof(f596,plain,(
    spl4_65 ),
    inference(avatar_contradiction_clause,[],[f593])).

fof(f593,plain,
    ( $false
    | spl4_65 ),
    inference(unit_resulting_resolution,[],[f88,f587])).

fof(f587,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | spl4_65 ),
    inference(avatar_component_clause,[],[f585])).

fof(f585,plain,
    ( spl4_65
  <=> v2_funct_1(k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_65])])).

fof(f88,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f59,f57])).

fof(f59,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f588,plain,
    ( ~ spl4_41
    | ~ spl4_10
    | ~ spl4_11
    | spl4_50
    | spl4_17
    | ~ spl4_65
    | ~ spl4_8
    | ~ spl4_49 ),
    inference(avatar_split_clause,[],[f581,f489,f160,f585,f238,f496,f177,f173,f421])).

fof(f160,plain,
    ( spl4_8
  <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f489,plain,
    ( spl4_49
  <=> ! [X1,X0] :
        ( ~ v1_funct_1(X0)
        | v2_funct_1(X0)
        | k1_xboole_0 = X1
        | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X1,sK2,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
        | ~ v1_funct_2(X0,sK1,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_49])])).

fof(f581,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | v2_funct_1(sK3)
    | k1_xboole_0 = sK0
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ spl4_8
    | ~ spl4_49 ),
    inference(superposition,[],[f490,f162])).

fof(f162,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f160])).

fof(f490,plain,
    ( ! [X0,X1] :
        ( ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X1,sK2,X0))
        | v2_funct_1(X0)
        | k1_xboole_0 = X1
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
        | ~ v1_funct_2(X0,sK1,X1) )
    | ~ spl4_49 ),
    inference(avatar_component_clause,[],[f489])).

fof(f491,plain,
    ( ~ spl4_9
    | spl4_49
    | ~ spl4_5
    | ~ spl4_25 ),
    inference(avatar_split_clause,[],[f487,f278,f135,f489,f169])).

fof(f169,plain,
    ( spl4_9
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f135,plain,
    ( spl4_5
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f278,plain,
    ( spl4_25
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f487,plain,(
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
    inference(trivial_inequality_removal,[],[f482])).

fof(f482,plain,(
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
    inference(superposition,[],[f82,f48])).

fof(f48,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f82,plain,(
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
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f37,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
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

fof(f443,plain,
    ( ~ spl4_10
    | spl4_43
    | ~ spl4_40 ),
    inference(avatar_split_clause,[],[f435,f417,f439,f173])).

fof(f435,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_40 ),
    inference(superposition,[],[f75,f419])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f431,plain,(
    spl4_41 ),
    inference(avatar_contradiction_clause,[],[f430])).

fof(f430,plain,
    ( $false
    | spl4_41 ),
    inference(subsumption_resolution,[],[f46,f423])).

fof(f423,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | spl4_41 ),
    inference(avatar_component_clause,[],[f421])).

fof(f46,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f424,plain,
    ( spl4_40
    | ~ spl4_11
    | ~ spl4_5
    | ~ spl4_25
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_41 ),
    inference(avatar_split_clause,[],[f412,f421,f173,f169,f278,f135,f177,f417])).

fof(f412,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | sK0 = k2_relset_1(sK1,sK0,sK3) ),
    inference(resolution,[],[f78,f49])).

fof(f49,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X1,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_1(X2)
      | k2_relset_1(X0,X1,X2) = X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
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

fof(f359,plain,(
    spl4_34 ),
    inference(avatar_contradiction_clause,[],[f356])).

fof(f356,plain,
    ( $false
    | spl4_34 ),
    inference(unit_resulting_resolution,[],[f93,f354])).

fof(f354,plain,
    ( ~ r1_tarski(sK1,sK1)
    | spl4_34 ),
    inference(avatar_component_clause,[],[f352])).

fof(f352,plain,
    ( spl4_34
  <=> r1_tarski(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).

fof(f355,plain,
    ( ~ spl4_3
    | ~ spl4_24
    | ~ spl4_9
    | ~ spl4_34
    | ~ spl4_6
    | spl4_33 ),
    inference(avatar_split_clause,[],[f350,f340,f139,f352,f169,f274,f112])).

fof(f112,plain,
    ( spl4_3
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f274,plain,
    ( spl4_24
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f340,plain,
    ( spl4_33
  <=> r1_tarski(sK1,k1_relat_1(k2_funct_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).

fof(f350,plain,
    ( ~ r1_tarski(sK1,sK1)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_6
    | spl4_33 ),
    inference(forward_demodulation,[],[f349,f141])).

fof(f349,plain,
    ( ~ r1_tarski(sK1,k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl4_33 ),
    inference(superposition,[],[f342,f68])).

fof(f342,plain,
    ( ~ r1_tarski(sK1,k1_relat_1(k2_funct_1(sK2)))
    | spl4_33 ),
    inference(avatar_component_clause,[],[f340])).

fof(f346,plain,
    ( ~ spl4_3
    | spl4_28 ),
    inference(avatar_contradiction_clause,[],[f344])).

fof(f344,plain,
    ( $false
    | ~ spl4_3
    | spl4_28 ),
    inference(unit_resulting_resolution,[],[f114,f54,f319,f66])).

fof(f319,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | spl4_28 ),
    inference(avatar_component_clause,[],[f317])).

fof(f317,plain,
    ( spl4_28
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f54,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f114,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f112])).

fof(f343,plain,
    ( ~ spl4_3
    | ~ spl4_28
    | spl4_20
    | ~ spl4_33
    | ~ spl4_6
    | ~ spl4_22 ),
    inference(avatar_split_clause,[],[f338,f266,f139,f340,f253,f317,f112])).

fof(f266,plain,
    ( spl4_22
  <=> k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f338,plain,
    ( ~ r1_tarski(sK1,k1_relat_1(k2_funct_1(sK2)))
    | sK0 = k1_relat_1(sK2)
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl4_6
    | ~ spl4_22 ),
    inference(forward_demodulation,[],[f337,f141])).

fof(f337,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ r1_tarski(k2_relat_1(sK2),k1_relat_1(k2_funct_1(sK2)))
    | ~ v1_relat_1(sK2)
    | ~ spl4_22 ),
    inference(forward_demodulation,[],[f310,f91])).

fof(f310,plain,
    ( k1_relat_1(sK2) = k1_relat_1(k6_partfun1(sK0))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ r1_tarski(k2_relat_1(sK2),k1_relat_1(k2_funct_1(sK2)))
    | ~ v1_relat_1(sK2)
    | ~ spl4_22 ),
    inference(superposition,[],[f64,f268])).

fof(f268,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f266])).

fof(f308,plain,(
    ~ spl4_23 ),
    inference(avatar_contradiction_clause,[],[f295])).

fof(f295,plain,
    ( $false
    | ~ spl4_23 ),
    inference(subsumption_resolution,[],[f52,f272])).

fof(f272,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f270])).

fof(f270,plain,
    ( spl4_23
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f52,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f22])).

fof(f285,plain,(
    spl4_25 ),
    inference(avatar_contradiction_clause,[],[f284])).

fof(f284,plain,
    ( $false
    | spl4_25 ),
    inference(subsumption_resolution,[],[f55,f280])).

fof(f280,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | spl4_25 ),
    inference(avatar_component_clause,[],[f278])).

fof(f55,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f283,plain,(
    spl4_24 ),
    inference(avatar_contradiction_clause,[],[f282])).

fof(f282,plain,
    ( $false
    | spl4_24 ),
    inference(subsumption_resolution,[],[f50,f276])).

fof(f276,plain,
    ( ~ v2_funct_1(sK2)
    | spl4_24 ),
    inference(avatar_component_clause,[],[f274])).

fof(f281,plain,
    ( spl4_22
    | spl4_23
    | ~ spl4_24
    | ~ spl4_9
    | ~ spl4_5
    | ~ spl4_25 ),
    inference(avatar_split_clause,[],[f264,f278,f135,f169,f274,f270,f266])).

fof(f264,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k1_xboole_0 = sK1
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(trivial_inequality_removal,[],[f261])).

fof(f261,plain,
    ( sK1 != sK1
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k1_xboole_0 = sK1
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(superposition,[],[f76,f48])).

fof(f249,plain,
    ( spl4_16
    | ~ spl4_1
    | ~ spl4_17
    | ~ spl4_9
    | ~ spl4_3
    | ~ spl4_11
    | ~ spl4_18
    | ~ spl4_19
    | ~ spl4_6
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f232,f212,f139,f246,f242,f177,f112,f169,f238,f103,f234])).

fof(f212,plain,
    ( spl4_14
  <=> k6_partfun1(sK0) = k5_relat_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f232,plain,
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
    inference(forward_demodulation,[],[f230,f141])).

fof(f230,plain,
    ( k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK3)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_relat_1(sK3)
    | sK2 = k2_funct_1(sK3)
    | ~ spl4_14 ),
    inference(superposition,[],[f92,f214])).

fof(f214,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f212])).

fof(f222,plain,
    ( ~ spl4_9
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_5
    | spl4_14
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f219,f160,f212,f135,f177,f173,f169])).

fof(f219,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_8 ),
    inference(superposition,[],[f85,f162])).

fof(f85,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f205,plain,(
    spl4_11 ),
    inference(avatar_contradiction_clause,[],[f204])).

fof(f204,plain,
    ( $false
    | spl4_11 ),
    inference(subsumption_resolution,[],[f45,f179])).

fof(f179,plain,
    ( ~ v1_funct_1(sK3)
    | spl4_11 ),
    inference(avatar_component_clause,[],[f177])).

fof(f203,plain,(
    spl4_10 ),
    inference(avatar_contradiction_clause,[],[f202])).

fof(f202,plain,
    ( $false
    | spl4_10 ),
    inference(subsumption_resolution,[],[f47,f175])).

fof(f175,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl4_10 ),
    inference(avatar_component_clause,[],[f173])).

fof(f47,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f22])).

fof(f201,plain,(
    spl4_9 ),
    inference(avatar_contradiction_clause,[],[f200])).

fof(f200,plain,
    ( $false
    | spl4_9 ),
    inference(subsumption_resolution,[],[f54,f171])).

fof(f171,plain,
    ( ~ v1_funct_1(sK2)
    | spl4_9 ),
    inference(avatar_component_clause,[],[f169])).

fof(f199,plain,(
    spl4_7 ),
    inference(avatar_contradiction_clause,[],[f190])).

fof(f190,plain,
    ( $false
    | spl4_7 ),
    inference(unit_resulting_resolution,[],[f54,f45,f47,f56,f158,f87])).

fof(f87,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
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
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f158,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl4_7 ),
    inference(avatar_component_clause,[],[f156])).

fof(f156,plain,
    ( spl4_7
  <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f56,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f22])).

fof(f163,plain,
    ( ~ spl4_7
    | spl4_8 ),
    inference(avatar_split_clause,[],[f153,f160,f156])).

fof(f153,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
    | ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f149,f49])).

fof(f149,plain,(
    ! [X2,X1] :
      ( ~ r2_relset_1(X2,X2,X1,k6_partfun1(X2))
      | k6_partfun1(X2) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ) ),
    inference(resolution,[],[f84,f61])).

fof(f61,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f145,plain,(
    spl4_5 ),
    inference(avatar_contradiction_clause,[],[f144])).

fof(f144,plain,
    ( $false
    | spl4_5 ),
    inference(subsumption_resolution,[],[f56,f137])).

fof(f137,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl4_5 ),
    inference(avatar_component_clause,[],[f135])).

fof(f143,plain,
    ( ~ spl4_5
    | spl4_6 ),
    inference(avatar_split_clause,[],[f133,f139,f135])).

fof(f133,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f48,f75])).

fof(f128,plain,(
    spl4_4 ),
    inference(avatar_contradiction_clause,[],[f125])).

fof(f125,plain,
    ( $false
    | spl4_4 ),
    inference(unit_resulting_resolution,[],[f71,f118])).

fof(f118,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | spl4_4 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl4_4
  <=> v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f71,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f123,plain,(
    spl4_2 ),
    inference(avatar_contradiction_clause,[],[f120])).

fof(f120,plain,
    ( $false
    | spl4_2 ),
    inference(unit_resulting_resolution,[],[f71,f109])).

fof(f109,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | spl4_2 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl4_2
  <=> v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f119,plain,
    ( spl4_3
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f100,f116,f112])).

fof(f100,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK2) ),
    inference(resolution,[],[f65,f56])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f110,plain,
    ( spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f99,f107,f103])).

fof(f99,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | v1_relat_1(sK3) ),
    inference(resolution,[],[f65,f47])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:39:50 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.54  % (14138)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.54  % (14160)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.54  % (14143)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (14152)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.56  % (14144)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.57  % (14140)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.57  % (14141)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.40/0.57  % (14150)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.40/0.57  % (14162)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.40/0.58  % (14139)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.40/0.58  % (14155)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.40/0.58  % (14142)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.40/0.58  % (14159)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.40/0.58  % (14147)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.76/0.59  % (14151)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.76/0.59  % (14137)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.76/0.59  % (14164)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.76/0.60  % (14165)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.76/0.60  % (14161)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.76/0.61  % (14153)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.76/0.61  % (14157)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.76/0.61  % (14146)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.76/0.61  % (14156)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.76/0.61  % (14147)Refutation not found, incomplete strategy% (14147)------------------------------
% 1.76/0.61  % (14147)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.76/0.61  % (14147)Termination reason: Refutation not found, incomplete strategy
% 1.76/0.61  
% 1.76/0.61  % (14147)Memory used [KB]: 11001
% 1.76/0.61  % (14147)Time elapsed: 0.166 s
% 1.76/0.61  % (14147)------------------------------
% 1.76/0.61  % (14147)------------------------------
% 1.76/0.61  % (14166)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.76/0.61  % (14163)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.76/0.61  % (14149)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.76/0.61  % (14145)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.76/0.61  % (14148)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.76/0.62  % (14158)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.76/0.63  % (14150)Refutation found. Thanks to Tanya!
% 1.76/0.63  % SZS status Theorem for theBenchmark
% 1.76/0.63  % SZS output start Proof for theBenchmark
% 1.76/0.63  fof(f770,plain,(
% 1.76/0.63    $false),
% 1.76/0.63    inference(avatar_sat_refutation,[],[f110,f119,f123,f128,f143,f145,f163,f199,f201,f203,f205,f222,f249,f281,f283,f285,f308,f343,f346,f355,f359,f424,f431,f443,f491,f588,f596,f601,f627,f665,f672,f675,f678,f700,f704,f707,f720,f724,f751,f766])).
% 1.76/0.63  fof(f766,plain,(
% 1.76/0.63    ~spl4_16 | ~spl4_71),
% 1.76/0.63    inference(avatar_contradiction_clause,[],[f754])).
% 1.76/0.63  fof(f754,plain,(
% 1.76/0.63    $false | (~spl4_16 | ~spl4_71)),
% 1.76/0.63    inference(subsumption_resolution,[],[f53,f753])).
% 1.76/0.63  fof(f753,plain,(
% 1.76/0.63    sK3 = k2_funct_1(sK2) | (~spl4_16 | ~spl4_71)),
% 1.76/0.63    inference(forward_demodulation,[],[f648,f236])).
% 1.76/0.63  fof(f236,plain,(
% 1.76/0.63    sK2 = k2_funct_1(sK3) | ~spl4_16),
% 1.76/0.63    inference(avatar_component_clause,[],[f234])).
% 1.76/0.63  fof(f234,plain,(
% 1.76/0.63    spl4_16 <=> sK2 = k2_funct_1(sK3)),
% 1.76/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 1.76/0.63  fof(f648,plain,(
% 1.76/0.63    sK3 = k2_funct_1(k2_funct_1(sK3)) | ~spl4_71),
% 1.76/0.63    inference(avatar_component_clause,[],[f646])).
% 1.76/0.63  fof(f646,plain,(
% 1.76/0.63    spl4_71 <=> sK3 = k2_funct_1(k2_funct_1(sK3))),
% 1.76/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_71])])).
% 1.76/0.63  fof(f53,plain,(
% 1.76/0.63    sK3 != k2_funct_1(sK2)),
% 1.76/0.63    inference(cnf_transformation,[],[f22])).
% 1.76/0.63  fof(f22,plain,(
% 1.76/0.63    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.76/0.63    inference(flattening,[],[f21])).
% 1.76/0.63  fof(f21,plain,(
% 1.76/0.63    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.76/0.63    inference(ennf_transformation,[],[f20])).
% 1.76/0.63  fof(f20,negated_conjecture,(
% 1.76/0.63    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.76/0.63    inference(negated_conjecture,[],[f19])).
% 1.76/0.63  fof(f19,conjecture,(
% 1.76/0.63    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.76/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).
% 1.76/0.63  fof(f751,plain,(
% 1.76/0.63    ~spl4_16 | ~spl4_20 | spl4_75),
% 1.76/0.63    inference(avatar_contradiction_clause,[],[f750])).
% 1.76/0.63  fof(f750,plain,(
% 1.76/0.63    $false | (~spl4_16 | ~spl4_20 | spl4_75)),
% 1.76/0.63    inference(subsumption_resolution,[],[f255,f726])).
% 1.76/0.63  fof(f726,plain,(
% 1.76/0.63    sK0 != k1_relat_1(sK2) | (~spl4_16 | spl4_75)),
% 1.76/0.63    inference(forward_demodulation,[],[f664,f236])).
% 1.76/0.63  fof(f664,plain,(
% 1.76/0.63    sK0 != k1_relat_1(k2_funct_1(sK3)) | spl4_75),
% 1.76/0.63    inference(avatar_component_clause,[],[f662])).
% 1.76/0.63  fof(f662,plain,(
% 1.76/0.63    spl4_75 <=> sK0 = k1_relat_1(k2_funct_1(sK3))),
% 1.76/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_75])])).
% 1.76/0.63  fof(f255,plain,(
% 1.76/0.63    sK0 = k1_relat_1(sK2) | ~spl4_20),
% 1.76/0.63    inference(avatar_component_clause,[],[f253])).
% 1.76/0.63  fof(f253,plain,(
% 1.76/0.63    spl4_20 <=> sK0 = k1_relat_1(sK2)),
% 1.76/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 1.76/0.63  fof(f724,plain,(
% 1.76/0.63    ~spl4_6 | ~spl4_16 | spl4_74),
% 1.76/0.63    inference(avatar_contradiction_clause,[],[f723])).
% 1.76/0.63  fof(f723,plain,(
% 1.76/0.63    $false | (~spl4_6 | ~spl4_16 | spl4_74)),
% 1.76/0.63    inference(trivial_inequality_removal,[],[f722])).
% 1.76/0.63  fof(f722,plain,(
% 1.76/0.63    k6_partfun1(sK1) != k6_partfun1(sK1) | (~spl4_6 | ~spl4_16 | spl4_74)),
% 1.76/0.63    inference(forward_demodulation,[],[f721,f141])).
% 1.76/0.63  fof(f141,plain,(
% 1.76/0.63    sK1 = k2_relat_1(sK2) | ~spl4_6),
% 1.76/0.63    inference(avatar_component_clause,[],[f139])).
% 1.76/0.63  fof(f139,plain,(
% 1.76/0.63    spl4_6 <=> sK1 = k2_relat_1(sK2)),
% 1.76/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.76/0.63  fof(f721,plain,(
% 1.76/0.63    k6_partfun1(k2_relat_1(sK2)) != k6_partfun1(sK1) | (~spl4_16 | spl4_74)),
% 1.76/0.63    inference(forward_demodulation,[],[f660,f236])).
% 1.76/0.63  fof(f660,plain,(
% 1.76/0.63    k6_partfun1(sK1) != k6_partfun1(k2_relat_1(k2_funct_1(sK3))) | spl4_74),
% 1.76/0.63    inference(avatar_component_clause,[],[f658])).
% 1.76/0.63  fof(f658,plain,(
% 1.76/0.63    spl4_74 <=> k6_partfun1(sK1) = k6_partfun1(k2_relat_1(k2_funct_1(sK3)))),
% 1.76/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_74])])).
% 1.76/0.63  fof(f720,plain,(
% 1.76/0.63    ~spl4_16 | spl4_73),
% 1.76/0.63    inference(avatar_contradiction_clause,[],[f719])).
% 1.76/0.63  fof(f719,plain,(
% 1.76/0.63    $false | (~spl4_16 | spl4_73)),
% 1.76/0.63    inference(subsumption_resolution,[],[f50,f708])).
% 1.76/0.63  fof(f708,plain,(
% 1.76/0.63    ~v2_funct_1(sK2) | (~spl4_16 | spl4_73)),
% 1.76/0.63    inference(superposition,[],[f656,f236])).
% 1.76/0.63  fof(f656,plain,(
% 1.76/0.63    ~v2_funct_1(k2_funct_1(sK3)) | spl4_73),
% 1.76/0.63    inference(avatar_component_clause,[],[f654])).
% 1.76/0.63  fof(f654,plain,(
% 1.76/0.63    spl4_73 <=> v2_funct_1(k2_funct_1(sK3))),
% 1.76/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_73])])).
% 1.76/0.63  fof(f50,plain,(
% 1.76/0.63    v2_funct_1(sK2)),
% 1.76/0.63    inference(cnf_transformation,[],[f22])).
% 1.76/0.63  fof(f707,plain,(
% 1.76/0.63    spl4_18 | ~spl4_43),
% 1.76/0.63    inference(avatar_contradiction_clause,[],[f706])).
% 1.76/0.63  fof(f706,plain,(
% 1.76/0.63    $false | (spl4_18 | ~spl4_43)),
% 1.76/0.63    inference(trivial_inequality_removal,[],[f705])).
% 1.76/0.63  fof(f705,plain,(
% 1.76/0.63    k6_partfun1(sK0) != k6_partfun1(sK0) | (spl4_18 | ~spl4_43)),
% 1.76/0.63    inference(forward_demodulation,[],[f244,f441])).
% 1.76/0.63  fof(f441,plain,(
% 1.76/0.63    sK0 = k2_relat_1(sK3) | ~spl4_43),
% 1.76/0.63    inference(avatar_component_clause,[],[f439])).
% 1.76/0.63  fof(f439,plain,(
% 1.76/0.63    spl4_43 <=> sK0 = k2_relat_1(sK3)),
% 1.76/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).
% 1.76/0.63  fof(f244,plain,(
% 1.76/0.63    k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3)) | spl4_18),
% 1.76/0.63    inference(avatar_component_clause,[],[f242])).
% 1.76/0.63  fof(f242,plain,(
% 1.76/0.63    spl4_18 <=> k6_partfun1(sK0) = k6_partfun1(k2_relat_1(sK3))),
% 1.76/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 1.76/0.63  fof(f704,plain,(
% 1.76/0.63    spl4_79),
% 1.76/0.63    inference(avatar_contradiction_clause,[],[f701])).
% 1.76/0.63  fof(f701,plain,(
% 1.76/0.63    $false | spl4_79),
% 1.76/0.63    inference(unit_resulting_resolution,[],[f93,f699])).
% 1.76/0.63  fof(f699,plain,(
% 1.76/0.63    ~r1_tarski(sK0,sK0) | spl4_79),
% 1.76/0.63    inference(avatar_component_clause,[],[f697])).
% 1.76/0.63  fof(f697,plain,(
% 1.76/0.63    spl4_79 <=> r1_tarski(sK0,sK0)),
% 1.76/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_79])])).
% 1.76/0.63  fof(f93,plain,(
% 1.76/0.63    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.76/0.63    inference(equality_resolution,[],[f73])).
% 1.76/0.63  fof(f73,plain,(
% 1.76/0.63    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.76/0.63    inference(cnf_transformation,[],[f1])).
% 1.76/0.63  fof(f1,axiom,(
% 1.76/0.63    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.76/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.76/0.63  fof(f700,plain,(
% 1.76/0.63    ~spl4_1 | ~spl4_17 | ~spl4_11 | ~spl4_79 | ~spl4_43 | spl4_76),
% 1.76/0.63    inference(avatar_split_clause,[],[f695,f669,f439,f697,f177,f238,f103])).
% 1.76/0.63  fof(f103,plain,(
% 1.76/0.63    spl4_1 <=> v1_relat_1(sK3)),
% 1.76/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.76/0.63  fof(f238,plain,(
% 1.76/0.63    spl4_17 <=> v2_funct_1(sK3)),
% 1.76/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 1.76/0.63  fof(f177,plain,(
% 1.76/0.63    spl4_11 <=> v1_funct_1(sK3)),
% 1.76/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 1.76/0.63  fof(f669,plain,(
% 1.76/0.63    spl4_76 <=> r1_tarski(sK0,k1_relat_1(k2_funct_1(sK3)))),
% 1.76/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_76])])).
% 1.76/0.63  fof(f695,plain,(
% 1.76/0.63    ~r1_tarski(sK0,sK0) | ~v1_funct_1(sK3) | ~v2_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl4_43 | spl4_76)),
% 1.76/0.63    inference(forward_demodulation,[],[f694,f441])).
% 1.76/0.63  fof(f694,plain,(
% 1.76/0.63    ~r1_tarski(sK0,k2_relat_1(sK3)) | ~v1_funct_1(sK3) | ~v2_funct_1(sK3) | ~v1_relat_1(sK3) | spl4_76),
% 1.76/0.63    inference(superposition,[],[f671,f68])).
% 1.76/0.63  fof(f68,plain,(
% 1.76/0.63    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.76/0.63    inference(cnf_transformation,[],[f29])).
% 1.76/0.63  fof(f29,plain,(
% 1.76/0.63    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.76/0.63    inference(flattening,[],[f28])).
% 1.76/0.63  fof(f28,plain,(
% 1.76/0.63    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.76/0.63    inference(ennf_transformation,[],[f8])).
% 1.76/0.63  fof(f8,axiom,(
% 1.76/0.63    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 1.76/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 1.76/0.63  fof(f671,plain,(
% 1.76/0.63    ~r1_tarski(sK0,k1_relat_1(k2_funct_1(sK3))) | spl4_76),
% 1.76/0.63    inference(avatar_component_clause,[],[f669])).
% 1.76/0.63  fof(f678,plain,(
% 1.76/0.63    ~spl4_1 | spl4_72),
% 1.76/0.63    inference(avatar_contradiction_clause,[],[f676])).
% 1.76/0.63  fof(f676,plain,(
% 1.76/0.63    $false | (~spl4_1 | spl4_72)),
% 1.76/0.63    inference(unit_resulting_resolution,[],[f105,f45,f652,f66])).
% 1.76/0.63  fof(f66,plain,(
% 1.76/0.63    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.76/0.63    inference(cnf_transformation,[],[f27])).
% 1.76/0.63  fof(f27,plain,(
% 1.76/0.63    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.76/0.63    inference(flattening,[],[f26])).
% 1.76/0.63  fof(f26,plain,(
% 1.76/0.63    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.76/0.63    inference(ennf_transformation,[],[f6])).
% 1.76/0.63  fof(f6,axiom,(
% 1.76/0.63    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 1.76/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 1.76/0.63  fof(f652,plain,(
% 1.76/0.63    ~v1_relat_1(k2_funct_1(sK3)) | spl4_72),
% 1.76/0.63    inference(avatar_component_clause,[],[f650])).
% 1.76/0.63  fof(f650,plain,(
% 1.76/0.63    spl4_72 <=> v1_relat_1(k2_funct_1(sK3))),
% 1.76/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_72])])).
% 1.76/0.63  fof(f45,plain,(
% 1.76/0.63    v1_funct_1(sK3)),
% 1.76/0.63    inference(cnf_transformation,[],[f22])).
% 1.76/0.63  % (14165)Refutation not found, incomplete strategy% (14165)------------------------------
% 1.76/0.63  % (14165)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.76/0.63  % (14165)Termination reason: Refutation not found, incomplete strategy
% 1.76/0.63  
% 1.76/0.63  % (14165)Memory used [KB]: 11001
% 1.76/0.63  % (14165)Time elapsed: 0.205 s
% 1.76/0.63  % (14165)------------------------------
% 1.76/0.63  % (14165)------------------------------
% 1.76/0.63  % (14154)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.76/0.63  % (14153)Refutation not found, incomplete strategy% (14153)------------------------------
% 1.76/0.63  % (14153)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.76/0.63  % (14153)Termination reason: Refutation not found, incomplete strategy
% 1.76/0.63  
% 1.76/0.63  % (14153)Memory used [KB]: 10746
% 1.76/0.63  % (14153)Time elapsed: 0.182 s
% 1.76/0.63  % (14153)------------------------------
% 1.76/0.63  % (14153)------------------------------
% 1.76/0.65  fof(f105,plain,(
% 1.76/0.65    v1_relat_1(sK3) | ~spl4_1),
% 1.76/0.65    inference(avatar_component_clause,[],[f103])).
% 1.76/0.65  fof(f675,plain,(
% 1.76/0.65    ~spl4_1 | spl4_69),
% 1.76/0.65    inference(avatar_contradiction_clause,[],[f673])).
% 1.76/0.65  fof(f673,plain,(
% 1.76/0.65    $false | (~spl4_1 | spl4_69)),
% 1.76/0.65    inference(unit_resulting_resolution,[],[f105,f45,f639,f67])).
% 1.76/0.65  fof(f67,plain,(
% 1.76/0.65    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.76/0.65    inference(cnf_transformation,[],[f27])).
% 1.76/0.65  fof(f639,plain,(
% 1.76/0.65    ~v1_funct_1(k2_funct_1(sK3)) | spl4_69),
% 1.76/0.65    inference(avatar_component_clause,[],[f637])).
% 1.76/0.65  fof(f637,plain,(
% 1.76/0.65    spl4_69 <=> v1_funct_1(k2_funct_1(sK3))),
% 1.76/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_69])])).
% 1.76/0.65  fof(f672,plain,(
% 1.76/0.65    ~spl4_1 | ~spl4_72 | spl4_19 | ~spl4_76 | ~spl4_43 | ~spl4_67),
% 1.76/0.65    inference(avatar_split_clause,[],[f667,f598,f439,f669,f246,f650,f103])).
% 1.76/0.65  fof(f246,plain,(
% 1.76/0.65    spl4_19 <=> sK1 = k1_relat_1(sK3)),
% 1.76/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 1.76/0.65  fof(f598,plain,(
% 1.76/0.65    spl4_67 <=> k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))),
% 1.76/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_67])])).
% 1.76/0.65  fof(f667,plain,(
% 1.76/0.65    ~r1_tarski(sK0,k1_relat_1(k2_funct_1(sK3))) | sK1 = k1_relat_1(sK3) | ~v1_relat_1(k2_funct_1(sK3)) | ~v1_relat_1(sK3) | (~spl4_43 | ~spl4_67)),
% 1.76/0.65    inference(forward_demodulation,[],[f666,f441])).
% 1.76/0.65  fof(f666,plain,(
% 1.76/0.65    sK1 = k1_relat_1(sK3) | ~v1_relat_1(k2_funct_1(sK3)) | ~r1_tarski(k2_relat_1(sK3),k1_relat_1(k2_funct_1(sK3))) | ~v1_relat_1(sK3) | ~spl4_67),
% 1.76/0.65    inference(forward_demodulation,[],[f635,f91])).
% 1.76/0.65  fof(f91,plain,(
% 1.76/0.65    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 1.76/0.65    inference(definition_unfolding,[],[f62,f57])).
% 1.76/0.65  fof(f57,plain,(
% 1.76/0.65    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.76/0.65    inference(cnf_transformation,[],[f15])).
% 1.76/0.65  fof(f15,axiom,(
% 1.76/0.65    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.76/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.76/0.65  fof(f62,plain,(
% 1.76/0.65    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.76/0.65    inference(cnf_transformation,[],[f5])).
% 1.76/0.65  fof(f5,axiom,(
% 1.76/0.65    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.76/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 1.76/0.65  fof(f635,plain,(
% 1.76/0.65    k1_relat_1(sK3) = k1_relat_1(k6_partfun1(sK1)) | ~v1_relat_1(k2_funct_1(sK3)) | ~r1_tarski(k2_relat_1(sK3),k1_relat_1(k2_funct_1(sK3))) | ~v1_relat_1(sK3) | ~spl4_67),
% 1.76/0.65    inference(superposition,[],[f64,f600])).
% 1.76/0.65  fof(f600,plain,(
% 1.76/0.65    k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~spl4_67),
% 1.76/0.65    inference(avatar_component_clause,[],[f598])).
% 1.76/0.65  fof(f64,plain,(
% 1.76/0.65    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) | ~v1_relat_1(X1) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X0)) )),
% 1.76/0.65    inference(cnf_transformation,[],[f24])).
% 1.76/0.65  fof(f24,plain,(
% 1.76/0.65    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.76/0.65    inference(flattening,[],[f23])).
% 1.76/0.65  fof(f23,plain,(
% 1.76/0.65    ! [X0] : (! [X1] : ((k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.76/0.65    inference(ennf_transformation,[],[f4])).
% 1.76/0.65  fof(f4,axiom,(
% 1.76/0.65    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) => k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0))))),
% 1.76/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).
% 1.76/0.65  fof(f665,plain,(
% 1.76/0.65    spl4_71 | ~spl4_72 | ~spl4_73 | ~spl4_11 | ~spl4_1 | ~spl4_69 | ~spl4_74 | ~spl4_75 | ~spl4_43 | ~spl4_67),
% 1.76/0.65    inference(avatar_split_clause,[],[f644,f598,f439,f662,f658,f637,f103,f177,f654,f650,f646])).
% 1.76/0.65  fof(f644,plain,(
% 1.76/0.65    sK0 != k1_relat_1(k2_funct_1(sK3)) | k6_partfun1(sK1) != k6_partfun1(k2_relat_1(k2_funct_1(sK3))) | ~v1_funct_1(k2_funct_1(sK3)) | ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v2_funct_1(k2_funct_1(sK3)) | ~v1_relat_1(k2_funct_1(sK3)) | sK3 = k2_funct_1(k2_funct_1(sK3)) | (~spl4_43 | ~spl4_67)),
% 1.76/0.65    inference(forward_demodulation,[],[f634,f441])).
% 1.76/0.65  fof(f634,plain,(
% 1.76/0.65    k6_partfun1(sK1) != k6_partfun1(k2_relat_1(k2_funct_1(sK3))) | ~v1_funct_1(k2_funct_1(sK3)) | ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v2_funct_1(k2_funct_1(sK3)) | k2_relat_1(sK3) != k1_relat_1(k2_funct_1(sK3)) | ~v1_relat_1(k2_funct_1(sK3)) | sK3 = k2_funct_1(k2_funct_1(sK3)) | ~spl4_67),
% 1.76/0.65    inference(superposition,[],[f92,f600])).
% 1.76/0.65  fof(f92,plain,(
% 1.76/0.65    ( ! [X0,X1] : (k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v1_relat_1(X0) | k2_funct_1(X0) = X1) )),
% 1.76/0.65    inference(definition_unfolding,[],[f70,f57])).
% 1.76/0.65  fof(f70,plain,(
% 1.76/0.65    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(X0) | k1_relat_1(X0) != k2_relat_1(X1) | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k2_funct_1(X0) = X1) )),
% 1.76/0.65    inference(cnf_transformation,[],[f31])).
% 1.76/0.65  fof(f31,plain,(
% 1.76/0.65    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.76/0.65    inference(flattening,[],[f30])).
% 1.76/0.65  fof(f30,plain,(
% 1.76/0.65    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.76/0.65    inference(ennf_transformation,[],[f9])).
% 1.76/0.65  fof(f9,axiom,(
% 1.76/0.65    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0)) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 1.76/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_1)).
% 1.76/0.65  fof(f627,plain,(
% 1.76/0.65    ~spl4_50),
% 1.76/0.65    inference(avatar_contradiction_clause,[],[f607])).
% 1.76/0.65  fof(f607,plain,(
% 1.76/0.65    $false | ~spl4_50),
% 1.76/0.65    inference(subsumption_resolution,[],[f51,f498])).
% 1.76/0.65  fof(f498,plain,(
% 1.76/0.65    k1_xboole_0 = sK0 | ~spl4_50),
% 1.76/0.65    inference(avatar_component_clause,[],[f496])).
% 1.76/0.65  fof(f496,plain,(
% 1.76/0.65    spl4_50 <=> k1_xboole_0 = sK0),
% 1.76/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_50])])).
% 1.76/0.65  fof(f51,plain,(
% 1.76/0.65    k1_xboole_0 != sK0),
% 1.76/0.65    inference(cnf_transformation,[],[f22])).
% 1.76/0.65  fof(f601,plain,(
% 1.76/0.65    spl4_67 | spl4_50 | ~spl4_17 | ~spl4_11 | ~spl4_10 | ~spl4_41 | ~spl4_40),
% 1.76/0.65    inference(avatar_split_clause,[],[f436,f417,f421,f173,f177,f238,f496,f598])).
% 1.76/0.65  fof(f173,plain,(
% 1.76/0.65    spl4_10 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.76/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 1.76/0.65  fof(f421,plain,(
% 1.76/0.65    spl4_41 <=> v1_funct_2(sK3,sK1,sK0)),
% 1.76/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).
% 1.76/0.65  fof(f417,plain,(
% 1.76/0.65    spl4_40 <=> sK0 = k2_relset_1(sK1,sK0,sK3)),
% 1.76/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).
% 1.76/0.65  fof(f436,plain,(
% 1.76/0.65    ~v1_funct_2(sK3,sK1,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~v2_funct_1(sK3) | k1_xboole_0 = sK0 | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~spl4_40),
% 1.76/0.65    inference(trivial_inequality_removal,[],[f434])).
% 1.76/0.65  fof(f434,plain,(
% 1.76/0.65    sK0 != sK0 | ~v1_funct_2(sK3,sK1,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~v2_funct_1(sK3) | k1_xboole_0 = sK0 | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~spl4_40),
% 1.76/0.65    inference(superposition,[],[f76,f419])).
% 1.76/0.65  fof(f419,plain,(
% 1.76/0.65    sK0 = k2_relset_1(sK1,sK0,sK3) | ~spl4_40),
% 1.76/0.65    inference(avatar_component_clause,[],[f417])).
% 1.76/0.65  fof(f76,plain,(
% 1.76/0.65    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v2_funct_1(X2) | k1_xboole_0 = X1 | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) )),
% 1.76/0.65    inference(cnf_transformation,[],[f34])).
% 1.76/0.65  fof(f34,plain,(
% 1.76/0.65    ! [X0,X1,X2] : ((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.76/0.65    inference(flattening,[],[f33])).
% 1.76/0.65  fof(f33,plain,(
% 1.76/0.65    ! [X0,X1,X2] : ((((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.76/0.65    inference(ennf_transformation,[],[f18])).
% 1.76/0.65  fof(f18,axiom,(
% 1.76/0.65    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1)))),
% 1.76/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_2)).
% 1.76/0.65  fof(f596,plain,(
% 1.76/0.65    spl4_65),
% 1.76/0.65    inference(avatar_contradiction_clause,[],[f593])).
% 1.76/0.65  fof(f593,plain,(
% 1.76/0.65    $false | spl4_65),
% 1.76/0.65    inference(unit_resulting_resolution,[],[f88,f587])).
% 1.76/0.65  fof(f587,plain,(
% 1.76/0.65    ~v2_funct_1(k6_partfun1(sK0)) | spl4_65),
% 1.76/0.65    inference(avatar_component_clause,[],[f585])).
% 1.76/0.65  fof(f585,plain,(
% 1.76/0.65    spl4_65 <=> v2_funct_1(k6_partfun1(sK0))),
% 1.76/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_65])])).
% 1.76/0.65  fof(f88,plain,(
% 1.76/0.65    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 1.76/0.65    inference(definition_unfolding,[],[f59,f57])).
% 1.76/0.65  fof(f59,plain,(
% 1.76/0.65    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 1.76/0.65    inference(cnf_transformation,[],[f7])).
% 1.76/0.65  fof(f7,axiom,(
% 1.76/0.65    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.76/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).
% 1.76/0.65  fof(f588,plain,(
% 1.76/0.65    ~spl4_41 | ~spl4_10 | ~spl4_11 | spl4_50 | spl4_17 | ~spl4_65 | ~spl4_8 | ~spl4_49),
% 1.76/0.65    inference(avatar_split_clause,[],[f581,f489,f160,f585,f238,f496,f177,f173,f421])).
% 1.76/0.65  fof(f160,plain,(
% 1.76/0.65    spl4_8 <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)),
% 1.76/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 1.76/0.65  fof(f489,plain,(
% 1.76/0.65    spl4_49 <=> ! [X1,X0] : (~v1_funct_1(X0) | v2_funct_1(X0) | k1_xboole_0 = X1 | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X1,sK2,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) | ~v1_funct_2(X0,sK1,X1))),
% 1.76/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_49])])).
% 1.76/0.65  fof(f581,plain,(
% 1.76/0.65    ~v2_funct_1(k6_partfun1(sK0)) | v2_funct_1(sK3) | k1_xboole_0 = sK0 | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | (~spl4_8 | ~spl4_49)),
% 1.76/0.65    inference(superposition,[],[f490,f162])).
% 1.76/0.65  fof(f162,plain,(
% 1.76/0.65    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) | ~spl4_8),
% 1.76/0.65    inference(avatar_component_clause,[],[f160])).
% 1.76/0.65  fof(f490,plain,(
% 1.76/0.65    ( ! [X0,X1] : (~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X1,sK2,X0)) | v2_funct_1(X0) | k1_xboole_0 = X1 | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) | ~v1_funct_2(X0,sK1,X1)) ) | ~spl4_49),
% 1.76/0.65    inference(avatar_component_clause,[],[f489])).
% 1.76/0.65  fof(f491,plain,(
% 1.76/0.65    ~spl4_9 | spl4_49 | ~spl4_5 | ~spl4_25),
% 1.76/0.65    inference(avatar_split_clause,[],[f487,f278,f135,f489,f169])).
% 1.76/0.65  fof(f169,plain,(
% 1.76/0.65    spl4_9 <=> v1_funct_1(sK2)),
% 1.76/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 1.76/0.65  fof(f135,plain,(
% 1.76/0.65    spl4_5 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.76/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.76/0.65  fof(f278,plain,(
% 1.76/0.65    spl4_25 <=> v1_funct_2(sK2,sK0,sK1)),
% 1.76/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 1.76/0.65  fof(f487,plain,(
% 1.76/0.65    ( ! [X0,X1] : (~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(X0) | ~v1_funct_2(X0,sK1,X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X1,sK2,X0)) | ~v1_funct_1(sK2) | k1_xboole_0 = X1 | v2_funct_1(X0)) )),
% 1.76/0.65    inference(trivial_inequality_removal,[],[f482])).
% 1.76/0.65  fof(f482,plain,(
% 1.76/0.65    ( ! [X0,X1] : (sK1 != sK1 | ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(X0) | ~v1_funct_2(X0,sK1,X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X1,sK2,X0)) | ~v1_funct_1(sK2) | k1_xboole_0 = X1 | v2_funct_1(X0)) )),
% 1.76/0.65    inference(superposition,[],[f82,f48])).
% 1.76/0.65  fof(f48,plain,(
% 1.76/0.65    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 1.76/0.65    inference(cnf_transformation,[],[f22])).
% 1.76/0.65  fof(f82,plain,(
% 1.76/0.65    ( ! [X4,X2,X0,X3,X1] : (k2_relset_1(X0,X1,X3) != X1 | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X1,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~v1_funct_1(X3) | k1_xboole_0 = X2 | v2_funct_1(X4)) )),
% 1.76/0.65    inference(cnf_transformation,[],[f38])).
% 1.76/0.65  fof(f38,plain,(
% 1.76/0.65    ! [X0,X1,X2,X3] : (! [X4] : ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.76/0.65    inference(flattening,[],[f37])).
% 1.76/0.65  fof(f37,plain,(
% 1.76/0.65    ! [X0,X1,X2,X3] : (! [X4] : ((((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | (k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.76/0.65    inference(ennf_transformation,[],[f17])).
% 1.76/0.65  fof(f17,axiom,(
% 1.76/0.65    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) => ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 1.76/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_funct_2)).
% 1.76/0.65  fof(f443,plain,(
% 1.76/0.65    ~spl4_10 | spl4_43 | ~spl4_40),
% 1.76/0.65    inference(avatar_split_clause,[],[f435,f417,f439,f173])).
% 1.76/0.65  fof(f435,plain,(
% 1.76/0.65    sK0 = k2_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_40),
% 1.76/0.65    inference(superposition,[],[f75,f419])).
% 1.76/0.65  fof(f75,plain,(
% 1.76/0.65    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.76/0.65    inference(cnf_transformation,[],[f32])).
% 1.76/0.65  fof(f32,plain,(
% 1.76/0.65    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.76/0.65    inference(ennf_transformation,[],[f10])).
% 1.76/0.65  fof(f10,axiom,(
% 1.76/0.65    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.76/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.76/0.65  fof(f431,plain,(
% 1.76/0.65    spl4_41),
% 1.76/0.65    inference(avatar_contradiction_clause,[],[f430])).
% 1.76/0.65  fof(f430,plain,(
% 1.76/0.65    $false | spl4_41),
% 1.76/0.65    inference(subsumption_resolution,[],[f46,f423])).
% 1.76/0.65  fof(f423,plain,(
% 1.76/0.65    ~v1_funct_2(sK3,sK1,sK0) | spl4_41),
% 1.76/0.65    inference(avatar_component_clause,[],[f421])).
% 1.76/0.65  fof(f46,plain,(
% 1.76/0.65    v1_funct_2(sK3,sK1,sK0)),
% 1.76/0.65    inference(cnf_transformation,[],[f22])).
% 1.76/0.65  fof(f424,plain,(
% 1.76/0.65    spl4_40 | ~spl4_11 | ~spl4_5 | ~spl4_25 | ~spl4_9 | ~spl4_10 | ~spl4_41),
% 1.76/0.65    inference(avatar_split_clause,[],[f412,f421,f173,f169,f278,f135,f177,f417])).
% 1.76/0.65  fof(f412,plain,(
% 1.76/0.65    ~v1_funct_2(sK3,sK1,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | sK0 = k2_relset_1(sK1,sK0,sK3)),
% 1.76/0.65    inference(resolution,[],[f78,f49])).
% 1.76/0.65  fof(f49,plain,(
% 1.76/0.65    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 1.76/0.65    inference(cnf_transformation,[],[f22])).
% 1.76/0.65  fof(f78,plain,(
% 1.76/0.65    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_1(X2) | k2_relset_1(X0,X1,X2) = X1) )),
% 1.76/0.65    inference(cnf_transformation,[],[f36])).
% 1.76/0.65  fof(f36,plain,(
% 1.76/0.65    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.76/0.65    inference(flattening,[],[f35])).
% 1.76/0.65  fof(f35,plain,(
% 1.76/0.65    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.76/0.65    inference(ennf_transformation,[],[f16])).
% 1.76/0.65  fof(f16,axiom,(
% 1.76/0.65    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 1.76/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_funct_2)).
% 1.76/0.65  fof(f359,plain,(
% 1.76/0.65    spl4_34),
% 1.76/0.65    inference(avatar_contradiction_clause,[],[f356])).
% 1.76/0.65  fof(f356,plain,(
% 1.76/0.65    $false | spl4_34),
% 1.76/0.65    inference(unit_resulting_resolution,[],[f93,f354])).
% 1.76/0.65  fof(f354,plain,(
% 1.76/0.65    ~r1_tarski(sK1,sK1) | spl4_34),
% 1.76/0.65    inference(avatar_component_clause,[],[f352])).
% 1.76/0.65  fof(f352,plain,(
% 1.76/0.65    spl4_34 <=> r1_tarski(sK1,sK1)),
% 1.76/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).
% 1.76/0.65  fof(f355,plain,(
% 1.76/0.65    ~spl4_3 | ~spl4_24 | ~spl4_9 | ~spl4_34 | ~spl4_6 | spl4_33),
% 1.76/0.65    inference(avatar_split_clause,[],[f350,f340,f139,f352,f169,f274,f112])).
% 1.76/0.65  fof(f112,plain,(
% 1.76/0.65    spl4_3 <=> v1_relat_1(sK2)),
% 1.76/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.76/0.65  fof(f274,plain,(
% 1.76/0.65    spl4_24 <=> v2_funct_1(sK2)),
% 1.76/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 1.76/0.65  fof(f340,plain,(
% 1.76/0.65    spl4_33 <=> r1_tarski(sK1,k1_relat_1(k2_funct_1(sK2)))),
% 1.76/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).
% 1.76/0.65  fof(f350,plain,(
% 1.76/0.65    ~r1_tarski(sK1,sK1) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl4_6 | spl4_33)),
% 1.76/0.65    inference(forward_demodulation,[],[f349,f141])).
% 1.76/0.65  fof(f349,plain,(
% 1.76/0.65    ~r1_tarski(sK1,k2_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | spl4_33),
% 1.76/0.65    inference(superposition,[],[f342,f68])).
% 1.76/0.65  fof(f342,plain,(
% 1.76/0.65    ~r1_tarski(sK1,k1_relat_1(k2_funct_1(sK2))) | spl4_33),
% 1.76/0.65    inference(avatar_component_clause,[],[f340])).
% 1.76/0.65  fof(f346,plain,(
% 1.76/0.65    ~spl4_3 | spl4_28),
% 1.76/0.65    inference(avatar_contradiction_clause,[],[f344])).
% 1.76/0.65  fof(f344,plain,(
% 1.76/0.65    $false | (~spl4_3 | spl4_28)),
% 1.76/0.65    inference(unit_resulting_resolution,[],[f114,f54,f319,f66])).
% 1.76/0.65  fof(f319,plain,(
% 1.76/0.65    ~v1_relat_1(k2_funct_1(sK2)) | spl4_28),
% 1.76/0.65    inference(avatar_component_clause,[],[f317])).
% 1.76/0.65  fof(f317,plain,(
% 1.76/0.65    spl4_28 <=> v1_relat_1(k2_funct_1(sK2))),
% 1.76/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 1.76/0.65  fof(f54,plain,(
% 1.76/0.65    v1_funct_1(sK2)),
% 1.76/0.65    inference(cnf_transformation,[],[f22])).
% 1.76/0.65  fof(f114,plain,(
% 1.76/0.65    v1_relat_1(sK2) | ~spl4_3),
% 1.76/0.65    inference(avatar_component_clause,[],[f112])).
% 1.76/0.65  fof(f343,plain,(
% 1.76/0.65    ~spl4_3 | ~spl4_28 | spl4_20 | ~spl4_33 | ~spl4_6 | ~spl4_22),
% 1.76/0.65    inference(avatar_split_clause,[],[f338,f266,f139,f340,f253,f317,f112])).
% 1.76/0.65  fof(f266,plain,(
% 1.76/0.65    spl4_22 <=> k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 1.76/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 1.76/0.65  fof(f338,plain,(
% 1.76/0.65    ~r1_tarski(sK1,k1_relat_1(k2_funct_1(sK2))) | sK0 = k1_relat_1(sK2) | ~v1_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2) | (~spl4_6 | ~spl4_22)),
% 1.76/0.65    inference(forward_demodulation,[],[f337,f141])).
% 1.76/0.65  fof(f337,plain,(
% 1.76/0.65    sK0 = k1_relat_1(sK2) | ~v1_relat_1(k2_funct_1(sK2)) | ~r1_tarski(k2_relat_1(sK2),k1_relat_1(k2_funct_1(sK2))) | ~v1_relat_1(sK2) | ~spl4_22),
% 1.76/0.65    inference(forward_demodulation,[],[f310,f91])).
% 1.76/0.65  fof(f310,plain,(
% 1.76/0.65    k1_relat_1(sK2) = k1_relat_1(k6_partfun1(sK0)) | ~v1_relat_1(k2_funct_1(sK2)) | ~r1_tarski(k2_relat_1(sK2),k1_relat_1(k2_funct_1(sK2))) | ~v1_relat_1(sK2) | ~spl4_22),
% 1.76/0.65    inference(superposition,[],[f64,f268])).
% 1.76/0.65  fof(f268,plain,(
% 1.76/0.65    k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~spl4_22),
% 1.76/0.65    inference(avatar_component_clause,[],[f266])).
% 1.76/0.65  fof(f308,plain,(
% 1.76/0.65    ~spl4_23),
% 1.76/0.65    inference(avatar_contradiction_clause,[],[f295])).
% 1.76/0.65  fof(f295,plain,(
% 1.76/0.65    $false | ~spl4_23),
% 1.76/0.65    inference(subsumption_resolution,[],[f52,f272])).
% 1.76/0.65  fof(f272,plain,(
% 1.76/0.65    k1_xboole_0 = sK1 | ~spl4_23),
% 1.76/0.65    inference(avatar_component_clause,[],[f270])).
% 1.76/0.65  fof(f270,plain,(
% 1.76/0.65    spl4_23 <=> k1_xboole_0 = sK1),
% 1.76/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 1.76/0.65  fof(f52,plain,(
% 1.76/0.65    k1_xboole_0 != sK1),
% 1.76/0.65    inference(cnf_transformation,[],[f22])).
% 1.76/0.65  fof(f285,plain,(
% 1.76/0.65    spl4_25),
% 1.76/0.65    inference(avatar_contradiction_clause,[],[f284])).
% 1.76/0.65  fof(f284,plain,(
% 1.76/0.65    $false | spl4_25),
% 1.76/0.65    inference(subsumption_resolution,[],[f55,f280])).
% 1.76/0.65  fof(f280,plain,(
% 1.76/0.65    ~v1_funct_2(sK2,sK0,sK1) | spl4_25),
% 1.76/0.65    inference(avatar_component_clause,[],[f278])).
% 1.76/0.65  fof(f55,plain,(
% 1.76/0.65    v1_funct_2(sK2,sK0,sK1)),
% 1.76/0.65    inference(cnf_transformation,[],[f22])).
% 1.76/0.65  fof(f283,plain,(
% 1.76/0.65    spl4_24),
% 1.76/0.65    inference(avatar_contradiction_clause,[],[f282])).
% 1.76/0.65  fof(f282,plain,(
% 1.76/0.65    $false | spl4_24),
% 1.76/0.65    inference(subsumption_resolution,[],[f50,f276])).
% 1.76/0.65  fof(f276,plain,(
% 1.76/0.65    ~v2_funct_1(sK2) | spl4_24),
% 1.76/0.65    inference(avatar_component_clause,[],[f274])).
% 1.76/0.65  fof(f281,plain,(
% 1.76/0.65    spl4_22 | spl4_23 | ~spl4_24 | ~spl4_9 | ~spl4_5 | ~spl4_25),
% 1.76/0.65    inference(avatar_split_clause,[],[f264,f278,f135,f169,f274,f270,f266])).
% 1.76/0.65  fof(f264,plain,(
% 1.76/0.65    ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | k1_xboole_0 = sK1 | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 1.76/0.65    inference(trivial_inequality_removal,[],[f261])).
% 1.76/0.65  fof(f261,plain,(
% 1.76/0.65    sK1 != sK1 | ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | k1_xboole_0 = sK1 | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 1.76/0.65    inference(superposition,[],[f76,f48])).
% 1.76/0.65  fof(f249,plain,(
% 1.76/0.65    spl4_16 | ~spl4_1 | ~spl4_17 | ~spl4_9 | ~spl4_3 | ~spl4_11 | ~spl4_18 | ~spl4_19 | ~spl4_6 | ~spl4_14),
% 1.76/0.65    inference(avatar_split_clause,[],[f232,f212,f139,f246,f242,f177,f112,f169,f238,f103,f234])).
% 1.76/0.65  fof(f212,plain,(
% 1.76/0.65    spl4_14 <=> k6_partfun1(sK0) = k5_relat_1(sK2,sK3)),
% 1.76/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 1.76/0.65  fof(f232,plain,(
% 1.76/0.65    sK1 != k1_relat_1(sK3) | k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v2_funct_1(sK3) | ~v1_relat_1(sK3) | sK2 = k2_funct_1(sK3) | (~spl4_6 | ~spl4_14)),
% 1.76/0.65    inference(forward_demodulation,[],[f230,f141])).
% 1.76/0.65  fof(f230,plain,(
% 1.76/0.65    k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v2_funct_1(sK3) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v1_relat_1(sK3) | sK2 = k2_funct_1(sK3) | ~spl4_14),
% 1.76/0.65    inference(superposition,[],[f92,f214])).
% 1.76/0.65  fof(f214,plain,(
% 1.76/0.65    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~spl4_14),
% 1.76/0.65    inference(avatar_component_clause,[],[f212])).
% 1.76/0.65  fof(f222,plain,(
% 1.76/0.65    ~spl4_9 | ~spl4_10 | ~spl4_11 | ~spl4_5 | spl4_14 | ~spl4_8),
% 1.76/0.65    inference(avatar_split_clause,[],[f219,f160,f212,f135,f177,f173,f169])).
% 1.76/0.65  fof(f219,plain,(
% 1.76/0.65    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK2) | ~spl4_8),
% 1.76/0.65    inference(superposition,[],[f85,f162])).
% 1.76/0.65  fof(f85,plain,(
% 1.76/0.65    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X4)) )),
% 1.76/0.65    inference(cnf_transformation,[],[f42])).
% 1.76/0.65  fof(f42,plain,(
% 1.76/0.65    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.76/0.65    inference(flattening,[],[f41])).
% 1.76/0.65  fof(f41,plain,(
% 1.76/0.65    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.76/0.65    inference(ennf_transformation,[],[f14])).
% 1.76/0.65  fof(f14,axiom,(
% 1.76/0.65    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.76/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 1.76/0.65  fof(f205,plain,(
% 1.76/0.65    spl4_11),
% 1.76/0.65    inference(avatar_contradiction_clause,[],[f204])).
% 1.76/0.65  fof(f204,plain,(
% 1.76/0.65    $false | spl4_11),
% 1.76/0.65    inference(subsumption_resolution,[],[f45,f179])).
% 1.76/0.65  fof(f179,plain,(
% 1.76/0.65    ~v1_funct_1(sK3) | spl4_11),
% 1.76/0.65    inference(avatar_component_clause,[],[f177])).
% 1.76/0.65  fof(f203,plain,(
% 1.76/0.65    spl4_10),
% 1.76/0.65    inference(avatar_contradiction_clause,[],[f202])).
% 1.76/0.65  fof(f202,plain,(
% 1.76/0.65    $false | spl4_10),
% 1.76/0.65    inference(subsumption_resolution,[],[f47,f175])).
% 1.76/0.65  fof(f175,plain,(
% 1.76/0.65    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl4_10),
% 1.76/0.65    inference(avatar_component_clause,[],[f173])).
% 1.76/0.65  fof(f47,plain,(
% 1.76/0.65    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.76/0.65    inference(cnf_transformation,[],[f22])).
% 1.76/0.65  fof(f201,plain,(
% 1.76/0.65    spl4_9),
% 1.76/0.65    inference(avatar_contradiction_clause,[],[f200])).
% 1.76/0.65  fof(f200,plain,(
% 1.76/0.65    $false | spl4_9),
% 1.76/0.65    inference(subsumption_resolution,[],[f54,f171])).
% 1.76/0.65  fof(f171,plain,(
% 1.76/0.65    ~v1_funct_1(sK2) | spl4_9),
% 1.76/0.65    inference(avatar_component_clause,[],[f169])).
% 1.76/0.65  fof(f199,plain,(
% 1.76/0.65    spl4_7),
% 1.76/0.65    inference(avatar_contradiction_clause,[],[f190])).
% 1.76/0.65  fof(f190,plain,(
% 1.76/0.65    $false | spl4_7),
% 1.76/0.65    inference(unit_resulting_resolution,[],[f54,f45,f47,f56,f158,f87])).
% 1.76/0.65  fof(f87,plain,(
% 1.76/0.65    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X4)) )),
% 1.76/0.65    inference(cnf_transformation,[],[f44])).
% 1.76/0.65  fof(f44,plain,(
% 1.76/0.65    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.76/0.65    inference(flattening,[],[f43])).
% 1.76/0.65  fof(f43,plain,(
% 1.76/0.65    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.76/0.65    inference(ennf_transformation,[],[f12])).
% 1.76/0.65  fof(f12,axiom,(
% 1.76/0.65    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 1.76/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 1.76/0.65  fof(f158,plain,(
% 1.76/0.65    ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl4_7),
% 1.76/0.65    inference(avatar_component_clause,[],[f156])).
% 1.76/0.65  fof(f156,plain,(
% 1.76/0.65    spl4_7 <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.76/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 1.76/0.65  fof(f56,plain,(
% 1.76/0.65    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.76/0.65    inference(cnf_transformation,[],[f22])).
% 1.76/0.65  fof(f163,plain,(
% 1.76/0.65    ~spl4_7 | spl4_8),
% 1.76/0.65    inference(avatar_split_clause,[],[f153,f160,f156])).
% 1.76/0.65  fof(f153,plain,(
% 1.76/0.65    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) | ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.76/0.65    inference(resolution,[],[f149,f49])).
% 1.76/0.65  fof(f149,plain,(
% 1.76/0.65    ( ! [X2,X1] : (~r2_relset_1(X2,X2,X1,k6_partfun1(X2)) | k6_partfun1(X2) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))) )),
% 1.76/0.65    inference(resolution,[],[f84,f61])).
% 1.76/0.65  fof(f61,plain,(
% 1.76/0.65    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.76/0.65    inference(cnf_transformation,[],[f13])).
% 1.76/0.65  fof(f13,axiom,(
% 1.76/0.65    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 1.76/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 1.76/0.65  fof(f84,plain,(
% 1.76/0.65    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 = X3 | ~r2_relset_1(X0,X1,X2,X3)) )),
% 1.76/0.65    inference(cnf_transformation,[],[f40])).
% 1.76/0.65  fof(f40,plain,(
% 1.76/0.65    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.76/0.65    inference(flattening,[],[f39])).
% 1.76/0.65  fof(f39,plain,(
% 1.76/0.65    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.76/0.65    inference(ennf_transformation,[],[f11])).
% 1.76/0.65  fof(f11,axiom,(
% 1.76/0.65    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.76/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.76/0.65  fof(f145,plain,(
% 1.76/0.65    spl4_5),
% 1.76/0.65    inference(avatar_contradiction_clause,[],[f144])).
% 1.76/0.65  fof(f144,plain,(
% 1.76/0.65    $false | spl4_5),
% 1.76/0.65    inference(subsumption_resolution,[],[f56,f137])).
% 1.76/0.65  fof(f137,plain,(
% 1.76/0.65    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl4_5),
% 1.76/0.65    inference(avatar_component_clause,[],[f135])).
% 1.76/0.65  fof(f143,plain,(
% 1.76/0.65    ~spl4_5 | spl4_6),
% 1.76/0.65    inference(avatar_split_clause,[],[f133,f139,f135])).
% 1.76/0.65  fof(f133,plain,(
% 1.76/0.65    sK1 = k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.76/0.65    inference(superposition,[],[f48,f75])).
% 1.76/0.65  fof(f128,plain,(
% 1.76/0.65    spl4_4),
% 1.76/0.65    inference(avatar_contradiction_clause,[],[f125])).
% 1.76/0.65  fof(f125,plain,(
% 1.76/0.65    $false | spl4_4),
% 1.76/0.65    inference(unit_resulting_resolution,[],[f71,f118])).
% 1.76/0.65  fof(f118,plain,(
% 1.76/0.65    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | spl4_4),
% 1.76/0.65    inference(avatar_component_clause,[],[f116])).
% 1.76/0.65  fof(f116,plain,(
% 1.76/0.65    spl4_4 <=> v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 1.76/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.76/0.65  fof(f71,plain,(
% 1.76/0.65    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.76/0.65    inference(cnf_transformation,[],[f3])).
% 1.76/0.65  fof(f3,axiom,(
% 1.76/0.65    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.76/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.76/0.65  fof(f123,plain,(
% 1.76/0.65    spl4_2),
% 1.76/0.65    inference(avatar_contradiction_clause,[],[f120])).
% 1.76/0.65  fof(f120,plain,(
% 1.76/0.65    $false | spl4_2),
% 1.76/0.65    inference(unit_resulting_resolution,[],[f71,f109])).
% 1.76/0.65  fof(f109,plain,(
% 1.76/0.65    ~v1_relat_1(k2_zfmisc_1(sK1,sK0)) | spl4_2),
% 1.76/0.65    inference(avatar_component_clause,[],[f107])).
% 1.76/0.65  fof(f107,plain,(
% 1.76/0.65    spl4_2 <=> v1_relat_1(k2_zfmisc_1(sK1,sK0))),
% 1.76/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.76/0.65  fof(f119,plain,(
% 1.76/0.65    spl4_3 | ~spl4_4),
% 1.76/0.65    inference(avatar_split_clause,[],[f100,f116,f112])).
% 1.76/0.65  fof(f100,plain,(
% 1.76/0.65    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | v1_relat_1(sK2)),
% 1.76/0.65    inference(resolution,[],[f65,f56])).
% 1.76/0.65  fof(f65,plain,(
% 1.76/0.65    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 1.76/0.65    inference(cnf_transformation,[],[f25])).
% 1.76/0.65  fof(f25,plain,(
% 1.76/0.65    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.76/0.65    inference(ennf_transformation,[],[f2])).
% 1.76/0.65  fof(f2,axiom,(
% 1.76/0.65    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.76/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.76/0.65  fof(f110,plain,(
% 1.76/0.65    spl4_1 | ~spl4_2),
% 1.76/0.65    inference(avatar_split_clause,[],[f99,f107,f103])).
% 1.76/0.65  fof(f99,plain,(
% 1.76/0.65    ~v1_relat_1(k2_zfmisc_1(sK1,sK0)) | v1_relat_1(sK3)),
% 1.76/0.65    inference(resolution,[],[f65,f47])).
% 1.76/0.65  % SZS output end Proof for theBenchmark
% 1.76/0.65  % (14150)------------------------------
% 1.76/0.65  % (14150)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.76/0.65  % (14150)Termination reason: Refutation
% 1.76/0.65  
% 1.76/0.65  % (14150)Memory used [KB]: 6908
% 1.76/0.65  % (14150)Time elapsed: 0.194 s
% 1.76/0.65  % (14150)------------------------------
% 1.76/0.65  % (14150)------------------------------
% 1.76/0.66  % (14136)Success in time 0.29 s
%------------------------------------------------------------------------------
