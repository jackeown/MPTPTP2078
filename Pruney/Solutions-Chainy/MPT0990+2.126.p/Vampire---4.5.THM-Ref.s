%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:50 EST 2020

% Result     : Theorem 2.59s
% Output     : Refutation 2.59s
% Verified   : 
% Statistics : Number of formulae       :  264 ( 521 expanded)
%              Number of leaves         :   60 ( 199 expanded)
%              Depth                    :   10
%              Number of atoms          :  850 (2080 expanded)
%              Number of equality atoms :  147 ( 527 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3234,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f150,f159,f163,f167,f334,f339,f374,f376,f693,f777,f824,f826,f847,f861,f874,f906,f913,f915,f923,f1006,f1018,f1101,f1184,f1809,f1831,f1863,f1869,f1969,f2004,f2759,f2765,f2830,f2925,f3213])).

fof(f3213,plain,(
    ~ spl4_254 ),
    inference(avatar_contradiction_clause,[],[f3187])).

fof(f3187,plain,
    ( $false
    | ~ spl4_254 ),
    inference(subsumption_resolution,[],[f78,f2924])).

fof(f2924,plain,
    ( sK3 = k2_funct_1(sK2)
    | ~ spl4_254 ),
    inference(avatar_component_clause,[],[f2922])).

fof(f2922,plain,
    ( spl4_254
  <=> sK3 = k2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_254])])).

fof(f78,plain,(
    sK3 != k2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f32,plain,(
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
    inference(ennf_transformation,[],[f31])).

fof(f31,negated_conjecture,(
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
    inference(negated_conjecture,[],[f30])).

fof(f30,conjecture,(
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

fof(f2925,plain,
    ( ~ spl4_1
    | ~ spl4_63
    | ~ spl4_47
    | spl4_254
    | ~ spl4_240 ),
    inference(avatar_split_clause,[],[f2905,f2827,f2922,f802,f968,f143])).

fof(f143,plain,
    ( spl4_1
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f968,plain,
    ( spl4_63
  <=> v2_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_63])])).

fof(f802,plain,
    ( spl4_47
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_47])])).

fof(f2827,plain,
    ( spl4_240
  <=> sK2 = k2_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_240])])).

fof(f2905,plain,
    ( sK3 = k2_funct_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_240 ),
    inference(superposition,[],[f97,f2829])).

fof(f2829,plain,
    ( sK2 = k2_funct_1(sK3)
    | ~ spl4_240 ),
    inference(avatar_component_clause,[],[f2827])).

fof(f97,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).

fof(f2830,plain,
    ( ~ spl4_69
    | spl4_240
    | ~ spl4_167
    | ~ spl4_233 ),
    inference(avatar_split_clause,[],[f2825,f2752,f2001,f2827,f995])).

fof(f995,plain,
    ( spl4_69
  <=> v1_relat_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_69])])).

fof(f2001,plain,
    ( spl4_167
  <=> sK2 = k5_relat_1(k6_partfun1(sK0),k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_167])])).

fof(f2752,plain,
    ( spl4_233
  <=> sK0 = k1_relat_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_233])])).

fof(f2825,plain,
    ( sK2 = k2_funct_1(sK3)
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ spl4_167
    | ~ spl4_233 ),
    inference(forward_demodulation,[],[f2783,f2003])).

fof(f2003,plain,
    ( sK2 = k5_relat_1(k6_partfun1(sK0),k2_funct_1(sK3))
    | ~ spl4_167 ),
    inference(avatar_component_clause,[],[f2001])).

fof(f2783,plain,
    ( k2_funct_1(sK3) = k5_relat_1(k6_partfun1(sK0),k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ spl4_233 ),
    inference(superposition,[],[f129,f2754])).

fof(f2754,plain,
    ( sK0 = k1_relat_1(k2_funct_1(sK3))
    | ~ spl4_233 ),
    inference(avatar_component_clause,[],[f2752])).

fof(f129,plain,(
    ! [X0] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f89,f82])).

fof(f82,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f89,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).

fof(f2765,plain,
    ( ~ spl4_71
    | ~ spl4_69
    | spl4_233
    | ~ spl4_232 ),
    inference(avatar_split_clause,[],[f2760,f2748,f2752,f995,f1003])).

fof(f1003,plain,
    ( spl4_71
  <=> v4_relat_1(k2_funct_1(sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_71])])).

fof(f2748,plain,
    ( spl4_232
  <=> r1_tarski(sK0,k1_relat_1(k2_funct_1(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_232])])).

fof(f2760,plain,
    ( sK0 = k1_relat_1(k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ v4_relat_1(k2_funct_1(sK3),sK0)
    | ~ spl4_232 ),
    inference(resolution,[],[f2749,f319])).

fof(f319,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,k1_relat_1(X0))
      | k1_relat_1(X0) = X1
      | ~ v1_relat_1(X0)
      | ~ v4_relat_1(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f310])).

fof(f310,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
      | ~ r1_tarski(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | ~ v4_relat_1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f107,f111])).

fof(f111,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(f107,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

fof(f2749,plain,
    ( r1_tarski(sK0,k1_relat_1(k2_funct_1(sK3)))
    | ~ spl4_232 ),
    inference(avatar_component_clause,[],[f2748])).

fof(f2759,plain,
    ( ~ spl4_1
    | ~ spl4_63
    | ~ spl4_47
    | ~ spl4_79
    | ~ spl4_58
    | spl4_232 ),
    inference(avatar_split_clause,[],[f2758,f2748,f919,f1078,f802,f968,f143])).

fof(f1078,plain,
    ( spl4_79
  <=> r1_tarski(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_79])])).

fof(f919,plain,
    ( spl4_58
  <=> sK0 = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_58])])).

fof(f2758,plain,
    ( ~ r1_tarski(sK0,sK0)
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_58
    | spl4_232 ),
    inference(forward_demodulation,[],[f2757,f921])).

fof(f921,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ spl4_58 ),
    inference(avatar_component_clause,[],[f919])).

fof(f2757,plain,
    ( ~ r1_tarski(sK0,k2_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | spl4_232 ),
    inference(superposition,[],[f2750,f98])).

fof(f98,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f2750,plain,
    ( ~ r1_tarski(sK0,k1_relat_1(k2_funct_1(sK3)))
    | spl4_232 ),
    inference(avatar_component_clause,[],[f2748])).

fof(f2004,plain,
    ( ~ spl4_1
    | ~ spl4_63
    | ~ spl4_47
    | ~ spl4_69
    | spl4_167
    | ~ spl4_16
    | ~ spl4_53
    | ~ spl4_147 ),
    inference(avatar_split_clause,[],[f1999,f1840,f872,f371,f2001,f995,f802,f968,f143])).

fof(f371,plain,
    ( spl4_16
  <=> sK2 = k5_relat_1(sK2,k6_partfun1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f872,plain,
    ( spl4_53
  <=> ! [X0] :
        ( k5_relat_1(sK2,k5_relat_1(sK3,X0)) = k5_relat_1(k6_partfun1(sK0),X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_53])])).

fof(f1840,plain,
    ( spl4_147
  <=> sK1 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_147])])).

fof(f1999,plain,
    ( sK2 = k5_relat_1(k6_partfun1(sK0),k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_16
    | ~ spl4_53
    | ~ spl4_147 ),
    inference(forward_demodulation,[],[f1998,f373])).

fof(f373,plain,
    ( sK2 = k5_relat_1(sK2,k6_partfun1(sK1))
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f371])).

fof(f1998,plain,
    ( k5_relat_1(sK2,k6_partfun1(sK1)) = k5_relat_1(k6_partfun1(sK0),k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_53
    | ~ spl4_147 ),
    inference(forward_demodulation,[],[f1142,f1842])).

fof(f1842,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl4_147 ),
    inference(avatar_component_clause,[],[f1840])).

fof(f1142,plain,
    ( k5_relat_1(k6_partfun1(sK0),k2_funct_1(sK3)) = k5_relat_1(sK2,k6_partfun1(k1_relat_1(sK3)))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_53 ),
    inference(superposition,[],[f873,f131])).

fof(f131,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f100,f82])).

fof(f100,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
          & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

fof(f873,plain,
    ( ! [X0] :
        ( k5_relat_1(sK2,k5_relat_1(sK3,X0)) = k5_relat_1(k6_partfun1(sK0),X0)
        | ~ v1_relat_1(X0) )
    | ~ spl4_53 ),
    inference(avatar_component_clause,[],[f872])).

fof(f1969,plain,
    ( ~ spl4_47
    | ~ spl4_1
    | spl4_63
    | ~ spl4_84
    | ~ spl4_36
    | ~ spl4_51
    | ~ spl4_147 ),
    inference(avatar_split_clause,[],[f1968,f1840,f850,f691,f1165,f968,f143,f802])).

fof(f1165,plain,
    ( spl4_84
  <=> v2_funct_1(k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_84])])).

fof(f691,plain,
    ( spl4_36
  <=> ! [X7] :
        ( sK1 != k1_relat_1(X7)
        | v2_funct_1(X7)
        | ~ v1_relat_1(X7)
        | ~ v2_funct_1(k5_relat_1(sK2,X7))
        | ~ v1_funct_1(X7) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f850,plain,
    ( spl4_51
  <=> k6_partfun1(sK0) = k5_relat_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_51])])).

fof(f1968,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ spl4_36
    | ~ spl4_51
    | ~ spl4_147 ),
    inference(forward_demodulation,[],[f1929,f852])).

fof(f852,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ spl4_51 ),
    inference(avatar_component_clause,[],[f850])).

fof(f1929,plain,
    ( v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | ~ v1_funct_1(sK3)
    | ~ spl4_36
    | ~ spl4_147 ),
    inference(trivial_inequality_removal,[],[f1927])).

fof(f1927,plain,
    ( sK1 != sK1
    | v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | ~ v1_funct_1(sK3)
    | ~ spl4_36
    | ~ spl4_147 ),
    inference(superposition,[],[f692,f1842])).

fof(f692,plain,
    ( ! [X7] :
        ( sK1 != k1_relat_1(X7)
        | v2_funct_1(X7)
        | ~ v1_relat_1(X7)
        | ~ v2_funct_1(k5_relat_1(sK2,X7))
        | ~ v1_funct_1(X7) )
    | ~ spl4_36 ),
    inference(avatar_component_clause,[],[f691])).

fof(f1869,plain,(
    spl4_148 ),
    inference(avatar_contradiction_clause,[],[f1864])).

fof(f1864,plain,
    ( $false
    | spl4_148 ),
    inference(subsumption_resolution,[],[f177,f1851])).

fof(f1851,plain,
    ( ~ v4_relat_1(sK2,sK0)
    | spl4_148 ),
    inference(avatar_component_clause,[],[f1849])).

fof(f1849,plain,
    ( spl4_148
  <=> v4_relat_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_148])])).

fof(f177,plain,(
    v4_relat_1(sK2,sK0) ),
    inference(resolution,[],[f115,f81])).

fof(f81,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f33])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f1863,plain,
    ( ~ spl4_148
    | ~ spl4_3
    | spl4_147
    | ~ spl4_10
    | ~ spl4_142 ),
    inference(avatar_split_clause,[],[f1862,f1802,f330,f1840,f152,f1849])).

fof(f152,plain,
    ( spl4_3
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f330,plain,
    ( spl4_10
  <=> sK1 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f1802,plain,
    ( spl4_142
  <=> k1_relat_1(sK3) = k9_relat_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_142])])).

fof(f1862,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ v1_relat_1(sK2)
    | ~ v4_relat_1(sK2,sK0)
    | ~ spl4_10
    | ~ spl4_142 ),
    inference(forward_demodulation,[],[f1846,f332])).

fof(f332,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f330])).

fof(f1846,plain,
    ( k1_relat_1(sK3) = k2_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v4_relat_1(sK2,sK0)
    | ~ spl4_142 ),
    inference(superposition,[],[f203,f1804])).

fof(f1804,plain,
    ( k1_relat_1(sK3) = k9_relat_1(sK2,sK0)
    | ~ spl4_142 ),
    inference(avatar_component_clause,[],[f1802])).

fof(f203,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = k9_relat_1(X0,X1)
      | ~ v1_relat_1(X0)
      | ~ v4_relat_1(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f200])).

fof(f200,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = k9_relat_1(X0,X1)
      | ~ v1_relat_1(X0)
      | ~ v4_relat_1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f106,f111])).

fof(f106,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f1831,plain,
    ( ~ spl4_1
    | spl4_143 ),
    inference(avatar_contradiction_clause,[],[f1829])).

fof(f1829,plain,
    ( $false
    | ~ spl4_1
    | spl4_143 ),
    inference(unit_resulting_resolution,[],[f145,f176,f1808,f109])).

fof(f109,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f1808,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),sK1)
    | spl4_143 ),
    inference(avatar_component_clause,[],[f1806])).

fof(f1806,plain,
    ( spl4_143
  <=> r1_tarski(k1_relat_1(sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_143])])).

fof(f176,plain,(
    v4_relat_1(sK3,sK1) ),
    inference(resolution,[],[f115,f72])).

fof(f72,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f33])).

fof(f145,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f143])).

fof(f1809,plain,
    ( ~ spl4_1
    | ~ spl4_3
    | ~ spl4_11
    | spl4_142
    | ~ spl4_143
    | ~ spl4_10
    | ~ spl4_51 ),
    inference(avatar_split_clause,[],[f1800,f850,f330,f1806,f1802,f347,f152,f143])).

fof(f347,plain,
    ( spl4_11
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f1800,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),sK1)
    | k1_relat_1(sK3) = k9_relat_1(sK2,sK0)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ spl4_10
    | ~ spl4_51 ),
    inference(forward_demodulation,[],[f1799,f332])).

fof(f1799,plain,
    ( k1_relat_1(sK3) = k9_relat_1(sK2,sK0)
    | ~ v1_funct_1(sK2)
    | ~ r1_tarski(k1_relat_1(sK3),k2_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ spl4_51 ),
    inference(forward_demodulation,[],[f1727,f127])).

fof(f127,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f86,f82])).

fof(f86,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f1727,plain,
    ( k1_relat_1(sK3) = k9_relat_1(sK2,k1_relat_1(k6_partfun1(sK0)))
    | ~ v1_funct_1(sK2)
    | ~ r1_tarski(k1_relat_1(sK3),k2_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ spl4_51 ),
    inference(superposition,[],[f503,f852])).

fof(f503,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = k9_relat_1(X0,k1_relat_1(k5_relat_1(X0,X1)))
      | ~ v1_funct_1(X0)
      | ~ r1_tarski(k1_relat_1(X1),k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1) ) ),
    inference(duplicate_literal_removal,[],[f493])).

fof(f493,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = k9_relat_1(X0,k1_relat_1(k5_relat_1(X0,X1)))
      | ~ v1_funct_1(X0)
      | ~ r1_tarski(k1_relat_1(X1),k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f110,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

fof(f110,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ v1_funct_1(X1)
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

fof(f1184,plain,(
    spl4_84 ),
    inference(avatar_contradiction_clause,[],[f1181])).

fof(f1181,plain,
    ( $false
    | spl4_84 ),
    inference(unit_resulting_resolution,[],[f124,f1167])).

fof(f1167,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | spl4_84 ),
    inference(avatar_component_clause,[],[f1165])).

fof(f124,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f85,f82])).

fof(f85,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f1101,plain,(
    spl4_79 ),
    inference(avatar_contradiction_clause,[],[f1096])).

fof(f1096,plain,
    ( $false
    | spl4_79 ),
    inference(unit_resulting_resolution,[],[f125,f1080,f206])).

fof(f206,plain,(
    ! [X0] :
      ( ~ v1_relat_1(k6_partfun1(X0))
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f174,f178])).

fof(f178,plain,(
    ! [X0] : v4_relat_1(k6_partfun1(X0),X0) ),
    inference(resolution,[],[f115,f123])).

fof(f123,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f83,f82])).

fof(f83,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

fof(f174,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(k6_partfun1(X0),X1)
      | ~ v1_relat_1(k6_partfun1(X0))
      | r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f109,f127])).

fof(f1080,plain,
    ( ~ r1_tarski(sK0,sK0)
    | spl4_79 ),
    inference(avatar_component_clause,[],[f1078])).

fof(f125,plain,(
    ! [X0] : v1_relat_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f84,f82])).

fof(f84,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f1018,plain,
    ( ~ spl4_1
    | spl4_69 ),
    inference(avatar_contradiction_clause,[],[f1016])).

fof(f1016,plain,
    ( $false
    | ~ spl4_1
    | spl4_69 ),
    inference(unit_resulting_resolution,[],[f145,f70,f997,f95])).

fof(f95,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f997,plain,
    ( ~ v1_relat_1(k2_funct_1(sK3))
    | spl4_69 ),
    inference(avatar_component_clause,[],[f995])).

fof(f70,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f1006,plain,
    ( ~ spl4_1
    | ~ spl4_63
    | ~ spl4_47
    | ~ spl4_69
    | spl4_71
    | ~ spl4_58 ),
    inference(avatar_split_clause,[],[f955,f919,f1003,f995,f802,f968,f143])).

fof(f955,plain,
    ( v4_relat_1(k2_funct_1(sK3),sK0)
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_58 ),
    inference(superposition,[],[f300,f921])).

fof(f300,plain,(
    ! [X7] :
      ( v4_relat_1(k2_funct_1(X7),k2_relat_1(X7))
      | ~ v1_relat_1(k2_funct_1(X7))
      | ~ v1_funct_1(X7)
      | ~ v2_funct_1(X7)
      | ~ v1_relat_1(X7) ) ),
    inference(superposition,[],[f211,f98])).

fof(f211,plain,(
    ! [X1] :
      ( v4_relat_1(X1,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f209,f108])).

fof(f108,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | v4_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f209,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(resolution,[],[f206,f125])).

fof(f923,plain,
    ( ~ spl4_46
    | spl4_58
    | ~ spl4_54 ),
    inference(avatar_split_clause,[],[f917,f895,f919,f798])).

fof(f798,plain,
    ( spl4_46
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).

fof(f895,plain,
    ( spl4_54
  <=> sK0 = k2_relset_1(sK1,sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_54])])).

fof(f917,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_54 ),
    inference(superposition,[],[f114,f897])).

fof(f897,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ spl4_54 ),
    inference(avatar_component_clause,[],[f895])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f915,plain,(
    spl4_56 ),
    inference(avatar_contradiction_clause,[],[f914])).

fof(f914,plain,
    ( $false
    | spl4_56 ),
    inference(subsumption_resolution,[],[f71,f905])).

fof(f905,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | spl4_56 ),
    inference(avatar_component_clause,[],[f903])).

fof(f903,plain,
    ( spl4_56
  <=> v1_funct_2(sK3,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_56])])).

fof(f71,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f913,plain,(
    spl4_55 ),
    inference(avatar_contradiction_clause,[],[f912])).

fof(f912,plain,
    ( $false
    | spl4_55 ),
    inference(subsumption_resolution,[],[f80,f901])).

fof(f901,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | spl4_55 ),
    inference(avatar_component_clause,[],[f899])).

fof(f899,plain,
    ( spl4_55
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_55])])).

fof(f80,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f906,plain,
    ( spl4_54
    | ~ spl4_47
    | ~ spl4_9
    | ~ spl4_55
    | ~ spl4_11
    | ~ spl4_46
    | ~ spl4_56 ),
    inference(avatar_split_clause,[],[f890,f903,f798,f347,f899,f326,f802,f895])).

fof(f326,plain,
    ( spl4_9
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f890,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | sK0 = k2_relset_1(sK1,sK0,sK3) ),
    inference(resolution,[],[f117,f74])).

fof(f74,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f33])).

fof(f117,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X1,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_1(X2)
      | k2_relset_1(X0,X1,X2) = X1 ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
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
    inference(flattening,[],[f62])).

fof(f62,plain,(
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
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
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

fof(f874,plain,
    ( ~ spl4_3
    | ~ spl4_1
    | spl4_53
    | ~ spl4_51 ),
    inference(avatar_split_clause,[],[f870,f850,f872,f143,f152])).

fof(f870,plain,
    ( ! [X0] :
        ( k5_relat_1(sK2,k5_relat_1(sK3,X0)) = k5_relat_1(k6_partfun1(sK0),X0)
        | ~ v1_relat_1(sK3)
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(sK2) )
    | ~ spl4_51 ),
    inference(superposition,[],[f91,f852])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

fof(f861,plain,
    ( ~ spl4_11
    | ~ spl4_46
    | ~ spl4_47
    | ~ spl4_9
    | spl4_51
    | ~ spl4_45 ),
    inference(avatar_split_clause,[],[f858,f774,f850,f326,f802,f798,f347])).

fof(f774,plain,
    ( spl4_45
  <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).

fof(f858,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_45 ),
    inference(superposition,[],[f120,f776])).

fof(f776,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
    | ~ spl4_45 ),
    inference(avatar_component_clause,[],[f774])).

fof(f120,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f66])).

fof(f66,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f847,plain,(
    spl4_44 ),
    inference(avatar_contradiction_clause,[],[f834])).

fof(f834,plain,
    ( $false
    | spl4_44 ),
    inference(unit_resulting_resolution,[],[f79,f70,f72,f81,f772,f122])).

fof(f122,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f68])).

fof(f68,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f772,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl4_44 ),
    inference(avatar_component_clause,[],[f770])).

fof(f770,plain,
    ( spl4_44
  <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).

fof(f79,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f826,plain,(
    spl4_47 ),
    inference(avatar_contradiction_clause,[],[f825])).

fof(f825,plain,
    ( $false
    | spl4_47 ),
    inference(subsumption_resolution,[],[f70,f804])).

fof(f804,plain,
    ( ~ v1_funct_1(sK3)
    | spl4_47 ),
    inference(avatar_component_clause,[],[f802])).

fof(f824,plain,(
    spl4_46 ),
    inference(avatar_contradiction_clause,[],[f820])).

fof(f820,plain,
    ( $false
    | spl4_46 ),
    inference(subsumption_resolution,[],[f72,f800])).

fof(f800,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl4_46 ),
    inference(avatar_component_clause,[],[f798])).

fof(f777,plain,
    ( ~ spl4_44
    | spl4_45 ),
    inference(avatar_split_clause,[],[f768,f774,f770])).

fof(f768,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
    | ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f745,f74])).

fof(f745,plain,(
    ! [X2,X3] :
      ( ~ r2_relset_1(X3,X3,X2,k6_partfun1(X3))
      | k6_partfun1(X3) = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X3))) ) ),
    inference(resolution,[],[f119,f123])).

fof(f119,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f64])).

fof(f64,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f693,plain,
    ( ~ spl4_11
    | ~ spl4_3
    | spl4_36
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f689,f330,f691,f152,f347])).

fof(f689,plain,
    ( ! [X7] :
        ( sK1 != k1_relat_1(X7)
        | ~ v1_funct_1(X7)
        | ~ v1_relat_1(sK2)
        | ~ v1_funct_1(sK2)
        | ~ v2_funct_1(k5_relat_1(sK2,X7))
        | ~ v1_relat_1(X7)
        | v2_funct_1(X7) )
    | ~ spl4_10 ),
    inference(superposition,[],[f103,f332])).

fof(f103,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(k5_relat_1(X1,X0))
      | ~ v1_relat_1(X0)
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_funct_1(X0)
            & v2_funct_1(X1) )
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_funct_1(X0)
            & v2_funct_1(X1) )
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k1_relat_1(X0) = k2_relat_1(X1)
              & v2_funct_1(k5_relat_1(X1,X0)) )
           => ( v2_funct_1(X0)
              & v2_funct_1(X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_1)).

fof(f376,plain,(
    spl4_11 ),
    inference(avatar_contradiction_clause,[],[f375])).

fof(f375,plain,
    ( $false
    | spl4_11 ),
    inference(subsumption_resolution,[],[f79,f349])).

fof(f349,plain,
    ( ~ v1_funct_1(sK2)
    | spl4_11 ),
    inference(avatar_component_clause,[],[f347])).

fof(f374,plain,
    ( ~ spl4_3
    | spl4_16
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f345,f330,f371,f152])).

fof(f345,plain,
    ( sK2 = k5_relat_1(sK2,k6_partfun1(sK1))
    | ~ v1_relat_1(sK2)
    | ~ spl4_10 ),
    inference(superposition,[],[f128,f332])).

fof(f128,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f88,f82])).

fof(f88,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

fof(f339,plain,(
    spl4_9 ),
    inference(avatar_contradiction_clause,[],[f335])).

fof(f335,plain,
    ( $false
    | spl4_9 ),
    inference(subsumption_resolution,[],[f81,f328])).

fof(f328,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl4_9 ),
    inference(avatar_component_clause,[],[f326])).

fof(f334,plain,
    ( ~ spl4_9
    | spl4_10 ),
    inference(avatar_split_clause,[],[f324,f330,f326])).

fof(f324,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f73,f114])).

fof(f73,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f167,plain,(
    spl4_4 ),
    inference(avatar_contradiction_clause,[],[f164])).

fof(f164,plain,
    ( $false
    | spl4_4 ),
    inference(unit_resulting_resolution,[],[f104,f158])).

fof(f158,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | spl4_4 ),
    inference(avatar_component_clause,[],[f156])).

fof(f156,plain,
    ( spl4_4
  <=> v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f104,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f163,plain,(
    spl4_2 ),
    inference(avatar_contradiction_clause,[],[f160])).

fof(f160,plain,
    ( $false
    | spl4_2 ),
    inference(unit_resulting_resolution,[],[f104,f149])).

fof(f149,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | spl4_2 ),
    inference(avatar_component_clause,[],[f147])).

fof(f147,plain,
    ( spl4_2
  <=> v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f159,plain,
    ( spl4_3
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f139,f156,f152])).

fof(f139,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK2) ),
    inference(resolution,[],[f92,f81])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f150,plain,
    ( spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f138,f147,f143])).

fof(f138,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | v1_relat_1(sK3) ),
    inference(resolution,[],[f92,f72])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:32:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (824)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.51  % (832)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.51  % (839)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.52  % (828)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.52  % (843)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.52  % (835)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.52  % (829)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.52  % (831)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.52  % (833)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.52  % (846)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.52  % (847)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.53  % (845)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.53  % (838)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.53  % (826)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.53  % (837)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.53  % (853)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.54  % (830)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.54  % (851)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.54  % (850)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.54  % (825)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.54  % (852)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.54  % (827)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.55  % (844)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.55  % (842)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.55  % (848)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.55  % (836)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.55  % (849)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.55  % (834)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.56  % (840)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.56  % (840)Refutation not found, incomplete strategy% (840)------------------------------
% 0.20/0.56  % (840)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (840)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (840)Memory used [KB]: 10746
% 0.20/0.56  % (840)Time elapsed: 0.151 s
% 0.20/0.56  % (840)------------------------------
% 0.20/0.56  % (840)------------------------------
% 0.20/0.56  % (841)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 2.59/0.75  % (854)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.59/0.75  % (837)Refutation found. Thanks to Tanya!
% 2.59/0.75  % SZS status Theorem for theBenchmark
% 2.59/0.75  % SZS output start Proof for theBenchmark
% 2.59/0.75  fof(f3234,plain,(
% 2.59/0.75    $false),
% 2.59/0.75    inference(avatar_sat_refutation,[],[f150,f159,f163,f167,f334,f339,f374,f376,f693,f777,f824,f826,f847,f861,f874,f906,f913,f915,f923,f1006,f1018,f1101,f1184,f1809,f1831,f1863,f1869,f1969,f2004,f2759,f2765,f2830,f2925,f3213])).
% 2.59/0.75  fof(f3213,plain,(
% 2.59/0.75    ~spl4_254),
% 2.59/0.75    inference(avatar_contradiction_clause,[],[f3187])).
% 2.59/0.75  fof(f3187,plain,(
% 2.59/0.75    $false | ~spl4_254),
% 2.59/0.75    inference(subsumption_resolution,[],[f78,f2924])).
% 2.59/0.75  fof(f2924,plain,(
% 2.59/0.75    sK3 = k2_funct_1(sK2) | ~spl4_254),
% 2.59/0.75    inference(avatar_component_clause,[],[f2922])).
% 2.59/0.75  fof(f2922,plain,(
% 2.59/0.75    spl4_254 <=> sK3 = k2_funct_1(sK2)),
% 2.59/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_254])])).
% 2.59/0.75  fof(f78,plain,(
% 2.59/0.75    sK3 != k2_funct_1(sK2)),
% 2.59/0.75    inference(cnf_transformation,[],[f33])).
% 2.59/0.75  fof(f33,plain,(
% 2.59/0.75    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.59/0.75    inference(flattening,[],[f32])).
% 2.59/0.75  fof(f32,plain,(
% 2.59/0.75    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.59/0.75    inference(ennf_transformation,[],[f31])).
% 2.59/0.75  fof(f31,negated_conjecture,(
% 2.59/0.75    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 2.59/0.75    inference(negated_conjecture,[],[f30])).
% 2.59/0.75  fof(f30,conjecture,(
% 2.59/0.75    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 2.59/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).
% 2.59/0.75  fof(f2925,plain,(
% 2.59/0.75    ~spl4_1 | ~spl4_63 | ~spl4_47 | spl4_254 | ~spl4_240),
% 2.59/0.75    inference(avatar_split_clause,[],[f2905,f2827,f2922,f802,f968,f143])).
% 2.59/0.75  fof(f143,plain,(
% 2.59/0.75    spl4_1 <=> v1_relat_1(sK3)),
% 2.59/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 2.59/0.75  fof(f968,plain,(
% 2.59/0.75    spl4_63 <=> v2_funct_1(sK3)),
% 2.59/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_63])])).
% 2.59/0.75  fof(f802,plain,(
% 2.59/0.75    spl4_47 <=> v1_funct_1(sK3)),
% 2.59/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_47])])).
% 2.59/0.75  fof(f2827,plain,(
% 2.59/0.75    spl4_240 <=> sK2 = k2_funct_1(sK3)),
% 2.59/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_240])])).
% 2.59/0.75  fof(f2905,plain,(
% 2.59/0.75    sK3 = k2_funct_1(sK2) | ~v1_funct_1(sK3) | ~v2_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl4_240),
% 2.59/0.75    inference(superposition,[],[f97,f2829])).
% 2.59/0.75  fof(f2829,plain,(
% 2.59/0.75    sK2 = k2_funct_1(sK3) | ~spl4_240),
% 2.59/0.75    inference(avatar_component_clause,[],[f2827])).
% 2.59/0.75  fof(f97,plain,(
% 2.59/0.75    ( ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.59/0.75    inference(cnf_transformation,[],[f44])).
% 2.59/0.75  fof(f44,plain,(
% 2.59/0.75    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.59/0.75    inference(flattening,[],[f43])).
% 2.59/0.75  fof(f43,plain,(
% 2.59/0.75    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.59/0.75    inference(ennf_transformation,[],[f20])).
% 2.59/0.75  fof(f20,axiom,(
% 2.59/0.75    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 2.59/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).
% 2.59/0.75  fof(f2830,plain,(
% 2.59/0.75    ~spl4_69 | spl4_240 | ~spl4_167 | ~spl4_233),
% 2.59/0.75    inference(avatar_split_clause,[],[f2825,f2752,f2001,f2827,f995])).
% 2.59/0.75  fof(f995,plain,(
% 2.59/0.75    spl4_69 <=> v1_relat_1(k2_funct_1(sK3))),
% 2.59/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_69])])).
% 2.59/0.75  fof(f2001,plain,(
% 2.59/0.75    spl4_167 <=> sK2 = k5_relat_1(k6_partfun1(sK0),k2_funct_1(sK3))),
% 2.59/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_167])])).
% 2.59/0.75  fof(f2752,plain,(
% 2.59/0.75    spl4_233 <=> sK0 = k1_relat_1(k2_funct_1(sK3))),
% 2.59/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_233])])).
% 2.59/0.75  fof(f2825,plain,(
% 2.59/0.75    sK2 = k2_funct_1(sK3) | ~v1_relat_1(k2_funct_1(sK3)) | (~spl4_167 | ~spl4_233)),
% 2.59/0.75    inference(forward_demodulation,[],[f2783,f2003])).
% 2.59/0.75  fof(f2003,plain,(
% 2.59/0.75    sK2 = k5_relat_1(k6_partfun1(sK0),k2_funct_1(sK3)) | ~spl4_167),
% 2.59/0.75    inference(avatar_component_clause,[],[f2001])).
% 2.59/0.75  fof(f2783,plain,(
% 2.59/0.75    k2_funct_1(sK3) = k5_relat_1(k6_partfun1(sK0),k2_funct_1(sK3)) | ~v1_relat_1(k2_funct_1(sK3)) | ~spl4_233),
% 2.59/0.75    inference(superposition,[],[f129,f2754])).
% 2.59/0.75  fof(f2754,plain,(
% 2.59/0.75    sK0 = k1_relat_1(k2_funct_1(sK3)) | ~spl4_233),
% 2.59/0.75    inference(avatar_component_clause,[],[f2752])).
% 2.59/0.75  fof(f129,plain,(
% 2.59/0.75    ( ! [X0] : (k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0)) )),
% 2.59/0.75    inference(definition_unfolding,[],[f89,f82])).
% 2.59/0.75  fof(f82,plain,(
% 2.59/0.75    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 2.59/0.75    inference(cnf_transformation,[],[f27])).
% 2.59/0.75  fof(f27,axiom,(
% 2.59/0.75    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 2.59/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 2.59/0.75  fof(f89,plain,(
% 2.59/0.75    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0) )),
% 2.59/0.75    inference(cnf_transformation,[],[f35])).
% 2.59/0.75  fof(f35,plain,(
% 2.59/0.75    ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0))),
% 2.59/0.75    inference(ennf_transformation,[],[f11])).
% 2.59/0.75  fof(f11,axiom,(
% 2.59/0.75    ! [X0] : (v1_relat_1(X0) => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0)),
% 2.59/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).
% 2.59/0.75  fof(f2765,plain,(
% 2.59/0.75    ~spl4_71 | ~spl4_69 | spl4_233 | ~spl4_232),
% 2.59/0.75    inference(avatar_split_clause,[],[f2760,f2748,f2752,f995,f1003])).
% 2.59/0.75  fof(f1003,plain,(
% 2.59/0.75    spl4_71 <=> v4_relat_1(k2_funct_1(sK3),sK0)),
% 2.59/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_71])])).
% 2.59/0.75  fof(f2748,plain,(
% 2.59/0.75    spl4_232 <=> r1_tarski(sK0,k1_relat_1(k2_funct_1(sK3)))),
% 2.59/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_232])])).
% 2.59/0.75  fof(f2760,plain,(
% 2.59/0.75    sK0 = k1_relat_1(k2_funct_1(sK3)) | ~v1_relat_1(k2_funct_1(sK3)) | ~v4_relat_1(k2_funct_1(sK3),sK0) | ~spl4_232),
% 2.59/0.75    inference(resolution,[],[f2749,f319])).
% 2.59/0.75  fof(f319,plain,(
% 2.59/0.75    ( ! [X0,X1] : (~r1_tarski(X1,k1_relat_1(X0)) | k1_relat_1(X0) = X1 | ~v1_relat_1(X0) | ~v4_relat_1(X0,X1)) )),
% 2.59/0.75    inference(duplicate_literal_removal,[],[f310])).
% 2.59/0.75  fof(f310,plain,(
% 2.59/0.75    ( ! [X0,X1] : (k1_relat_1(X0) = X1 | ~r1_tarski(X1,k1_relat_1(X0)) | ~v1_relat_1(X0) | ~v4_relat_1(X0,X1) | ~v1_relat_1(X0)) )),
% 2.59/0.75    inference(superposition,[],[f107,f111])).
% 2.59/0.75  fof(f111,plain,(
% 2.59/0.75    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.59/0.75    inference(cnf_transformation,[],[f59])).
% 2.59/0.75  fof(f59,plain,(
% 2.59/0.75    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.59/0.75    inference(flattening,[],[f58])).
% 2.59/0.75  fof(f58,plain,(
% 2.59/0.75    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.59/0.75    inference(ennf_transformation,[],[f8])).
% 2.59/0.75  fof(f8,axiom,(
% 2.59/0.75    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 2.59/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).
% 2.59/0.75  fof(f107,plain,(
% 2.59/0.75    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.59/0.75    inference(cnf_transformation,[],[f54])).
% 2.59/0.75  fof(f54,plain,(
% 2.59/0.75    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 2.59/0.75    inference(flattening,[],[f53])).
% 2.59/0.75  fof(f53,plain,(
% 2.59/0.75    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 2.59/0.75    inference(ennf_transformation,[],[f13])).
% 2.59/0.75  fof(f13,axiom,(
% 2.59/0.75    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 2.59/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).
% 2.59/0.75  fof(f2749,plain,(
% 2.59/0.75    r1_tarski(sK0,k1_relat_1(k2_funct_1(sK3))) | ~spl4_232),
% 2.59/0.75    inference(avatar_component_clause,[],[f2748])).
% 2.59/0.75  fof(f2759,plain,(
% 2.59/0.75    ~spl4_1 | ~spl4_63 | ~spl4_47 | ~spl4_79 | ~spl4_58 | spl4_232),
% 2.59/0.75    inference(avatar_split_clause,[],[f2758,f2748,f919,f1078,f802,f968,f143])).
% 2.59/0.75  fof(f1078,plain,(
% 2.59/0.75    spl4_79 <=> r1_tarski(sK0,sK0)),
% 2.59/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_79])])).
% 2.59/0.75  fof(f919,plain,(
% 2.59/0.75    spl4_58 <=> sK0 = k2_relat_1(sK3)),
% 2.59/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_58])])).
% 2.59/0.75  fof(f2758,plain,(
% 2.59/0.75    ~r1_tarski(sK0,sK0) | ~v1_funct_1(sK3) | ~v2_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl4_58 | spl4_232)),
% 2.59/0.75    inference(forward_demodulation,[],[f2757,f921])).
% 2.59/0.75  fof(f921,plain,(
% 2.59/0.75    sK0 = k2_relat_1(sK3) | ~spl4_58),
% 2.59/0.75    inference(avatar_component_clause,[],[f919])).
% 2.59/0.75  fof(f2757,plain,(
% 2.59/0.75    ~r1_tarski(sK0,k2_relat_1(sK3)) | ~v1_funct_1(sK3) | ~v2_funct_1(sK3) | ~v1_relat_1(sK3) | spl4_232),
% 2.59/0.75    inference(superposition,[],[f2750,f98])).
% 2.59/0.75  fof(f98,plain,(
% 2.59/0.75    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.59/0.75    inference(cnf_transformation,[],[f46])).
% 2.59/0.75  fof(f46,plain,(
% 2.59/0.75    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.59/0.75    inference(flattening,[],[f45])).
% 2.59/0.75  fof(f45,plain,(
% 2.59/0.75    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.59/0.75    inference(ennf_transformation,[],[f18])).
% 2.59/0.75  fof(f18,axiom,(
% 2.59/0.75    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 2.59/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 2.59/0.75  fof(f2750,plain,(
% 2.59/0.75    ~r1_tarski(sK0,k1_relat_1(k2_funct_1(sK3))) | spl4_232),
% 2.59/0.75    inference(avatar_component_clause,[],[f2748])).
% 2.59/0.75  fof(f2004,plain,(
% 2.59/0.75    ~spl4_1 | ~spl4_63 | ~spl4_47 | ~spl4_69 | spl4_167 | ~spl4_16 | ~spl4_53 | ~spl4_147),
% 2.59/0.75    inference(avatar_split_clause,[],[f1999,f1840,f872,f371,f2001,f995,f802,f968,f143])).
% 2.59/0.75  fof(f371,plain,(
% 2.59/0.75    spl4_16 <=> sK2 = k5_relat_1(sK2,k6_partfun1(sK1))),
% 2.59/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 2.59/0.75  fof(f872,plain,(
% 2.59/0.75    spl4_53 <=> ! [X0] : (k5_relat_1(sK2,k5_relat_1(sK3,X0)) = k5_relat_1(k6_partfun1(sK0),X0) | ~v1_relat_1(X0))),
% 2.59/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_53])])).
% 2.59/0.75  fof(f1840,plain,(
% 2.59/0.75    spl4_147 <=> sK1 = k1_relat_1(sK3)),
% 2.59/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_147])])).
% 2.59/0.75  fof(f1999,plain,(
% 2.59/0.75    sK2 = k5_relat_1(k6_partfun1(sK0),k2_funct_1(sK3)) | ~v1_relat_1(k2_funct_1(sK3)) | ~v1_funct_1(sK3) | ~v2_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl4_16 | ~spl4_53 | ~spl4_147)),
% 2.59/0.75    inference(forward_demodulation,[],[f1998,f373])).
% 2.59/0.75  fof(f373,plain,(
% 2.59/0.75    sK2 = k5_relat_1(sK2,k6_partfun1(sK1)) | ~spl4_16),
% 2.59/0.75    inference(avatar_component_clause,[],[f371])).
% 2.59/0.75  fof(f1998,plain,(
% 2.59/0.75    k5_relat_1(sK2,k6_partfun1(sK1)) = k5_relat_1(k6_partfun1(sK0),k2_funct_1(sK3)) | ~v1_relat_1(k2_funct_1(sK3)) | ~v1_funct_1(sK3) | ~v2_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl4_53 | ~spl4_147)),
% 2.59/0.75    inference(forward_demodulation,[],[f1142,f1842])).
% 2.59/0.75  fof(f1842,plain,(
% 2.59/0.75    sK1 = k1_relat_1(sK3) | ~spl4_147),
% 2.59/0.75    inference(avatar_component_clause,[],[f1840])).
% 2.59/0.75  fof(f1142,plain,(
% 2.59/0.75    k5_relat_1(k6_partfun1(sK0),k2_funct_1(sK3)) = k5_relat_1(sK2,k6_partfun1(k1_relat_1(sK3))) | ~v1_relat_1(k2_funct_1(sK3)) | ~v1_funct_1(sK3) | ~v2_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl4_53),
% 2.59/0.75    inference(superposition,[],[f873,f131])).
% 2.59/0.75  fof(f131,plain,(
% 2.59/0.75    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.59/0.75    inference(definition_unfolding,[],[f100,f82])).
% 2.59/0.75  fof(f100,plain,(
% 2.59/0.75    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) )),
% 2.59/0.75    inference(cnf_transformation,[],[f48])).
% 2.59/0.75  fof(f48,plain,(
% 2.59/0.75    ! [X0] : ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.59/0.75    inference(flattening,[],[f47])).
% 2.59/0.75  fof(f47,plain,(
% 2.59/0.75    ! [X0] : (((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.59/0.75    inference(ennf_transformation,[],[f19])).
% 2.59/0.75  fof(f19,axiom,(
% 2.59/0.75    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)))))),
% 2.59/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).
% 2.59/0.75  fof(f873,plain,(
% 2.59/0.75    ( ! [X0] : (k5_relat_1(sK2,k5_relat_1(sK3,X0)) = k5_relat_1(k6_partfun1(sK0),X0) | ~v1_relat_1(X0)) ) | ~spl4_53),
% 2.59/0.75    inference(avatar_component_clause,[],[f872])).
% 2.59/0.75  fof(f1969,plain,(
% 2.59/0.75    ~spl4_47 | ~spl4_1 | spl4_63 | ~spl4_84 | ~spl4_36 | ~spl4_51 | ~spl4_147),
% 2.59/0.75    inference(avatar_split_clause,[],[f1968,f1840,f850,f691,f1165,f968,f143,f802])).
% 2.59/0.75  fof(f1165,plain,(
% 2.59/0.75    spl4_84 <=> v2_funct_1(k6_partfun1(sK0))),
% 2.59/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_84])])).
% 2.59/0.75  fof(f691,plain,(
% 2.59/0.75    spl4_36 <=> ! [X7] : (sK1 != k1_relat_1(X7) | v2_funct_1(X7) | ~v1_relat_1(X7) | ~v2_funct_1(k5_relat_1(sK2,X7)) | ~v1_funct_1(X7))),
% 2.59/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).
% 2.59/0.75  fof(f850,plain,(
% 2.59/0.75    spl4_51 <=> k6_partfun1(sK0) = k5_relat_1(sK2,sK3)),
% 2.59/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_51])])).
% 2.59/0.75  fof(f1968,plain,(
% 2.59/0.75    ~v2_funct_1(k6_partfun1(sK0)) | v2_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | (~spl4_36 | ~spl4_51 | ~spl4_147)),
% 2.59/0.75    inference(forward_demodulation,[],[f1929,f852])).
% 2.59/0.75  fof(f852,plain,(
% 2.59/0.75    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~spl4_51),
% 2.59/0.75    inference(avatar_component_clause,[],[f850])).
% 2.59/0.75  fof(f1929,plain,(
% 2.59/0.75    v2_funct_1(sK3) | ~v1_relat_1(sK3) | ~v2_funct_1(k5_relat_1(sK2,sK3)) | ~v1_funct_1(sK3) | (~spl4_36 | ~spl4_147)),
% 2.59/0.75    inference(trivial_inequality_removal,[],[f1927])).
% 2.59/0.75  fof(f1927,plain,(
% 2.59/0.75    sK1 != sK1 | v2_funct_1(sK3) | ~v1_relat_1(sK3) | ~v2_funct_1(k5_relat_1(sK2,sK3)) | ~v1_funct_1(sK3) | (~spl4_36 | ~spl4_147)),
% 2.59/0.75    inference(superposition,[],[f692,f1842])).
% 2.59/0.75  fof(f692,plain,(
% 2.59/0.75    ( ! [X7] : (sK1 != k1_relat_1(X7) | v2_funct_1(X7) | ~v1_relat_1(X7) | ~v2_funct_1(k5_relat_1(sK2,X7)) | ~v1_funct_1(X7)) ) | ~spl4_36),
% 2.59/0.75    inference(avatar_component_clause,[],[f691])).
% 2.59/0.75  fof(f1869,plain,(
% 2.59/0.75    spl4_148),
% 2.59/0.75    inference(avatar_contradiction_clause,[],[f1864])).
% 2.59/0.75  fof(f1864,plain,(
% 2.59/0.75    $false | spl4_148),
% 2.59/0.75    inference(subsumption_resolution,[],[f177,f1851])).
% 2.59/0.75  fof(f1851,plain,(
% 2.59/0.75    ~v4_relat_1(sK2,sK0) | spl4_148),
% 2.59/0.75    inference(avatar_component_clause,[],[f1849])).
% 2.59/0.75  fof(f1849,plain,(
% 2.59/0.75    spl4_148 <=> v4_relat_1(sK2,sK0)),
% 2.59/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_148])])).
% 2.59/0.75  fof(f177,plain,(
% 2.59/0.75    v4_relat_1(sK2,sK0)),
% 2.59/0.75    inference(resolution,[],[f115,f81])).
% 2.59/0.75  fof(f81,plain,(
% 2.59/0.75    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.59/0.75    inference(cnf_transformation,[],[f33])).
% 2.59/0.75  fof(f115,plain,(
% 2.59/0.75    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 2.59/0.75    inference(cnf_transformation,[],[f61])).
% 2.59/0.75  fof(f61,plain,(
% 2.59/0.75    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.59/0.75    inference(ennf_transformation,[],[f21])).
% 2.59/0.75  fof(f21,axiom,(
% 2.59/0.75    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.59/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 2.59/0.75  fof(f1863,plain,(
% 2.59/0.75    ~spl4_148 | ~spl4_3 | spl4_147 | ~spl4_10 | ~spl4_142),
% 2.59/0.75    inference(avatar_split_clause,[],[f1862,f1802,f330,f1840,f152,f1849])).
% 2.59/0.75  fof(f152,plain,(
% 2.59/0.75    spl4_3 <=> v1_relat_1(sK2)),
% 2.59/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 2.59/0.75  fof(f330,plain,(
% 2.59/0.75    spl4_10 <=> sK1 = k2_relat_1(sK2)),
% 2.59/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 2.59/0.75  fof(f1802,plain,(
% 2.59/0.75    spl4_142 <=> k1_relat_1(sK3) = k9_relat_1(sK2,sK0)),
% 2.59/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_142])])).
% 2.59/0.75  fof(f1862,plain,(
% 2.59/0.75    sK1 = k1_relat_1(sK3) | ~v1_relat_1(sK2) | ~v4_relat_1(sK2,sK0) | (~spl4_10 | ~spl4_142)),
% 2.59/0.75    inference(forward_demodulation,[],[f1846,f332])).
% 2.59/0.75  fof(f332,plain,(
% 2.59/0.75    sK1 = k2_relat_1(sK2) | ~spl4_10),
% 2.59/0.75    inference(avatar_component_clause,[],[f330])).
% 2.59/0.75  fof(f1846,plain,(
% 2.59/0.75    k1_relat_1(sK3) = k2_relat_1(sK2) | ~v1_relat_1(sK2) | ~v4_relat_1(sK2,sK0) | ~spl4_142),
% 2.59/0.75    inference(superposition,[],[f203,f1804])).
% 2.59/0.75  fof(f1804,plain,(
% 2.59/0.75    k1_relat_1(sK3) = k9_relat_1(sK2,sK0) | ~spl4_142),
% 2.59/0.75    inference(avatar_component_clause,[],[f1802])).
% 2.59/0.75  fof(f203,plain,(
% 2.59/0.75    ( ! [X0,X1] : (k2_relat_1(X0) = k9_relat_1(X0,X1) | ~v1_relat_1(X0) | ~v4_relat_1(X0,X1)) )),
% 2.59/0.75    inference(duplicate_literal_removal,[],[f200])).
% 2.59/0.75  fof(f200,plain,(
% 2.59/0.75    ( ! [X0,X1] : (k2_relat_1(X0) = k9_relat_1(X0,X1) | ~v1_relat_1(X0) | ~v4_relat_1(X0,X1) | ~v1_relat_1(X0)) )),
% 2.59/0.75    inference(superposition,[],[f106,f111])).
% 2.59/0.75  fof(f106,plain,(
% 2.59/0.75    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.59/0.75    inference(cnf_transformation,[],[f52])).
% 2.59/0.75  fof(f52,plain,(
% 2.59/0.75    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.59/0.75    inference(ennf_transformation,[],[f6])).
% 2.59/0.75  fof(f6,axiom,(
% 2.59/0.75    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 2.59/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 2.59/0.75  fof(f1831,plain,(
% 2.59/0.75    ~spl4_1 | spl4_143),
% 2.59/0.75    inference(avatar_contradiction_clause,[],[f1829])).
% 2.59/0.75  fof(f1829,plain,(
% 2.59/0.75    $false | (~spl4_1 | spl4_143)),
% 2.59/0.75    inference(unit_resulting_resolution,[],[f145,f176,f1808,f109])).
% 2.59/0.75  fof(f109,plain,(
% 2.59/0.75    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1) | ~v4_relat_1(X1,X0)) )),
% 2.59/0.75    inference(cnf_transformation,[],[f55])).
% 2.59/0.75  fof(f55,plain,(
% 2.59/0.75    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.59/0.75    inference(ennf_transformation,[],[f3])).
% 2.59/0.75  fof(f3,axiom,(
% 2.59/0.75    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 2.59/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 2.59/0.75  fof(f1808,plain,(
% 2.59/0.75    ~r1_tarski(k1_relat_1(sK3),sK1) | spl4_143),
% 2.59/0.75    inference(avatar_component_clause,[],[f1806])).
% 2.59/0.75  fof(f1806,plain,(
% 2.59/0.75    spl4_143 <=> r1_tarski(k1_relat_1(sK3),sK1)),
% 2.59/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_143])])).
% 2.59/0.75  fof(f176,plain,(
% 2.59/0.75    v4_relat_1(sK3,sK1)),
% 2.59/0.75    inference(resolution,[],[f115,f72])).
% 2.59/0.75  fof(f72,plain,(
% 2.59/0.75    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.59/0.75    inference(cnf_transformation,[],[f33])).
% 2.59/0.75  fof(f145,plain,(
% 2.59/0.75    v1_relat_1(sK3) | ~spl4_1),
% 2.59/0.75    inference(avatar_component_clause,[],[f143])).
% 2.59/0.75  fof(f1809,plain,(
% 2.59/0.75    ~spl4_1 | ~spl4_3 | ~spl4_11 | spl4_142 | ~spl4_143 | ~spl4_10 | ~spl4_51),
% 2.59/0.75    inference(avatar_split_clause,[],[f1800,f850,f330,f1806,f1802,f347,f152,f143])).
% 2.59/0.75  fof(f347,plain,(
% 2.59/0.75    spl4_11 <=> v1_funct_1(sK2)),
% 2.59/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 2.59/0.75  fof(f1800,plain,(
% 2.59/0.75    ~r1_tarski(k1_relat_1(sK3),sK1) | k1_relat_1(sK3) = k9_relat_1(sK2,sK0) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_relat_1(sK3) | (~spl4_10 | ~spl4_51)),
% 2.59/0.75    inference(forward_demodulation,[],[f1799,f332])).
% 2.59/0.75  fof(f1799,plain,(
% 2.59/0.75    k1_relat_1(sK3) = k9_relat_1(sK2,sK0) | ~v1_funct_1(sK2) | ~r1_tarski(k1_relat_1(sK3),k2_relat_1(sK2)) | ~v1_relat_1(sK2) | ~v1_relat_1(sK3) | ~spl4_51),
% 2.59/0.75    inference(forward_demodulation,[],[f1727,f127])).
% 2.59/0.75  fof(f127,plain,(
% 2.59/0.75    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 2.59/0.75    inference(definition_unfolding,[],[f86,f82])).
% 2.59/0.75  fof(f86,plain,(
% 2.59/0.75    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 2.59/0.75    inference(cnf_transformation,[],[f10])).
% 2.59/0.75  fof(f10,axiom,(
% 2.59/0.75    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 2.59/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 2.59/0.75  fof(f1727,plain,(
% 2.59/0.75    k1_relat_1(sK3) = k9_relat_1(sK2,k1_relat_1(k6_partfun1(sK0))) | ~v1_funct_1(sK2) | ~r1_tarski(k1_relat_1(sK3),k2_relat_1(sK2)) | ~v1_relat_1(sK2) | ~v1_relat_1(sK3) | ~spl4_51),
% 2.59/0.75    inference(superposition,[],[f503,f852])).
% 2.59/0.75  fof(f503,plain,(
% 2.59/0.75    ( ! [X0,X1] : (k1_relat_1(X1) = k9_relat_1(X0,k1_relat_1(k5_relat_1(X0,X1))) | ~v1_funct_1(X0) | ~r1_tarski(k1_relat_1(X1),k2_relat_1(X0)) | ~v1_relat_1(X0) | ~v1_relat_1(X1)) )),
% 2.59/0.75    inference(duplicate_literal_removal,[],[f493])).
% 2.59/0.75  fof(f493,plain,(
% 2.59/0.75    ( ! [X0,X1] : (k1_relat_1(X1) = k9_relat_1(X0,k1_relat_1(k5_relat_1(X0,X1))) | ~v1_funct_1(X0) | ~r1_tarski(k1_relat_1(X1),k2_relat_1(X0)) | ~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.59/0.75    inference(superposition,[],[f110,f90])).
% 2.59/0.75  fof(f90,plain,(
% 2.59/0.75    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.59/0.75    inference(cnf_transformation,[],[f36])).
% 2.59/0.75  fof(f36,plain,(
% 2.59/0.75    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.59/0.75    inference(ennf_transformation,[],[f7])).
% 2.59/0.75  fof(f7,axiom,(
% 2.59/0.75    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 2.59/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).
% 2.59/0.75  fof(f110,plain,(
% 2.59/0.75    ( ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~v1_funct_1(X1) | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.59/0.75    inference(cnf_transformation,[],[f57])).
% 2.59/0.75  fof(f57,plain,(
% 2.59/0.75    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.59/0.75    inference(flattening,[],[f56])).
% 2.59/0.75  fof(f56,plain,(
% 2.59/0.75    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.59/0.75    inference(ennf_transformation,[],[f16])).
% 2.59/0.75  fof(f16,axiom,(
% 2.59/0.75    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 2.59/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).
% 2.59/0.75  fof(f1184,plain,(
% 2.59/0.75    spl4_84),
% 2.59/0.75    inference(avatar_contradiction_clause,[],[f1181])).
% 2.59/0.75  fof(f1181,plain,(
% 2.59/0.75    $false | spl4_84),
% 2.59/0.75    inference(unit_resulting_resolution,[],[f124,f1167])).
% 2.59/0.75  fof(f1167,plain,(
% 2.59/0.75    ~v2_funct_1(k6_partfun1(sK0)) | spl4_84),
% 2.59/0.75    inference(avatar_component_clause,[],[f1165])).
% 2.59/0.75  fof(f124,plain,(
% 2.59/0.75    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 2.59/0.75    inference(definition_unfolding,[],[f85,f82])).
% 2.59/0.75  fof(f85,plain,(
% 2.59/0.75    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 2.59/0.75    inference(cnf_transformation,[],[f15])).
% 2.59/0.75  fof(f15,axiom,(
% 2.59/0.75    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 2.59/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).
% 2.59/0.75  fof(f1101,plain,(
% 2.59/0.75    spl4_79),
% 2.59/0.75    inference(avatar_contradiction_clause,[],[f1096])).
% 2.59/0.75  fof(f1096,plain,(
% 2.59/0.75    $false | spl4_79),
% 2.59/0.75    inference(unit_resulting_resolution,[],[f125,f1080,f206])).
% 2.59/0.75  fof(f206,plain,(
% 2.59/0.75    ( ! [X0] : (~v1_relat_1(k6_partfun1(X0)) | r1_tarski(X0,X0)) )),
% 2.59/0.75    inference(resolution,[],[f174,f178])).
% 2.59/0.75  fof(f178,plain,(
% 2.59/0.75    ( ! [X0] : (v4_relat_1(k6_partfun1(X0),X0)) )),
% 2.59/0.75    inference(resolution,[],[f115,f123])).
% 2.59/0.75  fof(f123,plain,(
% 2.59/0.75    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.59/0.75    inference(definition_unfolding,[],[f83,f82])).
% 2.59/0.75  fof(f83,plain,(
% 2.59/0.75    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.59/0.75    inference(cnf_transformation,[],[f24])).
% 2.59/0.75  fof(f24,axiom,(
% 2.59/0.75    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 2.59/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).
% 2.59/0.75  fof(f174,plain,(
% 2.59/0.75    ( ! [X0,X1] : (~v4_relat_1(k6_partfun1(X0),X1) | ~v1_relat_1(k6_partfun1(X0)) | r1_tarski(X0,X1)) )),
% 2.59/0.75    inference(superposition,[],[f109,f127])).
% 2.59/0.75  fof(f1080,plain,(
% 2.59/0.75    ~r1_tarski(sK0,sK0) | spl4_79),
% 2.59/0.75    inference(avatar_component_clause,[],[f1078])).
% 2.59/0.75  fof(f125,plain,(
% 2.59/0.75    ( ! [X0] : (v1_relat_1(k6_partfun1(X0))) )),
% 2.59/0.75    inference(definition_unfolding,[],[f84,f82])).
% 2.59/0.75  fof(f84,plain,(
% 2.59/0.75    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 2.59/0.75    inference(cnf_transformation,[],[f15])).
% 2.59/0.75  fof(f1018,plain,(
% 2.59/0.75    ~spl4_1 | spl4_69),
% 2.59/0.75    inference(avatar_contradiction_clause,[],[f1016])).
% 2.59/0.75  fof(f1016,plain,(
% 2.59/0.75    $false | (~spl4_1 | spl4_69)),
% 2.59/0.75    inference(unit_resulting_resolution,[],[f145,f70,f997,f95])).
% 2.59/0.75  fof(f95,plain,(
% 2.59/0.75    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.59/0.75    inference(cnf_transformation,[],[f42])).
% 2.59/0.75  fof(f42,plain,(
% 2.59/0.75    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.59/0.75    inference(flattening,[],[f41])).
% 2.59/0.75  fof(f41,plain,(
% 2.59/0.75    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.59/0.75    inference(ennf_transformation,[],[f14])).
% 2.59/0.75  fof(f14,axiom,(
% 2.59/0.75    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 2.59/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 2.59/0.75  fof(f997,plain,(
% 2.59/0.75    ~v1_relat_1(k2_funct_1(sK3)) | spl4_69),
% 2.59/0.75    inference(avatar_component_clause,[],[f995])).
% 2.59/0.75  fof(f70,plain,(
% 2.59/0.75    v1_funct_1(sK3)),
% 2.59/0.75    inference(cnf_transformation,[],[f33])).
% 2.59/0.75  fof(f1006,plain,(
% 2.59/0.75    ~spl4_1 | ~spl4_63 | ~spl4_47 | ~spl4_69 | spl4_71 | ~spl4_58),
% 2.59/0.75    inference(avatar_split_clause,[],[f955,f919,f1003,f995,f802,f968,f143])).
% 2.59/0.75  fof(f955,plain,(
% 2.59/0.75    v4_relat_1(k2_funct_1(sK3),sK0) | ~v1_relat_1(k2_funct_1(sK3)) | ~v1_funct_1(sK3) | ~v2_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl4_58),
% 2.59/0.75    inference(superposition,[],[f300,f921])).
% 2.59/0.75  fof(f300,plain,(
% 2.59/0.75    ( ! [X7] : (v4_relat_1(k2_funct_1(X7),k2_relat_1(X7)) | ~v1_relat_1(k2_funct_1(X7)) | ~v1_funct_1(X7) | ~v2_funct_1(X7) | ~v1_relat_1(X7)) )),
% 2.59/0.75    inference(superposition,[],[f211,f98])).
% 2.59/0.75  fof(f211,plain,(
% 2.59/0.75    ( ! [X1] : (v4_relat_1(X1,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.59/0.75    inference(resolution,[],[f209,f108])).
% 2.59/0.75  fof(f108,plain,(
% 2.59/0.75    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1) | v4_relat_1(X1,X0)) )),
% 2.59/0.75    inference(cnf_transformation,[],[f55])).
% 2.59/0.75  fof(f209,plain,(
% 2.59/0.75    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 2.59/0.75    inference(resolution,[],[f206,f125])).
% 2.59/0.75  fof(f923,plain,(
% 2.59/0.75    ~spl4_46 | spl4_58 | ~spl4_54),
% 2.59/0.75    inference(avatar_split_clause,[],[f917,f895,f919,f798])).
% 2.59/0.75  fof(f798,plain,(
% 2.59/0.75    spl4_46 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.59/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).
% 2.59/0.75  fof(f895,plain,(
% 2.59/0.75    spl4_54 <=> sK0 = k2_relset_1(sK1,sK0,sK3)),
% 2.59/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_54])])).
% 2.59/0.75  fof(f917,plain,(
% 2.59/0.75    sK0 = k2_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_54),
% 2.59/0.75    inference(superposition,[],[f114,f897])).
% 2.59/0.75  fof(f897,plain,(
% 2.59/0.75    sK0 = k2_relset_1(sK1,sK0,sK3) | ~spl4_54),
% 2.59/0.75    inference(avatar_component_clause,[],[f895])).
% 2.59/0.75  fof(f114,plain,(
% 2.59/0.75    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.59/0.75    inference(cnf_transformation,[],[f60])).
% 2.59/0.75  fof(f60,plain,(
% 2.59/0.75    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.59/0.75    inference(ennf_transformation,[],[f22])).
% 2.59/0.75  fof(f22,axiom,(
% 2.59/0.75    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 2.59/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 2.59/0.75  fof(f915,plain,(
% 2.59/0.75    spl4_56),
% 2.59/0.75    inference(avatar_contradiction_clause,[],[f914])).
% 2.59/0.75  fof(f914,plain,(
% 2.59/0.75    $false | spl4_56),
% 2.59/0.75    inference(subsumption_resolution,[],[f71,f905])).
% 2.59/0.75  fof(f905,plain,(
% 2.59/0.75    ~v1_funct_2(sK3,sK1,sK0) | spl4_56),
% 2.59/0.75    inference(avatar_component_clause,[],[f903])).
% 2.59/0.75  fof(f903,plain,(
% 2.59/0.75    spl4_56 <=> v1_funct_2(sK3,sK1,sK0)),
% 2.59/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_56])])).
% 2.59/0.75  fof(f71,plain,(
% 2.59/0.75    v1_funct_2(sK3,sK1,sK0)),
% 2.59/0.75    inference(cnf_transformation,[],[f33])).
% 2.59/0.75  fof(f913,plain,(
% 2.59/0.75    spl4_55),
% 2.59/0.75    inference(avatar_contradiction_clause,[],[f912])).
% 2.59/0.75  fof(f912,plain,(
% 2.59/0.75    $false | spl4_55),
% 2.59/0.75    inference(subsumption_resolution,[],[f80,f901])).
% 2.59/0.75  fof(f901,plain,(
% 2.59/0.75    ~v1_funct_2(sK2,sK0,sK1) | spl4_55),
% 2.59/0.75    inference(avatar_component_clause,[],[f899])).
% 2.59/0.75  fof(f899,plain,(
% 2.59/0.75    spl4_55 <=> v1_funct_2(sK2,sK0,sK1)),
% 2.59/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_55])])).
% 2.59/0.75  fof(f80,plain,(
% 2.59/0.75    v1_funct_2(sK2,sK0,sK1)),
% 2.59/0.75    inference(cnf_transformation,[],[f33])).
% 2.59/0.75  fof(f906,plain,(
% 2.59/0.75    spl4_54 | ~spl4_47 | ~spl4_9 | ~spl4_55 | ~spl4_11 | ~spl4_46 | ~spl4_56),
% 2.59/0.75    inference(avatar_split_clause,[],[f890,f903,f798,f347,f899,f326,f802,f895])).
% 2.59/0.75  fof(f326,plain,(
% 2.59/0.75    spl4_9 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.59/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 2.59/0.75  fof(f890,plain,(
% 2.59/0.75    ~v1_funct_2(sK3,sK1,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | sK0 = k2_relset_1(sK1,sK0,sK3)),
% 2.59/0.75    inference(resolution,[],[f117,f74])).
% 2.59/0.75  fof(f74,plain,(
% 2.59/0.75    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 2.59/0.75    inference(cnf_transformation,[],[f33])).
% 2.59/0.75  fof(f117,plain,(
% 2.59/0.75    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_1(X2) | k2_relset_1(X0,X1,X2) = X1) )),
% 2.59/0.75    inference(cnf_transformation,[],[f63])).
% 2.59/0.75  fof(f63,plain,(
% 2.59/0.75    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.59/0.75    inference(flattening,[],[f62])).
% 2.59/0.75  fof(f62,plain,(
% 2.59/0.75    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.59/0.75    inference(ennf_transformation,[],[f28])).
% 2.59/0.75  fof(f28,axiom,(
% 2.59/0.75    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 2.59/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_2)).
% 2.59/0.75  fof(f874,plain,(
% 2.59/0.75    ~spl4_3 | ~spl4_1 | spl4_53 | ~spl4_51),
% 2.59/0.75    inference(avatar_split_clause,[],[f870,f850,f872,f143,f152])).
% 2.59/0.75  fof(f870,plain,(
% 2.59/0.75    ( ! [X0] : (k5_relat_1(sK2,k5_relat_1(sK3,X0)) = k5_relat_1(k6_partfun1(sK0),X0) | ~v1_relat_1(sK3) | ~v1_relat_1(X0) | ~v1_relat_1(sK2)) ) | ~spl4_51),
% 2.59/0.75    inference(superposition,[],[f91,f852])).
% 2.59/0.75  fof(f91,plain,(
% 2.59/0.75    ( ! [X2,X0,X1] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | ~v1_relat_1(X0)) )),
% 2.59/0.75    inference(cnf_transformation,[],[f37])).
% 2.59/0.75  fof(f37,plain,(
% 2.59/0.75    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.59/0.75    inference(ennf_transformation,[],[f9])).
% 2.59/0.75  fof(f9,axiom,(
% 2.59/0.75    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)))))),
% 2.59/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).
% 2.59/0.75  fof(f861,plain,(
% 2.59/0.75    ~spl4_11 | ~spl4_46 | ~spl4_47 | ~spl4_9 | spl4_51 | ~spl4_45),
% 2.59/0.75    inference(avatar_split_clause,[],[f858,f774,f850,f326,f802,f798,f347])).
% 2.59/0.75  fof(f774,plain,(
% 2.59/0.75    spl4_45 <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)),
% 2.59/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).
% 2.59/0.75  fof(f858,plain,(
% 2.59/0.75    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK2) | ~spl4_45),
% 2.59/0.75    inference(superposition,[],[f120,f776])).
% 2.59/0.75  fof(f776,plain,(
% 2.59/0.75    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) | ~spl4_45),
% 2.59/0.75    inference(avatar_component_clause,[],[f774])).
% 2.59/0.75  fof(f120,plain,(
% 2.59/0.75    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X4)) )),
% 2.59/0.75    inference(cnf_transformation,[],[f67])).
% 2.59/0.75  fof(f67,plain,(
% 2.59/0.75    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.59/0.75    inference(flattening,[],[f66])).
% 2.59/0.75  fof(f66,plain,(
% 2.59/0.75    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.59/0.75    inference(ennf_transformation,[],[f26])).
% 2.59/0.75  fof(f26,axiom,(
% 2.59/0.75    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 2.59/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 2.59/0.75  fof(f847,plain,(
% 2.59/0.75    spl4_44),
% 2.59/0.75    inference(avatar_contradiction_clause,[],[f834])).
% 2.59/0.75  fof(f834,plain,(
% 2.59/0.75    $false | spl4_44),
% 2.59/0.75    inference(unit_resulting_resolution,[],[f79,f70,f72,f81,f772,f122])).
% 2.59/0.75  fof(f122,plain,(
% 2.59/0.75    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X4)) )),
% 2.59/0.75    inference(cnf_transformation,[],[f69])).
% 2.59/0.75  fof(f69,plain,(
% 2.59/0.75    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.59/0.75    inference(flattening,[],[f68])).
% 2.59/0.75  fof(f68,plain,(
% 2.59/0.75    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.59/0.75    inference(ennf_transformation,[],[f25])).
% 2.59/0.75  fof(f25,axiom,(
% 2.59/0.75    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 2.59/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 2.59/0.75  fof(f772,plain,(
% 2.59/0.75    ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl4_44),
% 2.59/0.75    inference(avatar_component_clause,[],[f770])).
% 2.59/0.75  fof(f770,plain,(
% 2.59/0.75    spl4_44 <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.59/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).
% 2.59/0.75  fof(f79,plain,(
% 2.59/0.75    v1_funct_1(sK2)),
% 2.59/0.75    inference(cnf_transformation,[],[f33])).
% 2.59/0.75  fof(f826,plain,(
% 2.59/0.75    spl4_47),
% 2.59/0.75    inference(avatar_contradiction_clause,[],[f825])).
% 2.59/0.75  fof(f825,plain,(
% 2.59/0.75    $false | spl4_47),
% 2.59/0.75    inference(subsumption_resolution,[],[f70,f804])).
% 2.59/0.75  fof(f804,plain,(
% 2.59/0.75    ~v1_funct_1(sK3) | spl4_47),
% 2.59/0.75    inference(avatar_component_clause,[],[f802])).
% 2.59/0.75  fof(f824,plain,(
% 2.59/0.75    spl4_46),
% 2.59/0.75    inference(avatar_contradiction_clause,[],[f820])).
% 2.59/0.75  fof(f820,plain,(
% 2.59/0.75    $false | spl4_46),
% 2.59/0.75    inference(subsumption_resolution,[],[f72,f800])).
% 2.59/0.75  fof(f800,plain,(
% 2.59/0.75    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl4_46),
% 2.59/0.75    inference(avatar_component_clause,[],[f798])).
% 2.59/0.75  fof(f777,plain,(
% 2.59/0.75    ~spl4_44 | spl4_45),
% 2.59/0.75    inference(avatar_split_clause,[],[f768,f774,f770])).
% 2.59/0.75  fof(f768,plain,(
% 2.59/0.75    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) | ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.59/0.75    inference(resolution,[],[f745,f74])).
% 2.59/0.75  fof(f745,plain,(
% 2.59/0.75    ( ! [X2,X3] : (~r2_relset_1(X3,X3,X2,k6_partfun1(X3)) | k6_partfun1(X3) = X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X3)))) )),
% 2.59/0.75    inference(resolution,[],[f119,f123])).
% 2.59/0.75  fof(f119,plain,(
% 2.59/0.75    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 = X3 | ~r2_relset_1(X0,X1,X2,X3)) )),
% 2.59/0.75    inference(cnf_transformation,[],[f65])).
% 2.59/0.75  fof(f65,plain,(
% 2.59/0.75    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.59/0.75    inference(flattening,[],[f64])).
% 2.59/0.75  fof(f64,plain,(
% 2.59/0.75    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.59/0.75    inference(ennf_transformation,[],[f23])).
% 2.59/0.75  fof(f23,axiom,(
% 2.59/0.75    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 2.59/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 2.59/0.75  fof(f693,plain,(
% 2.59/0.75    ~spl4_11 | ~spl4_3 | spl4_36 | ~spl4_10),
% 2.59/0.75    inference(avatar_split_clause,[],[f689,f330,f691,f152,f347])).
% 2.59/0.75  fof(f689,plain,(
% 2.59/0.75    ( ! [X7] : (sK1 != k1_relat_1(X7) | ~v1_funct_1(X7) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v2_funct_1(k5_relat_1(sK2,X7)) | ~v1_relat_1(X7) | v2_funct_1(X7)) ) | ~spl4_10),
% 2.59/0.75    inference(superposition,[],[f103,f332])).
% 2.59/0.75  fof(f103,plain,(
% 2.59/0.75    ( ! [X0,X1] : (k1_relat_1(X0) != k2_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_relat_1(X0) | v2_funct_1(X0)) )),
% 2.59/0.75    inference(cnf_transformation,[],[f50])).
% 2.59/0.75  fof(f50,plain,(
% 2.59/0.75    ! [X0] : (! [X1] : ((v2_funct_1(X0) & v2_funct_1(X1)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.59/0.75    inference(flattening,[],[f49])).
% 2.59/0.75  fof(f49,plain,(
% 2.59/0.75    ! [X0] : (! [X1] : (((v2_funct_1(X0) & v2_funct_1(X1)) | (k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.59/0.75    inference(ennf_transformation,[],[f17])).
% 2.59/0.75  fof(f17,axiom,(
% 2.59/0.75    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(k5_relat_1(X1,X0))) => (v2_funct_1(X0) & v2_funct_1(X1)))))),
% 2.59/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_1)).
% 2.59/0.75  fof(f376,plain,(
% 2.59/0.75    spl4_11),
% 2.59/0.75    inference(avatar_contradiction_clause,[],[f375])).
% 2.59/0.75  fof(f375,plain,(
% 2.59/0.75    $false | spl4_11),
% 2.59/0.75    inference(subsumption_resolution,[],[f79,f349])).
% 2.59/0.75  fof(f349,plain,(
% 2.59/0.75    ~v1_funct_1(sK2) | spl4_11),
% 2.59/0.75    inference(avatar_component_clause,[],[f347])).
% 2.59/0.75  fof(f374,plain,(
% 2.59/0.75    ~spl4_3 | spl4_16 | ~spl4_10),
% 2.59/0.75    inference(avatar_split_clause,[],[f345,f330,f371,f152])).
% 2.59/0.75  fof(f345,plain,(
% 2.59/0.75    sK2 = k5_relat_1(sK2,k6_partfun1(sK1)) | ~v1_relat_1(sK2) | ~spl4_10),
% 2.59/0.75    inference(superposition,[],[f128,f332])).
% 2.59/0.75  fof(f128,plain,(
% 2.59/0.75    ( ! [X0] : (k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 2.59/0.75    inference(definition_unfolding,[],[f88,f82])).
% 2.59/0.75  fof(f88,plain,(
% 2.59/0.75    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0) )),
% 2.59/0.75    inference(cnf_transformation,[],[f34])).
% 2.59/0.75  fof(f34,plain,(
% 2.59/0.75    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 2.59/0.75    inference(ennf_transformation,[],[f12])).
% 2.59/0.75  fof(f12,axiom,(
% 2.59/0.75    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 2.59/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).
% 2.59/0.75  fof(f339,plain,(
% 2.59/0.75    spl4_9),
% 2.59/0.75    inference(avatar_contradiction_clause,[],[f335])).
% 2.59/0.75  fof(f335,plain,(
% 2.59/0.75    $false | spl4_9),
% 2.59/0.75    inference(subsumption_resolution,[],[f81,f328])).
% 2.59/0.75  fof(f328,plain,(
% 2.59/0.75    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl4_9),
% 2.59/0.75    inference(avatar_component_clause,[],[f326])).
% 2.59/0.75  fof(f334,plain,(
% 2.59/0.75    ~spl4_9 | spl4_10),
% 2.59/0.75    inference(avatar_split_clause,[],[f324,f330,f326])).
% 2.59/0.75  fof(f324,plain,(
% 2.59/0.75    sK1 = k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.59/0.75    inference(superposition,[],[f73,f114])).
% 2.59/0.75  fof(f73,plain,(
% 2.59/0.75    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 2.59/0.75    inference(cnf_transformation,[],[f33])).
% 2.59/0.75  fof(f167,plain,(
% 2.59/0.75    spl4_4),
% 2.59/0.75    inference(avatar_contradiction_clause,[],[f164])).
% 2.59/0.75  fof(f164,plain,(
% 2.59/0.75    $false | spl4_4),
% 2.59/0.75    inference(unit_resulting_resolution,[],[f104,f158])).
% 2.59/0.75  fof(f158,plain,(
% 2.59/0.75    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | spl4_4),
% 2.59/0.75    inference(avatar_component_clause,[],[f156])).
% 2.59/0.75  fof(f156,plain,(
% 2.59/0.75    spl4_4 <=> v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 2.59/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 2.59/0.75  fof(f104,plain,(
% 2.59/0.75    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.59/0.75    inference(cnf_transformation,[],[f5])).
% 2.59/0.75  fof(f5,axiom,(
% 2.59/0.75    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.59/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 2.59/0.75  fof(f163,plain,(
% 2.59/0.75    spl4_2),
% 2.59/0.75    inference(avatar_contradiction_clause,[],[f160])).
% 2.59/0.75  fof(f160,plain,(
% 2.59/0.75    $false | spl4_2),
% 2.59/0.75    inference(unit_resulting_resolution,[],[f104,f149])).
% 2.59/0.75  fof(f149,plain,(
% 2.59/0.75    ~v1_relat_1(k2_zfmisc_1(sK1,sK0)) | spl4_2),
% 2.59/0.75    inference(avatar_component_clause,[],[f147])).
% 2.59/0.75  fof(f147,plain,(
% 2.59/0.75    spl4_2 <=> v1_relat_1(k2_zfmisc_1(sK1,sK0))),
% 2.59/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 2.59/0.75  fof(f159,plain,(
% 2.59/0.75    spl4_3 | ~spl4_4),
% 2.59/0.75    inference(avatar_split_clause,[],[f139,f156,f152])).
% 2.59/0.75  fof(f139,plain,(
% 2.59/0.75    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | v1_relat_1(sK2)),
% 2.59/0.75    inference(resolution,[],[f92,f81])).
% 2.59/0.75  fof(f92,plain,(
% 2.59/0.75    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 2.59/0.75    inference(cnf_transformation,[],[f38])).
% 2.59/0.75  fof(f38,plain,(
% 2.59/0.75    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.59/0.75    inference(ennf_transformation,[],[f2])).
% 2.59/0.75  fof(f2,axiom,(
% 2.59/0.75    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.59/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 2.59/0.75  fof(f150,plain,(
% 2.59/0.75    spl4_1 | ~spl4_2),
% 2.59/0.75    inference(avatar_split_clause,[],[f138,f147,f143])).
% 2.59/0.75  fof(f138,plain,(
% 2.59/0.75    ~v1_relat_1(k2_zfmisc_1(sK1,sK0)) | v1_relat_1(sK3)),
% 2.59/0.75    inference(resolution,[],[f92,f72])).
% 2.59/0.75  % SZS output end Proof for theBenchmark
% 2.59/0.75  % (837)------------------------------
% 2.59/0.75  % (837)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.59/0.75  % (837)Termination reason: Refutation
% 2.59/0.75  
% 2.59/0.75  % (837)Memory used [KB]: 8827
% 2.59/0.75  % (837)Time elapsed: 0.312 s
% 2.59/0.75  % (837)------------------------------
% 2.59/0.75  % (837)------------------------------
% 2.59/0.76  % (823)Success in time 0.396 s
%------------------------------------------------------------------------------
