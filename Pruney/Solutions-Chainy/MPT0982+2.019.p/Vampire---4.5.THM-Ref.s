%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:01:29 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.33s
% Verified   : 
% Statistics : Number of formulae       :  152 ( 437 expanded)
%              Number of leaves         :   28 ( 144 expanded)
%              Depth                    :   15
%              Number of atoms          :  516 (3112 expanded)
%              Number of equality atoms :  123 ( 927 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f667,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f169,f266,f296,f486,f523,f529,f594,f600,f610,f666])).

fof(f666,plain,
    ( ~ spl8_5
    | ~ spl8_36
    | ~ spl8_41 ),
    inference(avatar_contradiction_clause,[],[f665])).

fof(f665,plain,
    ( $false
    | ~ spl8_5
    | ~ spl8_36
    | ~ spl8_41 ),
    inference(subsumption_resolution,[],[f664,f129])).

fof(f129,plain,(
    sK4 != k2_relat_1(sK6) ),
    inference(subsumption_resolution,[],[f118,f51])).

fof(f51,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,
    ( sK4 != k2_relset_1(sK3,sK4,sK6)
    & k1_xboole_0 != sK5
    & v2_funct_1(sK7)
    & sK5 = k2_relset_1(sK3,sK5,k1_partfun1(sK3,sK4,sK4,sK5,sK6,sK7))
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    & v1_funct_2(sK7,sK4,sK5)
    & v1_funct_1(sK7)
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    & v1_funct_2(sK6,sK3,sK4)
    & v1_funct_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7])],[f17,f39,f38])).

fof(f38,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( k2_relset_1(X0,X1,X3) != X1
            & k1_xboole_0 != X2
            & v2_funct_1(X4)
            & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( sK4 != k2_relset_1(sK3,sK4,sK6)
          & k1_xboole_0 != sK5
          & v2_funct_1(X4)
          & sK5 = k2_relset_1(sK3,sK5,k1_partfun1(sK3,sK4,sK4,sK5,sK6,X4))
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
          & v1_funct_2(X4,sK4,sK5)
          & v1_funct_1(X4) )
      & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
      & v1_funct_2(sK6,sK3,sK4)
      & v1_funct_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X4] :
        ( sK4 != k2_relset_1(sK3,sK4,sK6)
        & k1_xboole_0 != sK5
        & v2_funct_1(X4)
        & sK5 = k2_relset_1(sK3,sK5,k1_partfun1(sK3,sK4,sK4,sK5,sK6,X4))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
        & v1_funct_2(X4,sK4,sK5)
        & v1_funct_1(X4) )
   => ( sK4 != k2_relset_1(sK3,sK4,sK6)
      & k1_xboole_0 != sK5
      & v2_funct_1(sK7)
      & sK5 = k2_relset_1(sK3,sK5,k1_partfun1(sK3,sK4,sK4,sK5,sK6,sK7))
      & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
      & v1_funct_2(sK7,sK4,sK5)
      & v1_funct_1(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( k2_relset_1(X0,X1,X3) != X1
          & k1_xboole_0 != X2
          & v2_funct_1(X4)
          & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X4,X1,X2)
          & v1_funct_1(X4) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( k2_relset_1(X0,X1,X3) != X1
          & k1_xboole_0 != X2
          & v2_funct_1(X4)
          & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X4,X1,X2)
          & v1_funct_1(X4) )
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
            ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(X4,X1,X2)
              & v1_funct_1(X4) )
           => ( ( v2_funct_1(X4)
                & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 )
             => ( k2_relset_1(X0,X1,X3) = X1
                | k1_xboole_0 = X2 ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
         => ( ( v2_funct_1(X4)
              & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 )
           => ( k2_relset_1(X0,X1,X3) = X1
              | k1_xboole_0 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_funct_2)).

fof(f118,plain,
    ( sK4 != k2_relat_1(sK6)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(superposition,[],[f58,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f58,plain,(
    sK4 != k2_relset_1(sK3,sK4,sK6) ),
    inference(cnf_transformation,[],[f40])).

fof(f664,plain,
    ( sK4 = k2_relat_1(sK6)
    | ~ spl8_5
    | ~ spl8_36
    | ~ spl8_41 ),
    inference(forward_demodulation,[],[f663,f164])).

fof(f164,plain,
    ( sK4 = k1_relat_1(sK7)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f162])).

fof(f162,plain,
    ( spl8_5
  <=> sK4 = k1_relat_1(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f663,plain,
    ( k2_relat_1(sK6) = k1_relat_1(sK7)
    | ~ spl8_36
    | ~ spl8_41 ),
    inference(forward_demodulation,[],[f553,f589])).

fof(f589,plain,
    ( k2_relat_1(sK6) = k10_relat_1(sK7,sK5)
    | ~ spl8_41 ),
    inference(avatar_component_clause,[],[f587])).

fof(f587,plain,
    ( spl8_41
  <=> k2_relat_1(sK6) = k10_relat_1(sK7,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_41])])).

fof(f553,plain,
    ( k1_relat_1(sK7) = k10_relat_1(sK7,sK5)
    | ~ spl8_36 ),
    inference(subsumption_resolution,[],[f536,f91])).

fof(f91,plain,(
    v1_relat_1(sK7) ),
    inference(resolution,[],[f68,f54])).

fof(f54,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f40])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f536,plain,
    ( k1_relat_1(sK7) = k10_relat_1(sK7,sK5)
    | ~ v1_relat_1(sK7)
    | ~ spl8_36 ),
    inference(superposition,[],[f59,f476])).

fof(f476,plain,
    ( sK5 = k2_relat_1(sK7)
    | ~ spl8_36 ),
    inference(avatar_component_clause,[],[f474])).

fof(f474,plain,
    ( spl8_36
  <=> sK5 = k2_relat_1(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_36])])).

fof(f59,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(f610,plain,(
    ~ spl8_6 ),
    inference(avatar_contradiction_clause,[],[f609])).

fof(f609,plain,
    ( $false
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f608,f57])).

fof(f57,plain,(
    k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f40])).

fof(f608,plain,
    ( k1_xboole_0 = sK5
    | ~ spl8_6 ),
    inference(resolution,[],[f168,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X1) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f168,plain,
    ( sP0(sK4,sK5)
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f166])).

fof(f166,plain,
    ( spl8_6
  <=> sP0(sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f600,plain,(
    spl8_42 ),
    inference(avatar_contradiction_clause,[],[f599])).

fof(f599,plain,
    ( $false
    | spl8_42 ),
    inference(subsumption_resolution,[],[f598,f90])).

fof(f90,plain,(
    v1_relat_1(sK6) ),
    inference(resolution,[],[f68,f51])).

fof(f598,plain,
    ( ~ v1_relat_1(sK6)
    | spl8_42 ),
    inference(subsumption_resolution,[],[f595,f99])).

fof(f99,plain,(
    v5_relat_1(sK6,sK4) ),
    inference(resolution,[],[f72,f51])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f595,plain,
    ( ~ v5_relat_1(sK6,sK4)
    | ~ v1_relat_1(sK6)
    | spl8_42 ),
    inference(resolution,[],[f593,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f593,plain,
    ( ~ r1_tarski(k2_relat_1(sK6),sK4)
    | spl8_42 ),
    inference(avatar_component_clause,[],[f591])).

fof(f591,plain,
    ( spl8_42
  <=> r1_tarski(k2_relat_1(sK6),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_42])])).

fof(f594,plain,
    ( spl8_41
    | ~ spl8_42
    | ~ spl8_5
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f585,f262,f162,f591,f587])).

fof(f262,plain,
    ( spl8_8
  <=> sK5 = k2_relat_1(k5_relat_1(sK6,sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f585,plain,
    ( ~ r1_tarski(k2_relat_1(sK6),sK4)
    | k2_relat_1(sK6) = k10_relat_1(sK7,sK5)
    | ~ spl8_5
    | ~ spl8_8 ),
    inference(forward_demodulation,[],[f584,f164])).

fof(f584,plain,
    ( k2_relat_1(sK6) = k10_relat_1(sK7,sK5)
    | ~ r1_tarski(k2_relat_1(sK6),k1_relat_1(sK7))
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f583,f91])).

fof(f583,plain,
    ( k2_relat_1(sK6) = k10_relat_1(sK7,sK5)
    | ~ r1_tarski(k2_relat_1(sK6),k1_relat_1(sK7))
    | ~ v1_relat_1(sK7)
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f582,f52])).

fof(f52,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f40])).

fof(f582,plain,
    ( k2_relat_1(sK6) = k10_relat_1(sK7,sK5)
    | ~ r1_tarski(k2_relat_1(sK6),k1_relat_1(sK7))
    | ~ v1_funct_1(sK7)
    | ~ v1_relat_1(sK7)
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f576,f56])).

fof(f56,plain,(
    v2_funct_1(sK7) ),
    inference(cnf_transformation,[],[f40])).

fof(f576,plain,
    ( k2_relat_1(sK6) = k10_relat_1(sK7,sK5)
    | ~ v2_funct_1(sK7)
    | ~ r1_tarski(k2_relat_1(sK6),k1_relat_1(sK7))
    | ~ v1_funct_1(sK7)
    | ~ v1_relat_1(sK7)
    | ~ spl8_8 ),
    inference(superposition,[],[f64,f401])).

fof(f401,plain,
    ( sK5 = k9_relat_1(sK7,k2_relat_1(sK6))
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f400,f90])).

fof(f400,plain,
    ( sK5 = k9_relat_1(sK7,k2_relat_1(sK6))
    | ~ v1_relat_1(sK6)
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f382,f91])).

fof(f382,plain,
    ( sK5 = k9_relat_1(sK7,k2_relat_1(sK6))
    | ~ v1_relat_1(sK7)
    | ~ v1_relat_1(sK6)
    | ~ spl8_8 ),
    inference(superposition,[],[f264,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).

fof(f264,plain,
    ( sK5 = k2_relat_1(k5_relat_1(sK6,sK7))
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f262])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( v2_funct_1(X1)
          & r1_tarski(X0,k1_relat_1(X1)) )
       => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).

fof(f529,plain,
    ( spl8_36
    | ~ spl8_8
    | ~ spl8_35 ),
    inference(avatar_split_clause,[],[f528,f470,f262,f474])).

fof(f470,plain,
    ( spl8_35
  <=> r1_tarski(k2_relat_1(sK7),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_35])])).

fof(f528,plain,
    ( sK5 = k2_relat_1(sK7)
    | ~ spl8_8
    | ~ spl8_35 ),
    inference(subsumption_resolution,[],[f525,f416])).

fof(f416,plain,
    ( r1_tarski(sK5,k2_relat_1(sK7))
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f415,f90])).

fof(f415,plain,
    ( r1_tarski(sK5,k2_relat_1(sK7))
    | ~ v1_relat_1(sK6)
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f386,f91])).

fof(f386,plain,
    ( r1_tarski(sK5,k2_relat_1(sK7))
    | ~ v1_relat_1(sK7)
    | ~ v1_relat_1(sK6)
    | ~ spl8_8 ),
    inference(superposition,[],[f60,f264])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

fof(f525,plain,
    ( sK5 = k2_relat_1(sK7)
    | ~ r1_tarski(sK5,k2_relat_1(sK7))
    | ~ spl8_35 ),
    inference(resolution,[],[f471,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f471,plain,
    ( r1_tarski(k2_relat_1(sK7),sK5)
    | ~ spl8_35 ),
    inference(avatar_component_clause,[],[f470])).

fof(f523,plain,
    ( spl8_7
    | ~ spl8_1 ),
    inference(avatar_split_clause,[],[f522,f121,f258])).

fof(f258,plain,
    ( spl8_7
  <=> m1_subset_1(k5_relat_1(sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(sK3,sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f121,plain,
    ( spl8_1
  <=> m1_subset_1(k1_partfun1(sK3,sK4,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(sK3,sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f522,plain,
    ( m1_subset_1(k5_relat_1(sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(sK3,sK5)))
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f521,f49])).

fof(f49,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f40])).

fof(f521,plain,
    ( m1_subset_1(k5_relat_1(sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(sK3,sK5)))
    | ~ v1_funct_1(sK6)
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f520,f51])).

fof(f520,plain,
    ( m1_subset_1(k5_relat_1(sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(sK3,sK5)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | ~ v1_funct_1(sK6)
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f519,f52])).

fof(f519,plain,
    ( m1_subset_1(k5_relat_1(sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(sK3,sK5)))
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | ~ v1_funct_1(sK6)
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f496,f54])).

fof(f496,plain,
    ( m1_subset_1(k5_relat_1(sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(sK3,sK5)))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | ~ v1_funct_1(sK6)
    | ~ spl8_1 ),
    inference(superposition,[],[f122,f81])).

fof(f81,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f122,plain,
    ( m1_subset_1(k1_partfun1(sK3,sK4,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(sK3,sK5)))
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f121])).

fof(f486,plain,(
    spl8_35 ),
    inference(avatar_contradiction_clause,[],[f485])).

fof(f485,plain,
    ( $false
    | spl8_35 ),
    inference(subsumption_resolution,[],[f484,f91])).

fof(f484,plain,
    ( ~ v1_relat_1(sK7)
    | spl8_35 ),
    inference(subsumption_resolution,[],[f481,f100])).

fof(f100,plain,(
    v5_relat_1(sK7,sK5) ),
    inference(resolution,[],[f72,f54])).

fof(f481,plain,
    ( ~ v5_relat_1(sK7,sK5)
    | ~ v1_relat_1(sK7)
    | spl8_35 ),
    inference(resolution,[],[f472,f62])).

fof(f472,plain,
    ( ~ r1_tarski(k2_relat_1(sK7),sK5)
    | spl8_35 ),
    inference(avatar_component_clause,[],[f470])).

fof(f296,plain,(
    spl8_1 ),
    inference(avatar_contradiction_clause,[],[f295])).

fof(f295,plain,
    ( $false
    | spl8_1 ),
    inference(subsumption_resolution,[],[f294,f49])).

fof(f294,plain,
    ( ~ v1_funct_1(sK6)
    | spl8_1 ),
    inference(subsumption_resolution,[],[f293,f51])).

fof(f293,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | ~ v1_funct_1(sK6)
    | spl8_1 ),
    inference(subsumption_resolution,[],[f292,f52])).

fof(f292,plain,
    ( ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | ~ v1_funct_1(sK6)
    | spl8_1 ),
    inference(subsumption_resolution,[],[f282,f54])).

fof(f282,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | ~ v1_funct_1(sK6)
    | spl8_1 ),
    inference(resolution,[],[f83,f123])).

fof(f123,plain,
    ( ~ m1_subset_1(k1_partfun1(sK3,sK4,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(sK3,sK5)))
    | spl8_1 ),
    inference(avatar_component_clause,[],[f121])).

fof(f83,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
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

fof(f266,plain,
    ( ~ spl8_7
    | spl8_8 ),
    inference(avatar_split_clause,[],[f256,f262,f258])).

fof(f256,plain,
    ( sK5 = k2_relat_1(k5_relat_1(sK6,sK7))
    | ~ m1_subset_1(k5_relat_1(sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(sK3,sK5))) ),
    inference(superposition,[],[f70,f254])).

fof(f254,plain,(
    sK5 = k2_relset_1(sK3,sK5,k5_relat_1(sK6,sK7)) ),
    inference(subsumption_resolution,[],[f253,f49])).

fof(f253,plain,
    ( sK5 = k2_relset_1(sK3,sK5,k5_relat_1(sK6,sK7))
    | ~ v1_funct_1(sK6) ),
    inference(subsumption_resolution,[],[f252,f51])).

fof(f252,plain,
    ( sK5 = k2_relset_1(sK3,sK5,k5_relat_1(sK6,sK7))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | ~ v1_funct_1(sK6) ),
    inference(subsumption_resolution,[],[f251,f52])).

fof(f251,plain,
    ( sK5 = k2_relset_1(sK3,sK5,k5_relat_1(sK6,sK7))
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | ~ v1_funct_1(sK6) ),
    inference(subsumption_resolution,[],[f244,f54])).

fof(f244,plain,
    ( sK5 = k2_relset_1(sK3,sK5,k5_relat_1(sK6,sK7))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | ~ v1_funct_1(sK6) ),
    inference(superposition,[],[f55,f81])).

fof(f55,plain,(
    sK5 = k2_relset_1(sK3,sK5,k1_partfun1(sK3,sK4,sK4,sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f40])).

fof(f169,plain,
    ( spl8_5
    | spl8_6 ),
    inference(avatar_split_clause,[],[f160,f166,f162])).

fof(f160,plain,
    ( sP0(sK4,sK5)
    | sK4 = k1_relat_1(sK7) ),
    inference(subsumption_resolution,[],[f149,f53])).

fof(f53,plain,(
    v1_funct_2(sK7,sK4,sK5) ),
    inference(cnf_transformation,[],[f40])).

fof(f149,plain,
    ( ~ v1_funct_2(sK7,sK4,sK5)
    | sP0(sK4,sK5)
    | sK4 = k1_relat_1(sK7) ),
    inference(resolution,[],[f142,f54])).

fof(f142,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_2(X5,X3,X4)
      | sP0(X3,X4)
      | k1_relat_1(X5) = X3 ) ),
    inference(subsumption_resolution,[],[f140,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP1(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X2,X1,X0)
        & sP1(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f29,f36,f35,f34])).

fof(f35,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | sP0(X0,X1)
      | ~ sP1(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f36,plain,(
    ! [X2,X1,X0] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_xboole_0 = X2 )
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ sP2(X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

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
    inference(flattening,[],[f28])).

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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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

fof(f140,plain,(
    ! [X4,X5,X3] :
      ( k1_relat_1(X5) = X3
      | ~ v1_funct_2(X5,X3,X4)
      | sP0(X3,X4)
      | ~ sP1(X3,X5,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ) ),
    inference(superposition,[],[f75,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X2,X1) = X0
      | ~ v1_funct_2(X1,X0,X2)
      | sP0(X0,X2)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | sP0(X0,X2)
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f46])).

fof(f46,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | sP0(X0,X1)
      | ~ sP1(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:58:23 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (21455)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.51  % (21451)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.51  % (21460)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.51  % (21453)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.51  % (21472)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.51  % (21449)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.52  % (21467)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.52  % (21454)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.52  % (21471)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.52  % (21453)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % (21462)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.52  % (21459)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.52  % (21463)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.52  % (21450)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (21464)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.52  % (21469)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.52  % (21452)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.53  % (21466)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.53  % (21456)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.53  % (21465)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.53  % (21473)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.33/0.54  % (21468)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.33/0.54  % (21458)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.33/0.55  % SZS output start Proof for theBenchmark
% 1.33/0.55  fof(f667,plain,(
% 1.33/0.55    $false),
% 1.33/0.55    inference(avatar_sat_refutation,[],[f169,f266,f296,f486,f523,f529,f594,f600,f610,f666])).
% 1.33/0.55  fof(f666,plain,(
% 1.33/0.55    ~spl8_5 | ~spl8_36 | ~spl8_41),
% 1.33/0.55    inference(avatar_contradiction_clause,[],[f665])).
% 1.33/0.55  fof(f665,plain,(
% 1.33/0.55    $false | (~spl8_5 | ~spl8_36 | ~spl8_41)),
% 1.33/0.55    inference(subsumption_resolution,[],[f664,f129])).
% 1.33/0.55  fof(f129,plain,(
% 1.33/0.55    sK4 != k2_relat_1(sK6)),
% 1.33/0.55    inference(subsumption_resolution,[],[f118,f51])).
% 1.33/0.55  fof(f51,plain,(
% 1.33/0.55    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 1.33/0.55    inference(cnf_transformation,[],[f40])).
% 1.33/0.55  fof(f40,plain,(
% 1.33/0.55    (sK4 != k2_relset_1(sK3,sK4,sK6) & k1_xboole_0 != sK5 & v2_funct_1(sK7) & sK5 = k2_relset_1(sK3,sK5,k1_partfun1(sK3,sK4,sK4,sK5,sK6,sK7)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(sK7,sK4,sK5) & v1_funct_1(sK7)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK6,sK3,sK4) & v1_funct_1(sK6)),
% 1.33/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7])],[f17,f39,f38])).
% 1.33/0.55  fof(f38,plain,(
% 1.33/0.55    ? [X0,X1,X2,X3] : (? [X4] : (k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2 & v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (? [X4] : (sK4 != k2_relset_1(sK3,sK4,sK6) & k1_xboole_0 != sK5 & v2_funct_1(X4) & sK5 = k2_relset_1(sK3,sK5,k1_partfun1(sK3,sK4,sK4,sK5,sK6,X4)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(X4,sK4,sK5) & v1_funct_1(X4)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK6,sK3,sK4) & v1_funct_1(sK6))),
% 1.33/0.55    introduced(choice_axiom,[])).
% 1.33/0.55  fof(f39,plain,(
% 1.33/0.55    ? [X4] : (sK4 != k2_relset_1(sK3,sK4,sK6) & k1_xboole_0 != sK5 & v2_funct_1(X4) & sK5 = k2_relset_1(sK3,sK5,k1_partfun1(sK3,sK4,sK4,sK5,sK6,X4)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(X4,sK4,sK5) & v1_funct_1(X4)) => (sK4 != k2_relset_1(sK3,sK4,sK6) & k1_xboole_0 != sK5 & v2_funct_1(sK7) & sK5 = k2_relset_1(sK3,sK5,k1_partfun1(sK3,sK4,sK4,sK5,sK6,sK7)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(sK7,sK4,sK5) & v1_funct_1(sK7))),
% 1.33/0.55    introduced(choice_axiom,[])).
% 1.33/0.55  fof(f17,plain,(
% 1.33/0.55    ? [X0,X1,X2,X3] : (? [X4] : (k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2 & v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 1.33/0.55    inference(flattening,[],[f16])).
% 1.33/0.55  fof(f16,plain,(
% 1.33/0.55    ? [X0,X1,X2,X3] : (? [X4] : (((k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2) & (v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 1.33/0.55    inference(ennf_transformation,[],[f15])).
% 1.33/0.55  fof(f15,negated_conjecture,(
% 1.33/0.55    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2) => (k2_relset_1(X0,X1,X3) = X1 | k1_xboole_0 = X2))))),
% 1.33/0.55    inference(negated_conjecture,[],[f14])).
% 1.33/0.55  fof(f14,conjecture,(
% 1.33/0.55    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2) => (k2_relset_1(X0,X1,X3) = X1 | k1_xboole_0 = X2))))),
% 1.33/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_funct_2)).
% 1.33/0.55  fof(f118,plain,(
% 1.33/0.55    sK4 != k2_relat_1(sK6) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 1.33/0.55    inference(superposition,[],[f58,f70])).
% 1.33/0.55  fof(f70,plain,(
% 1.33/0.55    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.33/0.55    inference(cnf_transformation,[],[f26])).
% 1.33/0.55  fof(f26,plain,(
% 1.33/0.55    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.33/0.55    inference(ennf_transformation,[],[f10])).
% 1.33/0.55  fof(f10,axiom,(
% 1.33/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.33/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.33/0.55  fof(f58,plain,(
% 1.33/0.55    sK4 != k2_relset_1(sK3,sK4,sK6)),
% 1.33/0.55    inference(cnf_transformation,[],[f40])).
% 1.33/0.55  fof(f664,plain,(
% 1.33/0.55    sK4 = k2_relat_1(sK6) | (~spl8_5 | ~spl8_36 | ~spl8_41)),
% 1.33/0.55    inference(forward_demodulation,[],[f663,f164])).
% 1.33/0.55  fof(f164,plain,(
% 1.33/0.55    sK4 = k1_relat_1(sK7) | ~spl8_5),
% 1.33/0.55    inference(avatar_component_clause,[],[f162])).
% 1.33/0.55  fof(f162,plain,(
% 1.33/0.55    spl8_5 <=> sK4 = k1_relat_1(sK7)),
% 1.33/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 1.33/0.55  fof(f663,plain,(
% 1.33/0.55    k2_relat_1(sK6) = k1_relat_1(sK7) | (~spl8_36 | ~spl8_41)),
% 1.33/0.55    inference(forward_demodulation,[],[f553,f589])).
% 1.33/0.55  fof(f589,plain,(
% 1.33/0.55    k2_relat_1(sK6) = k10_relat_1(sK7,sK5) | ~spl8_41),
% 1.33/0.55    inference(avatar_component_clause,[],[f587])).
% 1.33/0.55  fof(f587,plain,(
% 1.33/0.55    spl8_41 <=> k2_relat_1(sK6) = k10_relat_1(sK7,sK5)),
% 1.33/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_41])])).
% 1.33/0.55  fof(f553,plain,(
% 1.33/0.55    k1_relat_1(sK7) = k10_relat_1(sK7,sK5) | ~spl8_36),
% 1.33/0.55    inference(subsumption_resolution,[],[f536,f91])).
% 1.33/0.55  fof(f91,plain,(
% 1.33/0.55    v1_relat_1(sK7)),
% 1.33/0.55    inference(resolution,[],[f68,f54])).
% 1.33/0.55  fof(f54,plain,(
% 1.33/0.55    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))),
% 1.33/0.55    inference(cnf_transformation,[],[f40])).
% 1.33/0.55  fof(f68,plain,(
% 1.33/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.33/0.55    inference(cnf_transformation,[],[f24])).
% 1.33/0.55  fof(f24,plain,(
% 1.33/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.33/0.55    inference(ennf_transformation,[],[f7])).
% 1.33/0.55  fof(f7,axiom,(
% 1.33/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.33/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.33/0.55  fof(f536,plain,(
% 1.33/0.55    k1_relat_1(sK7) = k10_relat_1(sK7,sK5) | ~v1_relat_1(sK7) | ~spl8_36),
% 1.33/0.55    inference(superposition,[],[f59,f476])).
% 1.33/0.55  fof(f476,plain,(
% 1.33/0.55    sK5 = k2_relat_1(sK7) | ~spl8_36),
% 1.33/0.55    inference(avatar_component_clause,[],[f474])).
% 1.33/0.55  fof(f474,plain,(
% 1.33/0.55    spl8_36 <=> sK5 = k2_relat_1(sK7)),
% 1.33/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_36])])).
% 1.33/0.55  fof(f59,plain,(
% 1.33/0.55    ( ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 1.33/0.55    inference(cnf_transformation,[],[f18])).
% 1.33/0.55  fof(f18,plain,(
% 1.33/0.55    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 1.33/0.55    inference(ennf_transformation,[],[f4])).
% 1.33/0.55  fof(f4,axiom,(
% 1.33/0.55    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 1.33/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).
% 1.33/0.55  fof(f610,plain,(
% 1.33/0.55    ~spl8_6),
% 1.33/0.55    inference(avatar_contradiction_clause,[],[f609])).
% 1.33/0.55  fof(f609,plain,(
% 1.33/0.55    $false | ~spl8_6),
% 1.33/0.55    inference(subsumption_resolution,[],[f608,f57])).
% 1.33/0.55  fof(f57,plain,(
% 1.33/0.55    k1_xboole_0 != sK5),
% 1.33/0.55    inference(cnf_transformation,[],[f40])).
% 1.33/0.55  fof(f608,plain,(
% 1.33/0.55    k1_xboole_0 = sK5 | ~spl8_6),
% 1.33/0.55    inference(resolution,[],[f168,f77])).
% 1.33/0.55  fof(f77,plain,(
% 1.33/0.55    ( ! [X0,X1] : (~sP0(X0,X1) | k1_xboole_0 = X1) )),
% 1.33/0.55    inference(cnf_transformation,[],[f48])).
% 1.33/0.55  fof(f48,plain,(
% 1.33/0.55    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X1))),
% 1.33/0.55    inference(nnf_transformation,[],[f34])).
% 1.33/0.55  fof(f34,plain,(
% 1.33/0.55    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X1))),
% 1.33/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.33/0.55  fof(f168,plain,(
% 1.33/0.55    sP0(sK4,sK5) | ~spl8_6),
% 1.33/0.55    inference(avatar_component_clause,[],[f166])).
% 1.33/0.55  fof(f166,plain,(
% 1.33/0.55    spl8_6 <=> sP0(sK4,sK5)),
% 1.33/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 1.33/0.55  fof(f600,plain,(
% 1.33/0.55    spl8_42),
% 1.33/0.55    inference(avatar_contradiction_clause,[],[f599])).
% 1.33/0.55  fof(f599,plain,(
% 1.33/0.55    $false | spl8_42),
% 1.33/0.55    inference(subsumption_resolution,[],[f598,f90])).
% 1.33/0.55  fof(f90,plain,(
% 1.33/0.55    v1_relat_1(sK6)),
% 1.33/0.55    inference(resolution,[],[f68,f51])).
% 1.33/0.55  fof(f598,plain,(
% 1.33/0.55    ~v1_relat_1(sK6) | spl8_42),
% 1.33/0.55    inference(subsumption_resolution,[],[f595,f99])).
% 1.33/0.55  fof(f99,plain,(
% 1.33/0.55    v5_relat_1(sK6,sK4)),
% 1.33/0.55    inference(resolution,[],[f72,f51])).
% 1.33/0.55  fof(f72,plain,(
% 1.33/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.33/0.55    inference(cnf_transformation,[],[f27])).
% 1.33/0.55  fof(f27,plain,(
% 1.33/0.55    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.33/0.55    inference(ennf_transformation,[],[f8])).
% 1.33/0.55  fof(f8,axiom,(
% 1.33/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.33/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.33/0.55  fof(f595,plain,(
% 1.33/0.55    ~v5_relat_1(sK6,sK4) | ~v1_relat_1(sK6) | spl8_42),
% 1.33/0.55    inference(resolution,[],[f593,f62])).
% 1.33/0.55  fof(f62,plain,(
% 1.33/0.55    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.33/0.55    inference(cnf_transformation,[],[f41])).
% 1.33/0.55  fof(f41,plain,(
% 1.33/0.55    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.33/0.55    inference(nnf_transformation,[],[f21])).
% 1.33/0.55  fof(f21,plain,(
% 1.33/0.55    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.33/0.55    inference(ennf_transformation,[],[f2])).
% 1.33/0.55  fof(f2,axiom,(
% 1.33/0.55    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.33/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 1.33/0.55  fof(f593,plain,(
% 1.33/0.55    ~r1_tarski(k2_relat_1(sK6),sK4) | spl8_42),
% 1.33/0.55    inference(avatar_component_clause,[],[f591])).
% 1.33/0.55  fof(f591,plain,(
% 1.33/0.55    spl8_42 <=> r1_tarski(k2_relat_1(sK6),sK4)),
% 1.33/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_42])])).
% 1.33/0.55  fof(f594,plain,(
% 1.33/0.55    spl8_41 | ~spl8_42 | ~spl8_5 | ~spl8_8),
% 1.33/0.55    inference(avatar_split_clause,[],[f585,f262,f162,f591,f587])).
% 1.33/0.55  fof(f262,plain,(
% 1.33/0.55    spl8_8 <=> sK5 = k2_relat_1(k5_relat_1(sK6,sK7))),
% 1.33/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 1.33/0.55  fof(f585,plain,(
% 1.33/0.55    ~r1_tarski(k2_relat_1(sK6),sK4) | k2_relat_1(sK6) = k10_relat_1(sK7,sK5) | (~spl8_5 | ~spl8_8)),
% 1.33/0.55    inference(forward_demodulation,[],[f584,f164])).
% 1.33/0.55  fof(f584,plain,(
% 1.33/0.55    k2_relat_1(sK6) = k10_relat_1(sK7,sK5) | ~r1_tarski(k2_relat_1(sK6),k1_relat_1(sK7)) | ~spl8_8),
% 1.33/0.55    inference(subsumption_resolution,[],[f583,f91])).
% 1.33/0.55  fof(f583,plain,(
% 1.33/0.55    k2_relat_1(sK6) = k10_relat_1(sK7,sK5) | ~r1_tarski(k2_relat_1(sK6),k1_relat_1(sK7)) | ~v1_relat_1(sK7) | ~spl8_8),
% 1.33/0.55    inference(subsumption_resolution,[],[f582,f52])).
% 1.33/0.55  fof(f52,plain,(
% 1.33/0.55    v1_funct_1(sK7)),
% 1.33/0.55    inference(cnf_transformation,[],[f40])).
% 1.33/0.55  fof(f582,plain,(
% 1.33/0.55    k2_relat_1(sK6) = k10_relat_1(sK7,sK5) | ~r1_tarski(k2_relat_1(sK6),k1_relat_1(sK7)) | ~v1_funct_1(sK7) | ~v1_relat_1(sK7) | ~spl8_8),
% 1.33/0.55    inference(subsumption_resolution,[],[f576,f56])).
% 1.33/0.55  fof(f56,plain,(
% 1.33/0.55    v2_funct_1(sK7)),
% 1.33/0.55    inference(cnf_transformation,[],[f40])).
% 1.33/0.55  fof(f576,plain,(
% 1.33/0.55    k2_relat_1(sK6) = k10_relat_1(sK7,sK5) | ~v2_funct_1(sK7) | ~r1_tarski(k2_relat_1(sK6),k1_relat_1(sK7)) | ~v1_funct_1(sK7) | ~v1_relat_1(sK7) | ~spl8_8),
% 1.33/0.55    inference(superposition,[],[f64,f401])).
% 1.33/0.55  fof(f401,plain,(
% 1.33/0.55    sK5 = k9_relat_1(sK7,k2_relat_1(sK6)) | ~spl8_8),
% 1.33/0.55    inference(subsumption_resolution,[],[f400,f90])).
% 1.33/0.55  fof(f400,plain,(
% 1.33/0.55    sK5 = k9_relat_1(sK7,k2_relat_1(sK6)) | ~v1_relat_1(sK6) | ~spl8_8),
% 1.33/0.55    inference(subsumption_resolution,[],[f382,f91])).
% 1.33/0.55  fof(f382,plain,(
% 1.33/0.55    sK5 = k9_relat_1(sK7,k2_relat_1(sK6)) | ~v1_relat_1(sK7) | ~v1_relat_1(sK6) | ~spl8_8),
% 1.33/0.55    inference(superposition,[],[f264,f61])).
% 1.33/0.55  fof(f61,plain,(
% 1.33/0.55    ( ! [X0,X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.33/0.55    inference(cnf_transformation,[],[f20])).
% 1.33/0.55  fof(f20,plain,(
% 1.33/0.55    ! [X0] : (! [X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.33/0.55    inference(ennf_transformation,[],[f3])).
% 1.33/0.55  fof(f3,axiom,(
% 1.33/0.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 1.33/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).
% 1.33/0.55  fof(f264,plain,(
% 1.33/0.55    sK5 = k2_relat_1(k5_relat_1(sK6,sK7)) | ~spl8_8),
% 1.33/0.55    inference(avatar_component_clause,[],[f262])).
% 1.33/0.55  fof(f64,plain,(
% 1.33/0.55    ( ! [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.33/0.55    inference(cnf_transformation,[],[f23])).
% 1.33/0.55  fof(f23,plain,(
% 1.33/0.55    ! [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.33/0.55    inference(flattening,[],[f22])).
% 1.33/0.55  fof(f22,plain,(
% 1.33/0.55    ! [X0,X1] : ((k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | (~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.33/0.55    inference(ennf_transformation,[],[f6])).
% 1.33/0.55  fof(f6,axiom,(
% 1.33/0.55    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 1.33/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).
% 1.33/0.55  fof(f529,plain,(
% 1.33/0.55    spl8_36 | ~spl8_8 | ~spl8_35),
% 1.33/0.55    inference(avatar_split_clause,[],[f528,f470,f262,f474])).
% 1.33/0.55  fof(f470,plain,(
% 1.33/0.55    spl8_35 <=> r1_tarski(k2_relat_1(sK7),sK5)),
% 1.33/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_35])])).
% 1.33/0.55  fof(f528,plain,(
% 1.33/0.55    sK5 = k2_relat_1(sK7) | (~spl8_8 | ~spl8_35)),
% 1.33/0.55    inference(subsumption_resolution,[],[f525,f416])).
% 1.33/0.55  fof(f416,plain,(
% 1.33/0.55    r1_tarski(sK5,k2_relat_1(sK7)) | ~spl8_8),
% 1.33/0.55    inference(subsumption_resolution,[],[f415,f90])).
% 1.33/0.55  fof(f415,plain,(
% 1.33/0.55    r1_tarski(sK5,k2_relat_1(sK7)) | ~v1_relat_1(sK6) | ~spl8_8),
% 1.33/0.55    inference(subsumption_resolution,[],[f386,f91])).
% 1.33/0.55  fof(f386,plain,(
% 1.33/0.55    r1_tarski(sK5,k2_relat_1(sK7)) | ~v1_relat_1(sK7) | ~v1_relat_1(sK6) | ~spl8_8),
% 1.33/0.55    inference(superposition,[],[f60,f264])).
% 1.33/0.55  fof(f60,plain,(
% 1.33/0.55    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.33/0.55    inference(cnf_transformation,[],[f19])).
% 1.33/0.55  fof(f19,plain,(
% 1.33/0.55    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.33/0.55    inference(ennf_transformation,[],[f5])).
% 1.33/0.55  fof(f5,axiom,(
% 1.33/0.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 1.33/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).
% 1.33/0.55  fof(f525,plain,(
% 1.33/0.55    sK5 = k2_relat_1(sK7) | ~r1_tarski(sK5,k2_relat_1(sK7)) | ~spl8_35),
% 1.33/0.55    inference(resolution,[],[f471,f67])).
% 1.33/0.55  fof(f67,plain,(
% 1.33/0.55    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.33/0.55    inference(cnf_transformation,[],[f43])).
% 1.33/0.55  fof(f43,plain,(
% 1.33/0.55    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.33/0.55    inference(flattening,[],[f42])).
% 1.33/0.55  fof(f42,plain,(
% 1.33/0.55    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.33/0.55    inference(nnf_transformation,[],[f1])).
% 1.33/0.55  fof(f1,axiom,(
% 1.33/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.33/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.33/0.55  fof(f471,plain,(
% 1.33/0.55    r1_tarski(k2_relat_1(sK7),sK5) | ~spl8_35),
% 1.33/0.55    inference(avatar_component_clause,[],[f470])).
% 1.33/0.55  fof(f523,plain,(
% 1.33/0.55    spl8_7 | ~spl8_1),
% 1.33/0.55    inference(avatar_split_clause,[],[f522,f121,f258])).
% 1.33/0.55  fof(f258,plain,(
% 1.33/0.55    spl8_7 <=> m1_subset_1(k5_relat_1(sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(sK3,sK5)))),
% 1.33/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 1.33/0.55  fof(f121,plain,(
% 1.33/0.55    spl8_1 <=> m1_subset_1(k1_partfun1(sK3,sK4,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(sK3,sK5)))),
% 1.33/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 1.33/0.55  fof(f522,plain,(
% 1.33/0.55    m1_subset_1(k5_relat_1(sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(sK3,sK5))) | ~spl8_1),
% 1.33/0.55    inference(subsumption_resolution,[],[f521,f49])).
% 1.33/0.55  fof(f49,plain,(
% 1.33/0.55    v1_funct_1(sK6)),
% 1.33/0.55    inference(cnf_transformation,[],[f40])).
% 1.33/0.55  fof(f521,plain,(
% 1.33/0.55    m1_subset_1(k5_relat_1(sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(sK3,sK5))) | ~v1_funct_1(sK6) | ~spl8_1),
% 1.33/0.55    inference(subsumption_resolution,[],[f520,f51])).
% 1.33/0.55  fof(f520,plain,(
% 1.33/0.55    m1_subset_1(k5_relat_1(sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(sK3,sK5))) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) | ~v1_funct_1(sK6) | ~spl8_1),
% 1.33/0.55    inference(subsumption_resolution,[],[f519,f52])).
% 1.33/0.55  fof(f519,plain,(
% 1.33/0.55    m1_subset_1(k5_relat_1(sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(sK3,sK5))) | ~v1_funct_1(sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) | ~v1_funct_1(sK6) | ~spl8_1),
% 1.33/0.55    inference(subsumption_resolution,[],[f496,f54])).
% 1.33/0.55  fof(f496,plain,(
% 1.33/0.55    m1_subset_1(k5_relat_1(sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(sK3,sK5))) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) | ~v1_funct_1(sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) | ~v1_funct_1(sK6) | ~spl8_1),
% 1.33/0.55    inference(superposition,[],[f122,f81])).
% 1.33/0.55  fof(f81,plain,(
% 1.33/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.33/0.55    inference(cnf_transformation,[],[f31])).
% 1.33/0.55  fof(f31,plain,(
% 1.33/0.55    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.33/0.55    inference(flattening,[],[f30])).
% 1.33/0.55  fof(f30,plain,(
% 1.33/0.55    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.33/0.55    inference(ennf_transformation,[],[f13])).
% 1.33/0.55  fof(f13,axiom,(
% 1.33/0.55    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.33/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 1.33/0.55  fof(f122,plain,(
% 1.33/0.55    m1_subset_1(k1_partfun1(sK3,sK4,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(sK3,sK5))) | ~spl8_1),
% 1.33/0.55    inference(avatar_component_clause,[],[f121])).
% 1.33/0.55  fof(f486,plain,(
% 1.33/0.55    spl8_35),
% 1.33/0.55    inference(avatar_contradiction_clause,[],[f485])).
% 1.33/0.55  fof(f485,plain,(
% 1.33/0.55    $false | spl8_35),
% 1.33/0.55    inference(subsumption_resolution,[],[f484,f91])).
% 1.33/0.55  fof(f484,plain,(
% 1.33/0.55    ~v1_relat_1(sK7) | spl8_35),
% 1.33/0.55    inference(subsumption_resolution,[],[f481,f100])).
% 1.33/0.55  fof(f100,plain,(
% 1.33/0.55    v5_relat_1(sK7,sK5)),
% 1.33/0.55    inference(resolution,[],[f72,f54])).
% 1.33/0.55  fof(f481,plain,(
% 1.33/0.55    ~v5_relat_1(sK7,sK5) | ~v1_relat_1(sK7) | spl8_35),
% 1.33/0.55    inference(resolution,[],[f472,f62])).
% 1.33/0.55  fof(f472,plain,(
% 1.33/0.55    ~r1_tarski(k2_relat_1(sK7),sK5) | spl8_35),
% 1.33/0.55    inference(avatar_component_clause,[],[f470])).
% 1.33/0.55  fof(f296,plain,(
% 1.33/0.55    spl8_1),
% 1.33/0.55    inference(avatar_contradiction_clause,[],[f295])).
% 1.33/0.55  fof(f295,plain,(
% 1.33/0.55    $false | spl8_1),
% 1.33/0.55    inference(subsumption_resolution,[],[f294,f49])).
% 1.33/0.55  fof(f294,plain,(
% 1.33/0.55    ~v1_funct_1(sK6) | spl8_1),
% 1.33/0.55    inference(subsumption_resolution,[],[f293,f51])).
% 1.33/0.55  fof(f293,plain,(
% 1.33/0.55    ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) | ~v1_funct_1(sK6) | spl8_1),
% 1.33/0.55    inference(subsumption_resolution,[],[f292,f52])).
% 1.33/0.55  fof(f292,plain,(
% 1.33/0.55    ~v1_funct_1(sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) | ~v1_funct_1(sK6) | spl8_1),
% 1.33/0.55    inference(subsumption_resolution,[],[f282,f54])).
% 1.33/0.55  fof(f282,plain,(
% 1.33/0.55    ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) | ~v1_funct_1(sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) | ~v1_funct_1(sK6) | spl8_1),
% 1.33/0.55    inference(resolution,[],[f83,f123])).
% 1.33/0.55  fof(f123,plain,(
% 1.33/0.55    ~m1_subset_1(k1_partfun1(sK3,sK4,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(sK3,sK5))) | spl8_1),
% 1.33/0.55    inference(avatar_component_clause,[],[f121])).
% 1.33/0.55  fof(f83,plain,(
% 1.33/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.33/0.55    inference(cnf_transformation,[],[f33])).
% 1.33/0.55  fof(f33,plain,(
% 1.33/0.55    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.33/0.55    inference(flattening,[],[f32])).
% 1.33/0.55  fof(f32,plain,(
% 1.33/0.55    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.33/0.55    inference(ennf_transformation,[],[f12])).
% 1.33/0.55  fof(f12,axiom,(
% 1.33/0.55    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 1.33/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 1.33/0.55  fof(f266,plain,(
% 1.33/0.55    ~spl8_7 | spl8_8),
% 1.33/0.55    inference(avatar_split_clause,[],[f256,f262,f258])).
% 1.33/0.55  fof(f256,plain,(
% 1.33/0.55    sK5 = k2_relat_1(k5_relat_1(sK6,sK7)) | ~m1_subset_1(k5_relat_1(sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(sK3,sK5)))),
% 1.33/0.55    inference(superposition,[],[f70,f254])).
% 1.33/0.55  fof(f254,plain,(
% 1.33/0.55    sK5 = k2_relset_1(sK3,sK5,k5_relat_1(sK6,sK7))),
% 1.33/0.55    inference(subsumption_resolution,[],[f253,f49])).
% 1.33/0.55  fof(f253,plain,(
% 1.33/0.55    sK5 = k2_relset_1(sK3,sK5,k5_relat_1(sK6,sK7)) | ~v1_funct_1(sK6)),
% 1.33/0.55    inference(subsumption_resolution,[],[f252,f51])).
% 1.33/0.55  fof(f252,plain,(
% 1.33/0.55    sK5 = k2_relset_1(sK3,sK5,k5_relat_1(sK6,sK7)) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) | ~v1_funct_1(sK6)),
% 1.33/0.55    inference(subsumption_resolution,[],[f251,f52])).
% 1.33/0.55  fof(f251,plain,(
% 1.33/0.55    sK5 = k2_relset_1(sK3,sK5,k5_relat_1(sK6,sK7)) | ~v1_funct_1(sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) | ~v1_funct_1(sK6)),
% 1.33/0.55    inference(subsumption_resolution,[],[f244,f54])).
% 1.33/0.55  fof(f244,plain,(
% 1.33/0.55    sK5 = k2_relset_1(sK3,sK5,k5_relat_1(sK6,sK7)) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) | ~v1_funct_1(sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) | ~v1_funct_1(sK6)),
% 1.33/0.55    inference(superposition,[],[f55,f81])).
% 1.33/0.55  fof(f55,plain,(
% 1.33/0.55    sK5 = k2_relset_1(sK3,sK5,k1_partfun1(sK3,sK4,sK4,sK5,sK6,sK7))),
% 1.33/0.55    inference(cnf_transformation,[],[f40])).
% 1.33/0.55  fof(f169,plain,(
% 1.33/0.55    spl8_5 | spl8_6),
% 1.33/0.55    inference(avatar_split_clause,[],[f160,f166,f162])).
% 1.33/0.55  fof(f160,plain,(
% 1.33/0.55    sP0(sK4,sK5) | sK4 = k1_relat_1(sK7)),
% 1.33/0.55    inference(subsumption_resolution,[],[f149,f53])).
% 1.33/0.55  fof(f53,plain,(
% 1.33/0.55    v1_funct_2(sK7,sK4,sK5)),
% 1.33/0.55    inference(cnf_transformation,[],[f40])).
% 1.33/0.55  fof(f149,plain,(
% 1.33/0.55    ~v1_funct_2(sK7,sK4,sK5) | sP0(sK4,sK5) | sK4 = k1_relat_1(sK7)),
% 1.33/0.55    inference(resolution,[],[f142,f54])).
% 1.33/0.55  fof(f142,plain,(
% 1.33/0.55    ( ! [X4,X5,X3] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_2(X5,X3,X4) | sP0(X3,X4) | k1_relat_1(X5) = X3) )),
% 1.33/0.55    inference(subsumption_resolution,[],[f140,f79])).
% 1.33/0.55  fof(f79,plain,(
% 1.33/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP1(X0,X2,X1)) )),
% 1.33/0.55    inference(cnf_transformation,[],[f37])).
% 1.33/0.55  fof(f37,plain,(
% 1.33/0.55    ! [X0,X1,X2] : ((sP2(X2,X1,X0) & sP1(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.33/0.55    inference(definition_folding,[],[f29,f36,f35,f34])).
% 1.33/0.55  fof(f35,plain,(
% 1.33/0.55    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | sP0(X0,X1) | ~sP1(X0,X2,X1))),
% 1.33/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.33/0.55  fof(f36,plain,(
% 1.33/0.55    ! [X2,X1,X0] : ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~sP2(X2,X1,X0))),
% 1.33/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 1.33/0.55  fof(f29,plain,(
% 1.33/0.55    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.33/0.55    inference(flattening,[],[f28])).
% 1.33/0.55  fof(f28,plain,(
% 1.33/0.55    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.33/0.55    inference(ennf_transformation,[],[f11])).
% 1.33/0.55  fof(f11,axiom,(
% 1.33/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.33/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.33/0.55  fof(f140,plain,(
% 1.33/0.55    ( ! [X4,X5,X3] : (k1_relat_1(X5) = X3 | ~v1_funct_2(X5,X3,X4) | sP0(X3,X4) | ~sP1(X3,X5,X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) )),
% 1.33/0.55    inference(superposition,[],[f75,f69])).
% 1.33/0.55  fof(f69,plain,(
% 1.33/0.55    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.33/0.55    inference(cnf_transformation,[],[f25])).
% 1.33/0.55  fof(f25,plain,(
% 1.33/0.55    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.33/0.55    inference(ennf_transformation,[],[f9])).
% 1.33/0.55  fof(f9,axiom,(
% 1.33/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.33/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.33/0.55  fof(f75,plain,(
% 1.33/0.55    ( ! [X2,X0,X1] : (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2) | sP0(X0,X2) | ~sP1(X0,X1,X2)) )),
% 1.33/0.55    inference(cnf_transformation,[],[f47])).
% 1.33/0.55  fof(f47,plain,(
% 1.33/0.55    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | sP0(X0,X2) | ~sP1(X0,X1,X2))),
% 1.33/0.55    inference(rectify,[],[f46])).
% 1.33/0.55  fof(f46,plain,(
% 1.33/0.55    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | sP0(X0,X1) | ~sP1(X0,X2,X1))),
% 1.33/0.55    inference(nnf_transformation,[],[f35])).
% 1.33/0.55  % SZS output end Proof for theBenchmark
% 1.33/0.55  % (21453)------------------------------
% 1.33/0.55  % (21453)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.55  % (21453)Termination reason: Refutation
% 1.33/0.55  
% 1.33/0.55  % (21453)Memory used [KB]: 6524
% 1.33/0.55  % (21453)Time elapsed: 0.104 s
% 1.33/0.55  % (21453)------------------------------
% 1.33/0.55  % (21453)------------------------------
% 1.33/0.55  % (21448)Success in time 0.185 s
%------------------------------------------------------------------------------
