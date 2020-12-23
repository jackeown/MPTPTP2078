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
% DateTime   : Thu Dec  3 13:01:30 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 338 expanded)
%              Number of leaves         :   25 ( 110 expanded)
%              Depth                    :   14
%              Number of atoms          :  463 (2277 expanded)
%              Number of equality atoms :  119 ( 685 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f677,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f321,f560,f581,f600,f606,f607,f610,f676])).

fof(f676,plain,(
    ~ spl8_19 ),
    inference(avatar_contradiction_clause,[],[f674])).

fof(f674,plain,
    ( $false
    | ~ spl8_19 ),
    inference(subsumption_resolution,[],[f52,f559])).

fof(f559,plain,
    ( ! [X0] : ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,sK5)))
    | ~ spl8_19 ),
    inference(avatar_component_clause,[],[f558])).

fof(f558,plain,
    ( spl8_19
  <=> ! [X0] : ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).

fof(f52,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7])],[f16,f37,f36])).

fof(f36,plain,
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

fof(f37,plain,
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
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
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_funct_2)).

fof(f610,plain,(
    ~ spl8_17 ),
    inference(avatar_contradiction_clause,[],[f609])).

fof(f609,plain,
    ( $false
    | ~ spl8_17 ),
    inference(subsumption_resolution,[],[f608,f55])).

fof(f55,plain,(
    k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f38])).

fof(f608,plain,
    ( k1_xboole_0 = sK5
    | ~ spl8_17 ),
    inference(resolution,[],[f411,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X1) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f411,plain,
    ( sP0(sK4,sK5)
    | ~ spl8_17 ),
    inference(avatar_component_clause,[],[f409])).

fof(f409,plain,
    ( spl8_17
  <=> sP0(sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

fof(f607,plain,
    ( spl8_8
    | ~ spl8_12 ),
    inference(avatar_split_clause,[],[f572,f312,f164])).

fof(f164,plain,
    ( spl8_8
  <=> sK5 = k2_relat_1(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f312,plain,
    ( spl8_12
  <=> sK5 = k2_relat_1(k5_relat_1(sK6,sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f572,plain,
    ( sK5 = k2_relat_1(sK7)
    | ~ spl8_12 ),
    inference(subsumption_resolution,[],[f571,f89])).

fof(f89,plain,(
    v1_relat_1(sK7) ),
    inference(resolution,[],[f64,f52])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f571,plain,
    ( sK5 = k2_relat_1(sK7)
    | ~ v1_relat_1(sK7)
    | ~ spl8_12 ),
    inference(subsumption_resolution,[],[f570,f88])).

fof(f88,plain,(
    v1_relat_1(sK6) ),
    inference(resolution,[],[f64,f49])).

fof(f49,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f38])).

fof(f570,plain,
    ( ~ v1_relat_1(sK6)
    | sK5 = k2_relat_1(sK7)
    | ~ v1_relat_1(sK7)
    | ~ spl8_12 ),
    inference(subsumption_resolution,[],[f563,f157])).

fof(f157,plain,(
    r1_tarski(k2_relat_1(sK7),sK5) ),
    inference(resolution,[],[f151,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f151,plain,(
    m1_subset_1(k2_relat_1(sK7),k1_zfmisc_1(sK5)) ),
    inference(resolution,[],[f149,f52])).

fof(f149,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k2_relat_1(X2),k1_zfmisc_1(X1)) ) ),
    inference(duplicate_literal_removal,[],[f148])).

fof(f148,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relat_1(X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f67,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(f563,plain,
    ( ~ r1_tarski(k2_relat_1(sK7),sK5)
    | ~ v1_relat_1(sK6)
    | sK5 = k2_relat_1(sK7)
    | ~ v1_relat_1(sK7)
    | ~ spl8_12 ),
    inference(superposition,[],[f127,f314])).

fof(f314,plain,
    ( sK5 = k2_relat_1(k5_relat_1(sK6,sK7))
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f312])).

fof(f127,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X0),k2_relat_1(k5_relat_1(X1,X0)))
      | ~ v1_relat_1(X1)
      | k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f57,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
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

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

fof(f606,plain,
    ( spl8_16
    | spl8_17 ),
    inference(avatar_split_clause,[],[f605,f409,f405])).

fof(f405,plain,
    ( spl8_16
  <=> sK4 = k1_relat_1(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f605,plain,
    ( sP0(sK4,sK5)
    | sK4 = k1_relat_1(sK7) ),
    inference(subsumption_resolution,[],[f422,f51])).

fof(f51,plain,(
    v1_funct_2(sK7,sK4,sK5) ),
    inference(cnf_transformation,[],[f38])).

fof(f422,plain,
    ( sP0(sK4,sK5)
    | sK4 = k1_relat_1(sK7)
    | ~ v1_funct_2(sK7,sK4,sK5) ),
    inference(resolution,[],[f388,f86])).

fof(f86,plain,(
    r1_tarski(sK7,k2_zfmisc_1(sK4,sK5)) ),
    inference(resolution,[],[f62,f52])).

fof(f388,plain,(
    ! [X6,X8,X7] :
      ( ~ r1_tarski(X6,k2_zfmisc_1(X7,X8))
      | sP0(X7,X8)
      | k1_relat_1(X6) = X7
      | ~ v1_funct_2(X6,X7,X8) ) ),
    inference(resolution,[],[f189,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f189,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_2(X5,X3,X4)
      | sP0(X3,X4)
      | k1_relat_1(X5) = X3 ) ),
    inference(subsumption_resolution,[],[f187,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP1(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X2,X1,X0)
        & sP1(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f25,f34,f33,f32])).

fof(f33,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | sP0(X0,X1)
      | ~ sP1(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f34,plain,(
    ! [X2,X1,X0] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_xboole_0 = X2 )
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ sP2(X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f187,plain,(
    ! [X4,X5,X3] :
      ( k1_relat_1(X5) = X3
      | ~ v1_funct_2(X5,X3,X4)
      | sP0(X3,X4)
      | ~ sP1(X3,X5,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ) ),
    inference(superposition,[],[f70,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X2,X1) = X0
      | ~ v1_funct_2(X1,X0,X2)
      | sP0(X0,X2)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | sP0(X0,X2)
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f44])).

fof(f44,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | sP0(X0,X1)
      | ~ sP1(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f600,plain,(
    ~ spl8_18 ),
    inference(avatar_contradiction_clause,[],[f598])).

fof(f598,plain,
    ( $false
    | ~ spl8_18 ),
    inference(subsumption_resolution,[],[f49,f556])).

fof(f556,plain,
    ( ! [X1] : ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,X1)))
    | ~ spl8_18 ),
    inference(avatar_component_clause,[],[f555])).

fof(f555,plain,
    ( spl8_18
  <=> ! [X1] : ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f581,plain,
    ( ~ spl8_8
    | ~ spl8_12
    | ~ spl8_16 ),
    inference(avatar_split_clause,[],[f580,f405,f312,f164])).

fof(f580,plain,
    ( sK5 != k2_relat_1(sK7)
    | ~ spl8_12
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f579,f156])).

fof(f156,plain,(
    ~ r1_tarski(sK4,k2_relat_1(sK6)) ),
    inference(subsumption_resolution,[],[f155,f140])).

fof(f140,plain,(
    sK4 != k2_relat_1(sK6) ),
    inference(subsumption_resolution,[],[f129,f49])).

fof(f129,plain,
    ( sK4 != k2_relat_1(sK6)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(superposition,[],[f56,f66])).

fof(f56,plain,(
    sK4 != k2_relset_1(sK3,sK4,sK6) ),
    inference(cnf_transformation,[],[f38])).

fof(f155,plain,
    ( sK4 = k2_relat_1(sK6)
    | ~ r1_tarski(sK4,k2_relat_1(sK6)) ),
    inference(resolution,[],[f154,f61])).

fof(f154,plain,(
    r1_tarski(k2_relat_1(sK6),sK4) ),
    inference(resolution,[],[f150,f62])).

fof(f150,plain,(
    m1_subset_1(k2_relat_1(sK6),k1_zfmisc_1(sK4)) ),
    inference(resolution,[],[f149,f49])).

fof(f579,plain,
    ( r1_tarski(sK4,k2_relat_1(sK6))
    | sK5 != k2_relat_1(sK7)
    | ~ spl8_12
    | ~ spl8_16 ),
    inference(forward_demodulation,[],[f578,f407])).

fof(f407,plain,
    ( sK4 = k1_relat_1(sK7)
    | ~ spl8_16 ),
    inference(avatar_component_clause,[],[f405])).

fof(f578,plain,
    ( sK5 != k2_relat_1(sK7)
    | r1_tarski(k1_relat_1(sK7),k2_relat_1(sK6))
    | ~ spl8_12 ),
    inference(subsumption_resolution,[],[f577,f89])).

fof(f577,plain,
    ( sK5 != k2_relat_1(sK7)
    | r1_tarski(k1_relat_1(sK7),k2_relat_1(sK6))
    | ~ v1_relat_1(sK7)
    | ~ spl8_12 ),
    inference(subsumption_resolution,[],[f576,f50])).

fof(f50,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f38])).

fof(f576,plain,
    ( sK5 != k2_relat_1(sK7)
    | r1_tarski(k1_relat_1(sK7),k2_relat_1(sK6))
    | ~ v1_funct_1(sK7)
    | ~ v1_relat_1(sK7)
    | ~ spl8_12 ),
    inference(subsumption_resolution,[],[f575,f88])).

fof(f575,plain,
    ( sK5 != k2_relat_1(sK7)
    | r1_tarski(k1_relat_1(sK7),k2_relat_1(sK6))
    | ~ v1_relat_1(sK6)
    | ~ v1_funct_1(sK7)
    | ~ v1_relat_1(sK7)
    | ~ spl8_12 ),
    inference(subsumption_resolution,[],[f574,f47])).

fof(f47,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f38])).

fof(f574,plain,
    ( sK5 != k2_relat_1(sK7)
    | r1_tarski(k1_relat_1(sK7),k2_relat_1(sK6))
    | ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6)
    | ~ v1_funct_1(sK7)
    | ~ v1_relat_1(sK7)
    | ~ spl8_12 ),
    inference(subsumption_resolution,[],[f564,f54])).

fof(f54,plain,(
    v2_funct_1(sK7) ),
    inference(cnf_transformation,[],[f38])).

fof(f564,plain,
    ( sK5 != k2_relat_1(sK7)
    | ~ v2_funct_1(sK7)
    | r1_tarski(k1_relat_1(sK7),k2_relat_1(sK6))
    | ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6)
    | ~ v1_funct_1(sK7)
    | ~ v1_relat_1(sK7)
    | ~ spl8_12 ),
    inference(superposition,[],[f58,f314])).

% (24872)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
fof(f58,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k5_relat_1(X1,X0)) != k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v2_funct_1(X0)
          | k2_relat_1(k5_relat_1(X1,X0)) != k2_relat_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v2_funct_1(X0)
          | k2_relat_1(k5_relat_1(X1,X0)) != k2_relat_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( v2_funct_1(X0)
              & k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0) )
           => r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_funct_1)).

fof(f560,plain,
    ( spl8_18
    | spl8_19
    | spl8_11 ),
    inference(avatar_split_clause,[],[f539,f308,f558,f555])).

fof(f308,plain,
    ( spl8_11
  <=> m1_subset_1(k5_relat_1(sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(sK3,sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f539,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,sK5)))
        | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,X1))) )
    | spl8_11 ),
    inference(resolution,[],[f269,f310])).

fof(f310,plain,
    ( ~ m1_subset_1(k5_relat_1(sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(sK3,sK5)))
    | spl8_11 ),
    inference(avatar_component_clause,[],[f308])).

fof(f269,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(duplicate_literal_removal,[],[f268])).

fof(f268,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f78,f77])).

fof(f77,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

fof(f78,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relset_1)).

fof(f321,plain,
    ( ~ spl8_11
    | spl8_12 ),
    inference(avatar_split_clause,[],[f306,f312,f308])).

fof(f306,plain,
    ( sK5 = k2_relat_1(k5_relat_1(sK6,sK7))
    | ~ m1_subset_1(k5_relat_1(sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(sK3,sK5))) ),
    inference(superposition,[],[f66,f302])).

fof(f302,plain,(
    sK5 = k2_relset_1(sK3,sK5,k5_relat_1(sK6,sK7)) ),
    inference(subsumption_resolution,[],[f301,f47])).

fof(f301,plain,
    ( sK5 = k2_relset_1(sK3,sK5,k5_relat_1(sK6,sK7))
    | ~ v1_funct_1(sK6) ),
    inference(subsumption_resolution,[],[f300,f49])).

fof(f300,plain,
    ( sK5 = k2_relset_1(sK3,sK5,k5_relat_1(sK6,sK7))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | ~ v1_funct_1(sK6) ),
    inference(subsumption_resolution,[],[f299,f50])).

fof(f299,plain,
    ( sK5 = k2_relset_1(sK3,sK5,k5_relat_1(sK6,sK7))
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | ~ v1_funct_1(sK6) ),
    inference(subsumption_resolution,[],[f290,f52])).

fof(f290,plain,
    ( sK5 = k2_relset_1(sK3,sK5,k5_relat_1(sK6,sK7))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | ~ v1_funct_1(sK6) ),
    inference(superposition,[],[f53,f76])).

fof(f76,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
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
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f53,plain,(
    sK5 = k2_relset_1(sK3,sK5,k1_partfun1(sK3,sK4,sK4,sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:44:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (24874)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.49  % (24873)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.49  % (24874)Refutation not found, incomplete strategy% (24874)------------------------------
% 0.22/0.49  % (24874)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (24874)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (24874)Memory used [KB]: 6908
% 0.22/0.49  % (24874)Time elapsed: 0.051 s
% 0.22/0.49  % (24874)------------------------------
% 0.22/0.49  % (24874)------------------------------
% 0.22/0.49  % (24865)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.50  % (24869)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.50  % (24884)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.51  % (24883)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.51  % (24886)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.22/0.51  % (24865)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % (24868)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.51  % (24876)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.52  % (24878)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f677,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(avatar_sat_refutation,[],[f321,f560,f581,f600,f606,f607,f610,f676])).
% 0.22/0.52  fof(f676,plain,(
% 0.22/0.52    ~spl8_19),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f674])).
% 0.22/0.52  fof(f674,plain,(
% 0.22/0.52    $false | ~spl8_19),
% 0.22/0.52    inference(subsumption_resolution,[],[f52,f559])).
% 0.22/0.52  fof(f559,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,sK5)))) ) | ~spl8_19),
% 0.22/0.52    inference(avatar_component_clause,[],[f558])).
% 0.22/0.52  fof(f558,plain,(
% 0.22/0.52    spl8_19 <=> ! [X0] : ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,sK5)))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).
% 0.22/0.52  fof(f52,plain,(
% 0.22/0.52    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))),
% 0.22/0.52    inference(cnf_transformation,[],[f38])).
% 0.22/0.52  fof(f38,plain,(
% 0.22/0.52    (sK4 != k2_relset_1(sK3,sK4,sK6) & k1_xboole_0 != sK5 & v2_funct_1(sK7) & sK5 = k2_relset_1(sK3,sK5,k1_partfun1(sK3,sK4,sK4,sK5,sK6,sK7)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(sK7,sK4,sK5) & v1_funct_1(sK7)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK6,sK3,sK4) & v1_funct_1(sK6)),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7])],[f16,f37,f36])).
% 0.22/0.52  fof(f36,plain,(
% 0.22/0.52    ? [X0,X1,X2,X3] : (? [X4] : (k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2 & v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (? [X4] : (sK4 != k2_relset_1(sK3,sK4,sK6) & k1_xboole_0 != sK5 & v2_funct_1(X4) & sK5 = k2_relset_1(sK3,sK5,k1_partfun1(sK3,sK4,sK4,sK5,sK6,X4)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(X4,sK4,sK5) & v1_funct_1(X4)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK6,sK3,sK4) & v1_funct_1(sK6))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f37,plain,(
% 0.22/0.52    ? [X4] : (sK4 != k2_relset_1(sK3,sK4,sK6) & k1_xboole_0 != sK5 & v2_funct_1(X4) & sK5 = k2_relset_1(sK3,sK5,k1_partfun1(sK3,sK4,sK4,sK5,sK6,X4)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(X4,sK4,sK5) & v1_funct_1(X4)) => (sK4 != k2_relset_1(sK3,sK4,sK6) & k1_xboole_0 != sK5 & v2_funct_1(sK7) & sK5 = k2_relset_1(sK3,sK5,k1_partfun1(sK3,sK4,sK4,sK5,sK6,sK7)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(sK7,sK4,sK5) & v1_funct_1(sK7))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f16,plain,(
% 0.22/0.52    ? [X0,X1,X2,X3] : (? [X4] : (k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2 & v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.22/0.52    inference(flattening,[],[f15])).
% 0.22/0.52  fof(f15,plain,(
% 0.22/0.52    ? [X0,X1,X2,X3] : (? [X4] : (((k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2) & (v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.22/0.52    inference(ennf_transformation,[],[f14])).
% 0.22/0.52  fof(f14,negated_conjecture,(
% 0.22/0.52    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2) => (k2_relset_1(X0,X1,X3) = X1 | k1_xboole_0 = X2))))),
% 0.22/0.52    inference(negated_conjecture,[],[f13])).
% 0.22/0.52  fof(f13,conjecture,(
% 0.22/0.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2) => (k2_relset_1(X0,X1,X3) = X1 | k1_xboole_0 = X2))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_funct_2)).
% 0.22/0.52  fof(f610,plain,(
% 0.22/0.52    ~spl8_17),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f609])).
% 0.22/0.52  fof(f609,plain,(
% 0.22/0.52    $false | ~spl8_17),
% 0.22/0.52    inference(subsumption_resolution,[],[f608,f55])).
% 0.22/0.52  fof(f55,plain,(
% 0.22/0.52    k1_xboole_0 != sK5),
% 0.22/0.52    inference(cnf_transformation,[],[f38])).
% 0.22/0.52  fof(f608,plain,(
% 0.22/0.52    k1_xboole_0 = sK5 | ~spl8_17),
% 0.22/0.52    inference(resolution,[],[f411,f72])).
% 0.22/0.52  fof(f72,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~sP0(X0,X1) | k1_xboole_0 = X1) )),
% 0.22/0.52    inference(cnf_transformation,[],[f46])).
% 0.22/0.52  fof(f46,plain,(
% 0.22/0.52    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X1))),
% 0.22/0.52    inference(nnf_transformation,[],[f32])).
% 0.22/0.52  fof(f32,plain,(
% 0.22/0.52    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X1))),
% 0.22/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.22/0.52  fof(f411,plain,(
% 0.22/0.52    sP0(sK4,sK5) | ~spl8_17),
% 0.22/0.52    inference(avatar_component_clause,[],[f409])).
% 0.22/0.52  fof(f409,plain,(
% 0.22/0.52    spl8_17 <=> sP0(sK4,sK5)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).
% 0.22/0.52  fof(f607,plain,(
% 0.22/0.52    spl8_8 | ~spl8_12),
% 0.22/0.52    inference(avatar_split_clause,[],[f572,f312,f164])).
% 0.22/0.52  fof(f164,plain,(
% 0.22/0.52    spl8_8 <=> sK5 = k2_relat_1(sK7)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 0.22/0.52  fof(f312,plain,(
% 0.22/0.52    spl8_12 <=> sK5 = k2_relat_1(k5_relat_1(sK6,sK7))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).
% 0.22/0.52  fof(f572,plain,(
% 0.22/0.52    sK5 = k2_relat_1(sK7) | ~spl8_12),
% 0.22/0.52    inference(subsumption_resolution,[],[f571,f89])).
% 0.22/0.52  fof(f89,plain,(
% 0.22/0.52    v1_relat_1(sK7)),
% 0.22/0.52    inference(resolution,[],[f64,f52])).
% 0.22/0.52  fof(f64,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f20])).
% 0.22/0.52  fof(f20,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(ennf_transformation,[],[f5])).
% 0.22/0.52  fof(f5,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.52  fof(f571,plain,(
% 0.22/0.52    sK5 = k2_relat_1(sK7) | ~v1_relat_1(sK7) | ~spl8_12),
% 0.22/0.52    inference(subsumption_resolution,[],[f570,f88])).
% 0.22/0.52  fof(f88,plain,(
% 0.22/0.52    v1_relat_1(sK6)),
% 0.22/0.52    inference(resolution,[],[f64,f49])).
% 0.22/0.52  fof(f49,plain,(
% 0.22/0.52    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 0.22/0.52    inference(cnf_transformation,[],[f38])).
% 0.22/0.52  fof(f570,plain,(
% 0.22/0.52    ~v1_relat_1(sK6) | sK5 = k2_relat_1(sK7) | ~v1_relat_1(sK7) | ~spl8_12),
% 0.22/0.52    inference(subsumption_resolution,[],[f563,f157])).
% 0.22/0.52  fof(f157,plain,(
% 0.22/0.52    r1_tarski(k2_relat_1(sK7),sK5)),
% 0.22/0.52    inference(resolution,[],[f151,f62])).
% 0.22/0.52  fof(f62,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f41])).
% 0.22/0.52  fof(f41,plain,(
% 0.22/0.52    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.22/0.52    inference(nnf_transformation,[],[f2])).
% 0.22/0.52  fof(f2,axiom,(
% 0.22/0.52    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.52  fof(f151,plain,(
% 0.22/0.52    m1_subset_1(k2_relat_1(sK7),k1_zfmisc_1(sK5))),
% 0.22/0.52    inference(resolution,[],[f149,f52])).
% 0.22/0.52  fof(f149,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k2_relat_1(X2),k1_zfmisc_1(X1))) )),
% 0.22/0.52    inference(duplicate_literal_removal,[],[f148])).
% 0.22/0.52  fof(f148,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (m1_subset_1(k2_relat_1(X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.52    inference(superposition,[],[f67,f66])).
% 0.22/0.52  fof(f66,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f22])).
% 0.22/0.52  fof(f22,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(ennf_transformation,[],[f9])).
% 0.22/0.52  fof(f9,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.22/0.52  fof(f67,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f23])).
% 0.22/0.52  fof(f23,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(ennf_transformation,[],[f6])).
% 0.22/0.52  fof(f6,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).
% 0.22/0.52  fof(f563,plain,(
% 0.22/0.52    ~r1_tarski(k2_relat_1(sK7),sK5) | ~v1_relat_1(sK6) | sK5 = k2_relat_1(sK7) | ~v1_relat_1(sK7) | ~spl8_12),
% 0.22/0.52    inference(superposition,[],[f127,f314])).
% 0.22/0.52  fof(f314,plain,(
% 0.22/0.52    sK5 = k2_relat_1(k5_relat_1(sK6,sK7)) | ~spl8_12),
% 0.22/0.52    inference(avatar_component_clause,[],[f312])).
% 0.22/0.52  fof(f127,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X0),k2_relat_1(k5_relat_1(X1,X0))) | ~v1_relat_1(X1) | k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.52    inference(resolution,[],[f57,f61])).
% 0.22/0.52  fof(f61,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f40])).
% 0.22/0.52  fof(f40,plain,(
% 0.22/0.52    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.52    inference(flattening,[],[f39])).
% 0.22/0.52  fof(f39,plain,(
% 0.22/0.52    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.52    inference(nnf_transformation,[],[f1])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.52  fof(f57,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f17])).
% 0.22/0.52  fof(f17,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f3])).
% 0.22/0.52  fof(f3,axiom,(
% 0.22/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).
% 0.22/0.52  fof(f606,plain,(
% 0.22/0.52    spl8_16 | spl8_17),
% 0.22/0.52    inference(avatar_split_clause,[],[f605,f409,f405])).
% 0.22/0.52  fof(f405,plain,(
% 0.22/0.52    spl8_16 <=> sK4 = k1_relat_1(sK7)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).
% 0.22/0.52  fof(f605,plain,(
% 0.22/0.52    sP0(sK4,sK5) | sK4 = k1_relat_1(sK7)),
% 0.22/0.52    inference(subsumption_resolution,[],[f422,f51])).
% 0.22/0.52  fof(f51,plain,(
% 0.22/0.52    v1_funct_2(sK7,sK4,sK5)),
% 0.22/0.52    inference(cnf_transformation,[],[f38])).
% 0.22/0.52  fof(f422,plain,(
% 0.22/0.52    sP0(sK4,sK5) | sK4 = k1_relat_1(sK7) | ~v1_funct_2(sK7,sK4,sK5)),
% 0.22/0.52    inference(resolution,[],[f388,f86])).
% 0.22/0.52  fof(f86,plain,(
% 0.22/0.52    r1_tarski(sK7,k2_zfmisc_1(sK4,sK5))),
% 0.22/0.52    inference(resolution,[],[f62,f52])).
% 0.22/0.52  fof(f388,plain,(
% 0.22/0.52    ( ! [X6,X8,X7] : (~r1_tarski(X6,k2_zfmisc_1(X7,X8)) | sP0(X7,X8) | k1_relat_1(X6) = X7 | ~v1_funct_2(X6,X7,X8)) )),
% 0.22/0.52    inference(resolution,[],[f189,f63])).
% 0.22/0.52  fof(f63,plain,(
% 0.22/0.52    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f41])).
% 0.22/0.52  fof(f189,plain,(
% 0.22/0.52    ( ! [X4,X5,X3] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_2(X5,X3,X4) | sP0(X3,X4) | k1_relat_1(X5) = X3) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f187,f74])).
% 0.22/0.52  fof(f74,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP1(X0,X2,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f35])).
% 0.22/0.52  fof(f35,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((sP2(X2,X1,X0) & sP1(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(definition_folding,[],[f25,f34,f33,f32])).
% 0.22/0.52  fof(f33,plain,(
% 0.22/0.52    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | sP0(X0,X1) | ~sP1(X0,X2,X1))),
% 0.22/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.22/0.52  fof(f34,plain,(
% 0.22/0.52    ! [X2,X1,X0] : ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~sP2(X2,X1,X0))),
% 0.22/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.22/0.52  fof(f25,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(flattening,[],[f24])).
% 0.22/0.52  fof(f24,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(ennf_transformation,[],[f11])).
% 0.22/0.52  fof(f11,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.22/0.52  fof(f187,plain,(
% 0.22/0.52    ( ! [X4,X5,X3] : (k1_relat_1(X5) = X3 | ~v1_funct_2(X5,X3,X4) | sP0(X3,X4) | ~sP1(X3,X5,X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) )),
% 0.22/0.52    inference(superposition,[],[f70,f65])).
% 0.22/0.52  fof(f65,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f21])).
% 0.22/0.52  fof(f21,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(ennf_transformation,[],[f8])).
% 0.22/0.52  fof(f8,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.52  fof(f70,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2) | sP0(X0,X2) | ~sP1(X0,X1,X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f45])).
% 0.22/0.52  fof(f45,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | sP0(X0,X2) | ~sP1(X0,X1,X2))),
% 0.22/0.52    inference(rectify,[],[f44])).
% 0.22/0.52  fof(f44,plain,(
% 0.22/0.52    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | sP0(X0,X1) | ~sP1(X0,X2,X1))),
% 0.22/0.52    inference(nnf_transformation,[],[f33])).
% 0.22/0.52  fof(f600,plain,(
% 0.22/0.52    ~spl8_18),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f598])).
% 0.22/0.52  fof(f598,plain,(
% 0.22/0.52    $false | ~spl8_18),
% 0.22/0.52    inference(subsumption_resolution,[],[f49,f556])).
% 0.22/0.52  fof(f556,plain,(
% 0.22/0.52    ( ! [X1] : (~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,X1)))) ) | ~spl8_18),
% 0.22/0.52    inference(avatar_component_clause,[],[f555])).
% 0.22/0.52  fof(f555,plain,(
% 0.22/0.52    spl8_18 <=> ! [X1] : ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,X1)))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).
% 0.22/0.52  fof(f581,plain,(
% 0.22/0.52    ~spl8_8 | ~spl8_12 | ~spl8_16),
% 0.22/0.52    inference(avatar_split_clause,[],[f580,f405,f312,f164])).
% 0.22/0.52  fof(f580,plain,(
% 0.22/0.52    sK5 != k2_relat_1(sK7) | (~spl8_12 | ~spl8_16)),
% 0.22/0.52    inference(subsumption_resolution,[],[f579,f156])).
% 0.22/0.52  fof(f156,plain,(
% 0.22/0.52    ~r1_tarski(sK4,k2_relat_1(sK6))),
% 0.22/0.52    inference(subsumption_resolution,[],[f155,f140])).
% 0.22/0.52  fof(f140,plain,(
% 0.22/0.52    sK4 != k2_relat_1(sK6)),
% 0.22/0.52    inference(subsumption_resolution,[],[f129,f49])).
% 0.22/0.52  fof(f129,plain,(
% 0.22/0.52    sK4 != k2_relat_1(sK6) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 0.22/0.52    inference(superposition,[],[f56,f66])).
% 0.22/0.52  fof(f56,plain,(
% 0.22/0.52    sK4 != k2_relset_1(sK3,sK4,sK6)),
% 0.22/0.52    inference(cnf_transformation,[],[f38])).
% 0.22/0.52  fof(f155,plain,(
% 0.22/0.52    sK4 = k2_relat_1(sK6) | ~r1_tarski(sK4,k2_relat_1(sK6))),
% 0.22/0.52    inference(resolution,[],[f154,f61])).
% 0.22/0.52  fof(f154,plain,(
% 0.22/0.52    r1_tarski(k2_relat_1(sK6),sK4)),
% 0.22/0.52    inference(resolution,[],[f150,f62])).
% 0.22/0.52  fof(f150,plain,(
% 0.22/0.52    m1_subset_1(k2_relat_1(sK6),k1_zfmisc_1(sK4))),
% 0.22/0.52    inference(resolution,[],[f149,f49])).
% 0.22/0.52  fof(f579,plain,(
% 0.22/0.52    r1_tarski(sK4,k2_relat_1(sK6)) | sK5 != k2_relat_1(sK7) | (~spl8_12 | ~spl8_16)),
% 0.22/0.52    inference(forward_demodulation,[],[f578,f407])).
% 0.22/0.52  fof(f407,plain,(
% 0.22/0.52    sK4 = k1_relat_1(sK7) | ~spl8_16),
% 0.22/0.52    inference(avatar_component_clause,[],[f405])).
% 0.22/0.52  fof(f578,plain,(
% 0.22/0.52    sK5 != k2_relat_1(sK7) | r1_tarski(k1_relat_1(sK7),k2_relat_1(sK6)) | ~spl8_12),
% 0.22/0.52    inference(subsumption_resolution,[],[f577,f89])).
% 0.22/0.52  fof(f577,plain,(
% 0.22/0.52    sK5 != k2_relat_1(sK7) | r1_tarski(k1_relat_1(sK7),k2_relat_1(sK6)) | ~v1_relat_1(sK7) | ~spl8_12),
% 0.22/0.52    inference(subsumption_resolution,[],[f576,f50])).
% 0.22/0.52  fof(f50,plain,(
% 0.22/0.52    v1_funct_1(sK7)),
% 0.22/0.52    inference(cnf_transformation,[],[f38])).
% 0.22/0.52  fof(f576,plain,(
% 0.22/0.52    sK5 != k2_relat_1(sK7) | r1_tarski(k1_relat_1(sK7),k2_relat_1(sK6)) | ~v1_funct_1(sK7) | ~v1_relat_1(sK7) | ~spl8_12),
% 0.22/0.52    inference(subsumption_resolution,[],[f575,f88])).
% 0.22/0.52  fof(f575,plain,(
% 0.22/0.52    sK5 != k2_relat_1(sK7) | r1_tarski(k1_relat_1(sK7),k2_relat_1(sK6)) | ~v1_relat_1(sK6) | ~v1_funct_1(sK7) | ~v1_relat_1(sK7) | ~spl8_12),
% 0.22/0.52    inference(subsumption_resolution,[],[f574,f47])).
% 0.22/0.52  fof(f47,plain,(
% 0.22/0.52    v1_funct_1(sK6)),
% 0.22/0.52    inference(cnf_transformation,[],[f38])).
% 0.22/0.52  fof(f574,plain,(
% 0.22/0.52    sK5 != k2_relat_1(sK7) | r1_tarski(k1_relat_1(sK7),k2_relat_1(sK6)) | ~v1_funct_1(sK6) | ~v1_relat_1(sK6) | ~v1_funct_1(sK7) | ~v1_relat_1(sK7) | ~spl8_12),
% 0.22/0.52    inference(subsumption_resolution,[],[f564,f54])).
% 0.22/0.52  fof(f54,plain,(
% 0.22/0.52    v2_funct_1(sK7)),
% 0.22/0.52    inference(cnf_transformation,[],[f38])).
% 0.22/0.52  fof(f564,plain,(
% 0.22/0.52    sK5 != k2_relat_1(sK7) | ~v2_funct_1(sK7) | r1_tarski(k1_relat_1(sK7),k2_relat_1(sK6)) | ~v1_funct_1(sK6) | ~v1_relat_1(sK6) | ~v1_funct_1(sK7) | ~v1_relat_1(sK7) | ~spl8_12),
% 0.22/0.52    inference(superposition,[],[f58,f314])).
% 0.22/0.52  % (24872)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.52  fof(f58,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k2_relat_1(k5_relat_1(X1,X0)) != k2_relat_1(X0) | ~v2_funct_1(X0) | r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f19])).
% 0.22/0.52  fof(f19,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v2_funct_1(X0) | k2_relat_1(k5_relat_1(X1,X0)) != k2_relat_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(flattening,[],[f18])).
% 0.22/0.52  fof(f18,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : ((r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | (~v2_funct_1(X0) | k2_relat_1(k5_relat_1(X1,X0)) != k2_relat_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f4])).
% 0.22/0.52  fof(f4,axiom,(
% 0.22/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X0) & k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0)) => r1_tarski(k1_relat_1(X0),k2_relat_1(X1)))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_funct_1)).
% 0.22/0.52  fof(f560,plain,(
% 0.22/0.52    spl8_18 | spl8_19 | spl8_11),
% 0.22/0.52    inference(avatar_split_clause,[],[f539,f308,f558,f555])).
% 0.22/0.52  fof(f308,plain,(
% 0.22/0.52    spl8_11 <=> m1_subset_1(k5_relat_1(sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(sK3,sK5)))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 0.22/0.52  fof(f539,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,sK5))) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,X1)))) ) | spl8_11),
% 0.22/0.52    inference(resolution,[],[f269,f310])).
% 0.22/0.52  fof(f310,plain,(
% 0.22/0.52    ~m1_subset_1(k5_relat_1(sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(sK3,sK5))) | spl8_11),
% 0.22/0.52    inference(avatar_component_clause,[],[f308])).
% 0.22/0.52  fof(f269,plain,(
% 0.22/0.52    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.52    inference(duplicate_literal_removal,[],[f268])).
% 0.22/0.52  fof(f268,plain,(
% 0.22/0.52    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.52    inference(superposition,[],[f78,f77])).
% 0.22/0.52  fof(f77,plain,(
% 0.22/0.52    ( ! [X4,X2,X0,X5,X3,X1] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f29])).
% 0.22/0.52  fof(f29,plain,(
% 0.22/0.52    ! [X0,X1,X2,X3,X4,X5] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(flattening,[],[f28])).
% 0.22/0.52  fof(f28,plain,(
% 0.22/0.52    ! [X0,X1,X2,X3,X4,X5] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.22/0.52    inference(ennf_transformation,[],[f10])).
% 0.22/0.52  fof(f10,axiom,(
% 0.22/0.52    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_relset_1)).
% 0.22/0.52  fof(f78,plain,(
% 0.22/0.52    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f31])).
% 0.22/0.52  fof(f31,plain,(
% 0.22/0.52    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(flattening,[],[f30])).
% 0.22/0.52  fof(f30,plain,(
% 0.22/0.52    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.22/0.52    inference(ennf_transformation,[],[f7])).
% 0.22/0.52  fof(f7,axiom,(
% 0.22/0.52    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relset_1)).
% 0.22/0.52  fof(f321,plain,(
% 0.22/0.52    ~spl8_11 | spl8_12),
% 0.22/0.52    inference(avatar_split_clause,[],[f306,f312,f308])).
% 0.22/0.52  fof(f306,plain,(
% 0.22/0.52    sK5 = k2_relat_1(k5_relat_1(sK6,sK7)) | ~m1_subset_1(k5_relat_1(sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(sK3,sK5)))),
% 0.22/0.52    inference(superposition,[],[f66,f302])).
% 0.22/0.52  fof(f302,plain,(
% 0.22/0.52    sK5 = k2_relset_1(sK3,sK5,k5_relat_1(sK6,sK7))),
% 0.22/0.52    inference(subsumption_resolution,[],[f301,f47])).
% 0.22/0.52  fof(f301,plain,(
% 0.22/0.52    sK5 = k2_relset_1(sK3,sK5,k5_relat_1(sK6,sK7)) | ~v1_funct_1(sK6)),
% 0.22/0.52    inference(subsumption_resolution,[],[f300,f49])).
% 0.22/0.52  fof(f300,plain,(
% 0.22/0.52    sK5 = k2_relset_1(sK3,sK5,k5_relat_1(sK6,sK7)) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) | ~v1_funct_1(sK6)),
% 0.22/0.52    inference(subsumption_resolution,[],[f299,f50])).
% 0.22/0.52  fof(f299,plain,(
% 0.22/0.52    sK5 = k2_relset_1(sK3,sK5,k5_relat_1(sK6,sK7)) | ~v1_funct_1(sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) | ~v1_funct_1(sK6)),
% 0.22/0.52    inference(subsumption_resolution,[],[f290,f52])).
% 0.22/0.52  fof(f290,plain,(
% 0.22/0.52    sK5 = k2_relset_1(sK3,sK5,k5_relat_1(sK6,sK7)) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) | ~v1_funct_1(sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) | ~v1_funct_1(sK6)),
% 0.22/0.52    inference(superposition,[],[f53,f76])).
% 0.22/0.52  fof(f76,plain,(
% 0.22/0.52    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f27])).
% 0.22/0.52  fof(f27,plain,(
% 0.22/0.52    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 0.22/0.52    inference(flattening,[],[f26])).
% 0.22/0.52  fof(f26,plain,(
% 0.22/0.52    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 0.22/0.52    inference(ennf_transformation,[],[f12])).
% 0.22/0.52  fof(f12,axiom,(
% 0.22/0.52    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 0.22/0.52  fof(f53,plain,(
% 0.22/0.52    sK5 = k2_relset_1(sK3,sK5,k1_partfun1(sK3,sK4,sK4,sK5,sK6,sK7))),
% 0.22/0.52    inference(cnf_transformation,[],[f38])).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (24865)------------------------------
% 0.22/0.52  % (24865)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (24865)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (24865)Memory used [KB]: 6652
% 0.22/0.52  % (24865)Time elapsed: 0.099 s
% 0.22/0.52  % (24865)------------------------------
% 0.22/0.52  % (24865)------------------------------
% 0.22/0.52  % (24867)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.52  % (24885)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.52  % (24860)Success in time 0.152 s
%------------------------------------------------------------------------------
