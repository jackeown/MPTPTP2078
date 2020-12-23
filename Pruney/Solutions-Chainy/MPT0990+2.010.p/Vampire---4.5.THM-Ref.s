%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:29 EST 2020

% Result     : Theorem 1.87s
% Output     : Refutation 2.20s
% Verified   : 
% Statistics : Number of formulae       :  162 ( 320 expanded)
%              Number of leaves         :   37 ( 103 expanded)
%              Depth                    :   11
%              Number of atoms          :  491 (1545 expanded)
%              Number of equality atoms :   94 ( 428 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1916,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f162,f164,f176,f246,f248,f251,f415,f472,f474,f498,f505,f542,f575,f596,f670,f1773,f1832,f1859,f1904])).

fof(f1904,plain,(
    ~ spl4_126 ),
    inference(avatar_contradiction_clause,[],[f1871])).

fof(f1871,plain,
    ( $false
    | ~ spl4_126 ),
    inference(subsumption_resolution,[],[f52,f1820])).

fof(f1820,plain,
    ( sK3 = k2_funct_1(sK2)
    | ~ spl4_126 ),
    inference(avatar_component_clause,[],[f1818])).

fof(f1818,plain,
    ( spl4_126
  <=> sK3 = k2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_126])])).

fof(f52,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).

fof(f1859,plain,(
    spl4_125 ),
    inference(avatar_contradiction_clause,[],[f1857])).

fof(f1857,plain,
    ( $false
    | spl4_125 ),
    inference(unit_resulting_resolution,[],[f95,f106,f1816,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f1816,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),sK1)
    | spl4_125 ),
    inference(avatar_component_clause,[],[f1814])).

fof(f1814,plain,
    ( spl4_125
  <=> r1_tarski(k1_relat_1(sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_125])])).

fof(f106,plain,(
    v4_relat_1(sK3,sK1) ),
    inference(resolution,[],[f77,f46])).

fof(f46,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f22])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f95,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f75,f46])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f1832,plain,
    ( ~ spl4_32
    | ~ spl4_125
    | spl4_126
    | ~ spl4_120 ),
    inference(avatar_split_clause,[],[f1804,f1770,f1818,f1814,f517])).

fof(f517,plain,
    ( spl4_32
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f1770,plain,
    ( spl4_120
  <=> k2_funct_1(sK2) = k5_relat_1(k6_partfun1(sK1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_120])])).

fof(f1804,plain,
    ( sK3 = k2_funct_1(sK2)
    | ~ r1_tarski(k1_relat_1(sK3),sK1)
    | ~ v1_relat_1(sK3)
    | ~ spl4_120 ),
    inference(superposition,[],[f90,f1772])).

fof(f1772,plain,
    ( k2_funct_1(sK2) = k5_relat_1(k6_partfun1(sK1),sK3)
    | ~ spl4_120 ),
    inference(avatar_component_clause,[],[f1770])).

fof(f90,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_partfun1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f69,f56])).

fof(f56,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | k5_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).

fof(f1773,plain,
    ( ~ spl4_5
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_32
    | ~ spl4_3
    | spl4_120
    | ~ spl4_2
    | ~ spl4_30
    | ~ spl4_50 ),
    inference(avatar_split_clause,[],[f1768,f667,f483,f158,f1770,f167,f517,f237,f233,f229])).

fof(f229,plain,
    ( spl4_5
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f233,plain,
    ( spl4_6
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f237,plain,
    ( spl4_7
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f167,plain,
    ( spl4_3
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f158,plain,
    ( spl4_2
  <=> sK1 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f483,plain,
    ( spl4_30
  <=> k6_partfun1(sK0) = k5_relat_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f667,plain,
    ( spl4_50
  <=> k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_50])])).

fof(f1768,plain,
    ( k2_funct_1(sK2) = k5_relat_1(k6_partfun1(sK1),sK3)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ spl4_2
    | ~ spl4_30
    | ~ spl4_50 ),
    inference(forward_demodulation,[],[f1767,f669])).

fof(f669,plain,
    ( k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0))
    | ~ spl4_50 ),
    inference(avatar_component_clause,[],[f667])).

fof(f1767,plain,
    ( k5_relat_1(k6_partfun1(sK1),sK3) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0))
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ spl4_2
    | ~ spl4_30 ),
    inference(forward_demodulation,[],[f1691,f160])).

fof(f160,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f158])).

fof(f1691,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k5_relat_1(k6_partfun1(k2_relat_1(sK2)),sK3)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ spl4_30 ),
    inference(superposition,[],[f272,f485])).

fof(f485,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ spl4_30 ),
    inference(avatar_component_clause,[],[f483])).

fof(f272,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k2_funct_1(X0),k5_relat_1(X0,X1)) = k5_relat_1(k6_partfun1(k2_relat_1(X0)),X1)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f252])).

fof(f252,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k2_funct_1(X0),k5_relat_1(X0,X1)) = k5_relat_1(k6_partfun1(k2_relat_1(X0)),X1)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f62,f88])).

fof(f88,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f68,f56])).

fof(f68,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

fof(f670,plain,
    ( ~ spl4_3
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_7
    | spl4_50
    | ~ spl4_38 ),
    inference(avatar_split_clause,[],[f641,f572,f667,f237,f233,f229,f167])).

fof(f572,plain,
    ( spl4_38
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).

fof(f641,plain,
    ( k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_38 ),
    inference(superposition,[],[f135,f574])).

fof(f574,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl4_38 ),
    inference(avatar_component_clause,[],[f572])).

fof(f135,plain,(
    ! [X0] :
      ( k2_funct_1(X0) = k5_relat_1(k2_funct_1(X0),k6_partfun1(k1_relat_1(X0)))
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f87,f66])).

fof(f66,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f87,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f60,f56])).

fof(f60,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

fof(f596,plain,(
    spl4_37 ),
    inference(avatar_contradiction_clause,[],[f594])).

fof(f594,plain,
    ( $false
    | spl4_37 ),
    inference(unit_resulting_resolution,[],[f96,f107,f570,f71])).

fof(f570,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),sK0)
    | spl4_37 ),
    inference(avatar_component_clause,[],[f568])).

fof(f568,plain,
    ( spl4_37
  <=> r1_tarski(k1_relat_1(sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).

fof(f107,plain,(
    v4_relat_1(sK2,sK0) ),
    inference(resolution,[],[f77,f55])).

fof(f55,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f22])).

fof(f96,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f75,f55])).

fof(f575,plain,
    ( ~ spl4_32
    | ~ spl4_3
    | ~ spl4_37
    | spl4_38
    | ~ spl4_30 ),
    inference(avatar_split_clause,[],[f566,f483,f572,f568,f167,f517])).

fof(f566,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ r1_tarski(k1_relat_1(sK2),sK0)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ spl4_30 ),
    inference(forward_demodulation,[],[f565,f86])).

fof(f86,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f58,f56])).

fof(f58,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f565,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),sK0)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK3)
    | k1_relat_1(sK2) = k1_relat_1(k6_partfun1(sK0))
    | ~ spl4_30 ),
    inference(forward_demodulation,[],[f555,f86])).

fof(f555,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(k6_partfun1(sK0)))
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK3)
    | k1_relat_1(sK2) = k1_relat_1(k6_partfun1(sK0))
    | ~ spl4_30 ),
    inference(superposition,[],[f122,f485])).

fof(f122,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(k1_relat_1(X3),k1_relat_1(k5_relat_1(X3,X2)))
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X2)
      | k1_relat_1(X3) = k1_relat_1(k5_relat_1(X3,X2)) ) ),
    inference(resolution,[],[f61,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_relat_1)).

fof(f542,plain,(
    spl4_32 ),
    inference(avatar_contradiction_clause,[],[f539])).

fof(f539,plain,
    ( $false
    | spl4_32 ),
    inference(subsumption_resolution,[],[f95,f519])).

fof(f519,plain,
    ( ~ v1_relat_1(sK3)
    | spl4_32 ),
    inference(avatar_component_clause,[],[f517])).

fof(f505,plain,
    ( ~ spl4_6
    | ~ spl4_26
    | ~ spl4_27
    | ~ spl4_1
    | spl4_30
    | ~ spl4_25 ),
    inference(avatar_split_clause,[],[f502,f412,f483,f154,f458,f454,f233])).

fof(f454,plain,
    ( spl4_26
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f458,plain,
    ( spl4_27
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f154,plain,
    ( spl4_1
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f412,plain,
    ( spl4_25
  <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f502,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_25 ),
    inference(superposition,[],[f81,f414])).

fof(f414,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f412])).

fof(f81,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f498,plain,(
    spl4_24 ),
    inference(avatar_contradiction_clause,[],[f487])).

fof(f487,plain,
    ( $false
    | spl4_24 ),
    inference(unit_resulting_resolution,[],[f53,f44,f46,f55,f410,f83])).

fof(f83,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f410,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl4_24 ),
    inference(avatar_component_clause,[],[f408])).

fof(f408,plain,
    ( spl4_24
  <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f44,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f22])).

fof(f53,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f474,plain,(
    spl4_27 ),
    inference(avatar_contradiction_clause,[],[f473])).

fof(f473,plain,
    ( $false
    | spl4_27 ),
    inference(subsumption_resolution,[],[f44,f460])).

fof(f460,plain,
    ( ~ v1_funct_1(sK3)
    | spl4_27 ),
    inference(avatar_component_clause,[],[f458])).

fof(f472,plain,(
    spl4_26 ),
    inference(avatar_contradiction_clause,[],[f471])).

fof(f471,plain,
    ( $false
    | spl4_26 ),
    inference(subsumption_resolution,[],[f46,f456])).

fof(f456,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl4_26 ),
    inference(avatar_component_clause,[],[f454])).

fof(f415,plain,
    ( ~ spl4_24
    | spl4_25 ),
    inference(avatar_split_clause,[],[f405,f412,f408])).

fof(f405,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
    | ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f378,f48])).

fof(f48,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f378,plain,(
    ! [X2,X1] :
      ( ~ r2_relset_1(X2,X2,X1,k6_partfun1(X2))
      | k6_partfun1(X2) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ) ),
    inference(resolution,[],[f80,f84])).

fof(f84,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f57,f56])).

fof(f57,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f251,plain,(
    spl4_7 ),
    inference(avatar_contradiction_clause,[],[f249])).

fof(f249,plain,
    ( $false
    | spl4_7 ),
    inference(unit_resulting_resolution,[],[f96,f53,f239,f63])).

fof(f63,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f239,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | spl4_7 ),
    inference(avatar_component_clause,[],[f237])).

fof(f248,plain,(
    spl4_6 ),
    inference(avatar_contradiction_clause,[],[f247])).

fof(f247,plain,
    ( $false
    | spl4_6 ),
    inference(subsumption_resolution,[],[f53,f235])).

fof(f235,plain,
    ( ~ v1_funct_1(sK2)
    | spl4_6 ),
    inference(avatar_component_clause,[],[f233])).

fof(f246,plain,(
    spl4_5 ),
    inference(avatar_contradiction_clause,[],[f245])).

fof(f245,plain,
    ( $false
    | spl4_5 ),
    inference(subsumption_resolution,[],[f49,f231])).

fof(f231,plain,
    ( ~ v2_funct_1(sK2)
    | spl4_5 ),
    inference(avatar_component_clause,[],[f229])).

fof(f49,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f176,plain,(
    spl4_3 ),
    inference(avatar_contradiction_clause,[],[f175])).

fof(f175,plain,
    ( $false
    | spl4_3 ),
    inference(subsumption_resolution,[],[f96,f169])).

fof(f169,plain,
    ( ~ v1_relat_1(sK2)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f167])).

fof(f164,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f163])).

fof(f163,plain,
    ( $false
    | spl4_1 ),
    inference(subsumption_resolution,[],[f55,f156])).

fof(f156,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f154])).

fof(f162,plain,
    ( ~ spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f152,f158,f154])).

fof(f152,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f47,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f47,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:42:14 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.52  % (25946)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.52  % (25937)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.53  % (25930)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  % (25953)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.53  % (25945)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.55  % (25933)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.56  % (25938)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.56  % (25939)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.57  % (25947)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.57  % (25926)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.57  % (25948)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.57  % (25932)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.57  % (25934)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.57  % (25925)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.58  % (25928)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.58  % (25935)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.58  % (25952)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.66/0.59  % (25931)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.66/0.59  % (25940)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.66/0.59  % (25924)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.66/0.59  % (25944)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.66/0.59  % (25923)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.66/0.60  % (25940)Refutation not found, incomplete strategy% (25940)------------------------------
% 1.66/0.60  % (25940)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.66/0.60  % (25940)Termination reason: Refutation not found, incomplete strategy
% 1.66/0.60  
% 1.66/0.60  % (25940)Memory used [KB]: 10746
% 1.66/0.60  % (25940)Time elapsed: 0.169 s
% 1.66/0.60  % (25940)------------------------------
% 1.66/0.60  % (25940)------------------------------
% 1.66/0.60  % (25942)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.66/0.60  % (25949)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.66/0.60  % (25929)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.87/0.61  % (25950)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.87/0.61  % (25941)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.87/0.61  % (25951)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.87/0.61  % (25936)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.87/0.63  % (25943)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.87/0.63  % (25937)Refutation found. Thanks to Tanya!
% 1.87/0.63  % SZS status Theorem for theBenchmark
% 1.87/0.63  % SZS output start Proof for theBenchmark
% 1.87/0.63  fof(f1916,plain,(
% 1.87/0.63    $false),
% 1.87/0.63    inference(avatar_sat_refutation,[],[f162,f164,f176,f246,f248,f251,f415,f472,f474,f498,f505,f542,f575,f596,f670,f1773,f1832,f1859,f1904])).
% 1.87/0.63  fof(f1904,plain,(
% 1.87/0.63    ~spl4_126),
% 1.87/0.63    inference(avatar_contradiction_clause,[],[f1871])).
% 1.87/0.63  fof(f1871,plain,(
% 1.87/0.63    $false | ~spl4_126),
% 1.87/0.63    inference(subsumption_resolution,[],[f52,f1820])).
% 1.87/0.63  fof(f1820,plain,(
% 1.87/0.63    sK3 = k2_funct_1(sK2) | ~spl4_126),
% 1.87/0.63    inference(avatar_component_clause,[],[f1818])).
% 1.87/0.63  fof(f1818,plain,(
% 1.87/0.63    spl4_126 <=> sK3 = k2_funct_1(sK2)),
% 1.87/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_126])])).
% 1.87/0.63  fof(f52,plain,(
% 1.87/0.63    sK3 != k2_funct_1(sK2)),
% 1.87/0.63    inference(cnf_transformation,[],[f22])).
% 1.87/0.63  fof(f22,plain,(
% 1.87/0.63    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.87/0.63    inference(flattening,[],[f21])).
% 1.87/0.63  fof(f21,plain,(
% 1.87/0.63    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.87/0.63    inference(ennf_transformation,[],[f20])).
% 1.87/0.63  fof(f20,negated_conjecture,(
% 1.87/0.63    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.87/0.63    inference(negated_conjecture,[],[f19])).
% 1.87/0.63  fof(f19,conjecture,(
% 1.87/0.63    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.87/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).
% 1.87/0.63  fof(f1859,plain,(
% 1.87/0.63    spl4_125),
% 1.87/0.63    inference(avatar_contradiction_clause,[],[f1857])).
% 1.87/0.63  fof(f1857,plain,(
% 1.87/0.63    $false | spl4_125),
% 1.87/0.63    inference(unit_resulting_resolution,[],[f95,f106,f1816,f71])).
% 1.87/0.63  fof(f71,plain,(
% 1.87/0.63    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1) | ~v4_relat_1(X1,X0)) )),
% 1.87/0.63    inference(cnf_transformation,[],[f34])).
% 1.87/0.63  fof(f34,plain,(
% 1.87/0.63    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.87/0.63    inference(ennf_transformation,[],[f2])).
% 1.87/0.63  fof(f2,axiom,(
% 1.87/0.63    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 1.87/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 1.87/0.63  fof(f1816,plain,(
% 1.87/0.63    ~r1_tarski(k1_relat_1(sK3),sK1) | spl4_125),
% 1.87/0.63    inference(avatar_component_clause,[],[f1814])).
% 1.87/0.63  fof(f1814,plain,(
% 1.87/0.63    spl4_125 <=> r1_tarski(k1_relat_1(sK3),sK1)),
% 1.87/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_125])])).
% 1.87/0.63  fof(f106,plain,(
% 1.87/0.63    v4_relat_1(sK3,sK1)),
% 1.87/0.63    inference(resolution,[],[f77,f46])).
% 1.87/0.63  fof(f46,plain,(
% 1.87/0.63    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.87/0.63    inference(cnf_transformation,[],[f22])).
% 1.87/0.63  fof(f77,plain,(
% 1.87/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 1.87/0.63    inference(cnf_transformation,[],[f37])).
% 1.87/0.63  fof(f37,plain,(
% 1.87/0.63    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.87/0.63    inference(ennf_transformation,[],[f12])).
% 1.87/0.63  fof(f12,axiom,(
% 1.87/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.87/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.87/0.63  fof(f95,plain,(
% 1.87/0.63    v1_relat_1(sK3)),
% 1.87/0.63    inference(resolution,[],[f75,f46])).
% 1.87/0.63  fof(f75,plain,(
% 1.87/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.87/0.63    inference(cnf_transformation,[],[f35])).
% 1.87/0.63  fof(f35,plain,(
% 1.87/0.63    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.87/0.63    inference(ennf_transformation,[],[f11])).
% 1.87/0.63  fof(f11,axiom,(
% 1.87/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.87/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.87/0.63  fof(f1832,plain,(
% 1.87/0.63    ~spl4_32 | ~spl4_125 | spl4_126 | ~spl4_120),
% 1.87/0.63    inference(avatar_split_clause,[],[f1804,f1770,f1818,f1814,f517])).
% 1.87/0.63  fof(f517,plain,(
% 1.87/0.63    spl4_32 <=> v1_relat_1(sK3)),
% 1.87/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).
% 1.87/0.63  fof(f1770,plain,(
% 1.87/0.63    spl4_120 <=> k2_funct_1(sK2) = k5_relat_1(k6_partfun1(sK1),sK3)),
% 1.87/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_120])])).
% 1.87/0.63  fof(f1804,plain,(
% 1.87/0.63    sK3 = k2_funct_1(sK2) | ~r1_tarski(k1_relat_1(sK3),sK1) | ~v1_relat_1(sK3) | ~spl4_120),
% 1.87/0.63    inference(superposition,[],[f90,f1772])).
% 1.87/0.63  fof(f1772,plain,(
% 1.87/0.63    k2_funct_1(sK2) = k5_relat_1(k6_partfun1(sK1),sK3) | ~spl4_120),
% 1.87/0.63    inference(avatar_component_clause,[],[f1770])).
% 1.87/0.63  fof(f90,plain,(
% 1.87/0.63    ( ! [X0,X1] : (k5_relat_1(k6_partfun1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.87/0.63    inference(definition_unfolding,[],[f69,f56])).
% 1.87/0.63  fof(f56,plain,(
% 1.87/0.63    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.87/0.63    inference(cnf_transformation,[],[f18])).
% 1.87/0.63  fof(f18,axiom,(
% 1.87/0.63    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.87/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.87/0.63  fof(f69,plain,(
% 1.87/0.63    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k1_relat_1(X1),X0) | k5_relat_1(k6_relat_1(X0),X1) = X1) )),
% 1.87/0.63    inference(cnf_transformation,[],[f33])).
% 1.87/0.63  fof(f33,plain,(
% 1.87/0.63    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.87/0.63    inference(flattening,[],[f32])).
% 1.87/0.63  fof(f32,plain,(
% 1.87/0.63    ! [X0,X1] : ((k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.87/0.63    inference(ennf_transformation,[],[f6])).
% 1.87/0.63  fof(f6,axiom,(
% 1.87/0.63    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k5_relat_1(k6_relat_1(X0),X1) = X1))),
% 1.87/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).
% 1.87/0.63  fof(f1773,plain,(
% 1.87/0.63    ~spl4_5 | ~spl4_6 | ~spl4_7 | ~spl4_32 | ~spl4_3 | spl4_120 | ~spl4_2 | ~spl4_30 | ~spl4_50),
% 1.87/0.63    inference(avatar_split_clause,[],[f1768,f667,f483,f158,f1770,f167,f517,f237,f233,f229])).
% 1.87/0.63  fof(f229,plain,(
% 1.87/0.63    spl4_5 <=> v2_funct_1(sK2)),
% 1.87/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.87/0.63  fof(f233,plain,(
% 1.87/0.63    spl4_6 <=> v1_funct_1(sK2)),
% 1.87/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.87/0.63  fof(f237,plain,(
% 1.87/0.63    spl4_7 <=> v1_relat_1(k2_funct_1(sK2))),
% 1.87/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 1.87/0.63  fof(f167,plain,(
% 1.87/0.63    spl4_3 <=> v1_relat_1(sK2)),
% 1.87/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.87/0.63  fof(f158,plain,(
% 1.87/0.63    spl4_2 <=> sK1 = k2_relat_1(sK2)),
% 1.87/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.87/0.63  fof(f483,plain,(
% 1.87/0.63    spl4_30 <=> k6_partfun1(sK0) = k5_relat_1(sK2,sK3)),
% 1.87/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).
% 1.87/0.63  fof(f667,plain,(
% 1.87/0.63    spl4_50 <=> k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0))),
% 1.87/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_50])])).
% 1.87/0.63  fof(f1768,plain,(
% 1.87/0.63    k2_funct_1(sK2) = k5_relat_1(k6_partfun1(sK1),sK3) | ~v1_relat_1(sK2) | ~v1_relat_1(sK3) | ~v1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | (~spl4_2 | ~spl4_30 | ~spl4_50)),
% 1.87/0.63    inference(forward_demodulation,[],[f1767,f669])).
% 1.87/0.63  fof(f669,plain,(
% 1.87/0.63    k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) | ~spl4_50),
% 1.87/0.63    inference(avatar_component_clause,[],[f667])).
% 1.87/0.63  fof(f1767,plain,(
% 1.87/0.63    k5_relat_1(k6_partfun1(sK1),sK3) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) | ~v1_relat_1(sK2) | ~v1_relat_1(sK3) | ~v1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | (~spl4_2 | ~spl4_30)),
% 1.87/0.63    inference(forward_demodulation,[],[f1691,f160])).
% 1.87/0.63  fof(f160,plain,(
% 1.87/0.63    sK1 = k2_relat_1(sK2) | ~spl4_2),
% 1.87/0.63    inference(avatar_component_clause,[],[f158])).
% 1.87/0.63  fof(f1691,plain,(
% 1.87/0.63    k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k5_relat_1(k6_partfun1(k2_relat_1(sK2)),sK3) | ~v1_relat_1(sK2) | ~v1_relat_1(sK3) | ~v1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~spl4_30),
% 1.87/0.63    inference(superposition,[],[f272,f485])).
% 1.87/0.63  fof(f485,plain,(
% 1.87/0.63    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~spl4_30),
% 1.87/0.63    inference(avatar_component_clause,[],[f483])).
% 1.87/0.63  fof(f272,plain,(
% 1.87/0.63    ( ! [X0,X1] : (k5_relat_1(k2_funct_1(X0),k5_relat_1(X0,X1)) = k5_relat_1(k6_partfun1(k2_relat_1(X0)),X1) | ~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0)) )),
% 1.87/0.63    inference(duplicate_literal_removal,[],[f252])).
% 1.87/0.63  fof(f252,plain,(
% 1.87/0.63    ( ! [X0,X1] : (k5_relat_1(k2_funct_1(X0),k5_relat_1(X0,X1)) = k5_relat_1(k6_partfun1(k2_relat_1(X0)),X1) | ~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.87/0.63    inference(superposition,[],[f62,f88])).
% 1.87/0.63  fof(f88,plain,(
% 1.87/0.63    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.87/0.63    inference(definition_unfolding,[],[f68,f56])).
% 1.87/0.63  fof(f68,plain,(
% 1.87/0.63    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)) )),
% 1.87/0.63    inference(cnf_transformation,[],[f31])).
% 1.87/0.63  fof(f31,plain,(
% 1.87/0.63    ! [X0] : ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.87/0.63    inference(flattening,[],[f30])).
% 1.87/0.63  fof(f30,plain,(
% 1.87/0.63    ! [X0] : (((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.87/0.63    inference(ennf_transformation,[],[f10])).
% 1.87/0.63  fof(f10,axiom,(
% 1.87/0.63    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 1.87/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).
% 2.20/0.65  fof(f62,plain,(
% 2.20/0.65    ( ! [X2,X0,X1] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | ~v1_relat_1(X0)) )),
% 2.20/0.65    inference(cnf_transformation,[],[f25])).
% 2.20/0.65  fof(f25,plain,(
% 2.20/0.65    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.20/0.65    inference(ennf_transformation,[],[f4])).
% 2.20/0.65  fof(f4,axiom,(
% 2.20/0.65    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)))))),
% 2.20/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).
% 2.20/0.65  fof(f670,plain,(
% 2.20/0.65    ~spl4_3 | ~spl4_5 | ~spl4_6 | ~spl4_7 | spl4_50 | ~spl4_38),
% 2.20/0.65    inference(avatar_split_clause,[],[f641,f572,f667,f237,f233,f229,f167])).
% 2.20/0.65  fof(f572,plain,(
% 2.20/0.65    spl4_38 <=> sK0 = k1_relat_1(sK2)),
% 2.20/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).
% 2.20/0.65  fof(f641,plain,(
% 2.20/0.65    k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) | ~v1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl4_38),
% 2.20/0.65    inference(superposition,[],[f135,f574])).
% 2.20/0.65  fof(f574,plain,(
% 2.20/0.65    sK0 = k1_relat_1(sK2) | ~spl4_38),
% 2.20/0.65    inference(avatar_component_clause,[],[f572])).
% 2.20/0.65  fof(f135,plain,(
% 2.20/0.65    ( ! [X0] : (k2_funct_1(X0) = k5_relat_1(k2_funct_1(X0),k6_partfun1(k1_relat_1(X0))) | ~v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.20/0.65    inference(superposition,[],[f87,f66])).
% 2.20/0.65  fof(f66,plain,(
% 2.20/0.65    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.20/0.65    inference(cnf_transformation,[],[f29])).
% 2.20/0.65  fof(f29,plain,(
% 2.20/0.65    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.20/0.65    inference(flattening,[],[f28])).
% 2.20/0.65  fof(f28,plain,(
% 2.20/0.65    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.20/0.65    inference(ennf_transformation,[],[f9])).
% 2.20/0.65  fof(f9,axiom,(
% 2.20/0.65    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 2.20/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 2.20/0.65  fof(f87,plain,(
% 2.20/0.65    ( ! [X0] : (k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 2.20/0.65    inference(definition_unfolding,[],[f60,f56])).
% 2.20/0.65  fof(f60,plain,(
% 2.20/0.65    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0) )),
% 2.20/0.65    inference(cnf_transformation,[],[f23])).
% 2.20/0.65  fof(f23,plain,(
% 2.20/0.65    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 2.20/0.65    inference(ennf_transformation,[],[f7])).
% 2.20/0.65  fof(f7,axiom,(
% 2.20/0.65    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 2.20/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).
% 2.20/0.65  fof(f596,plain,(
% 2.20/0.65    spl4_37),
% 2.20/0.65    inference(avatar_contradiction_clause,[],[f594])).
% 2.20/0.65  fof(f594,plain,(
% 2.20/0.65    $false | spl4_37),
% 2.20/0.65    inference(unit_resulting_resolution,[],[f96,f107,f570,f71])).
% 2.20/0.65  fof(f570,plain,(
% 2.20/0.65    ~r1_tarski(k1_relat_1(sK2),sK0) | spl4_37),
% 2.20/0.65    inference(avatar_component_clause,[],[f568])).
% 2.20/0.65  fof(f568,plain,(
% 2.20/0.65    spl4_37 <=> r1_tarski(k1_relat_1(sK2),sK0)),
% 2.20/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).
% 2.20/0.65  fof(f107,plain,(
% 2.20/0.65    v4_relat_1(sK2,sK0)),
% 2.20/0.65    inference(resolution,[],[f77,f55])).
% 2.20/0.65  fof(f55,plain,(
% 2.20/0.65    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.20/0.65    inference(cnf_transformation,[],[f22])).
% 2.20/0.65  fof(f96,plain,(
% 2.20/0.65    v1_relat_1(sK2)),
% 2.20/0.65    inference(resolution,[],[f75,f55])).
% 2.20/0.65  fof(f575,plain,(
% 2.20/0.65    ~spl4_32 | ~spl4_3 | ~spl4_37 | spl4_38 | ~spl4_30),
% 2.20/0.65    inference(avatar_split_clause,[],[f566,f483,f572,f568,f167,f517])).
% 2.20/0.65  fof(f566,plain,(
% 2.20/0.65    sK0 = k1_relat_1(sK2) | ~r1_tarski(k1_relat_1(sK2),sK0) | ~v1_relat_1(sK2) | ~v1_relat_1(sK3) | ~spl4_30),
% 2.20/0.65    inference(forward_demodulation,[],[f565,f86])).
% 2.20/0.65  fof(f86,plain,(
% 2.20/0.65    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 2.20/0.65    inference(definition_unfolding,[],[f58,f56])).
% 2.20/0.65  fof(f58,plain,(
% 2.20/0.65    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 2.20/0.65    inference(cnf_transformation,[],[f5])).
% 2.20/0.65  fof(f5,axiom,(
% 2.20/0.65    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 2.20/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 2.20/0.65  fof(f565,plain,(
% 2.20/0.65    ~r1_tarski(k1_relat_1(sK2),sK0) | ~v1_relat_1(sK2) | ~v1_relat_1(sK3) | k1_relat_1(sK2) = k1_relat_1(k6_partfun1(sK0)) | ~spl4_30),
% 2.20/0.65    inference(forward_demodulation,[],[f555,f86])).
% 2.20/0.65  fof(f555,plain,(
% 2.20/0.65    ~r1_tarski(k1_relat_1(sK2),k1_relat_1(k6_partfun1(sK0))) | ~v1_relat_1(sK2) | ~v1_relat_1(sK3) | k1_relat_1(sK2) = k1_relat_1(k6_partfun1(sK0)) | ~spl4_30),
% 2.20/0.65    inference(superposition,[],[f122,f485])).
% 2.20/0.65  fof(f122,plain,(
% 2.20/0.65    ( ! [X2,X3] : (~r1_tarski(k1_relat_1(X3),k1_relat_1(k5_relat_1(X3,X2))) | ~v1_relat_1(X3) | ~v1_relat_1(X2) | k1_relat_1(X3) = k1_relat_1(k5_relat_1(X3,X2))) )),
% 2.20/0.65    inference(resolution,[],[f61,f74])).
% 2.20/0.65  fof(f74,plain,(
% 2.20/0.65    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 2.20/0.65    inference(cnf_transformation,[],[f1])).
% 2.20/0.65  fof(f1,axiom,(
% 2.20/0.65    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.20/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.20/0.65  fof(f61,plain,(
% 2.20/0.65    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.20/0.65    inference(cnf_transformation,[],[f24])).
% 2.20/0.65  fof(f24,plain,(
% 2.20/0.65    ! [X0] : (! [X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.20/0.65    inference(ennf_transformation,[],[f3])).
% 2.20/0.65  fof(f3,axiom,(
% 2.20/0.65    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))))),
% 2.20/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_relat_1)).
% 2.20/0.65  fof(f542,plain,(
% 2.20/0.65    spl4_32),
% 2.20/0.65    inference(avatar_contradiction_clause,[],[f539])).
% 2.20/0.65  fof(f539,plain,(
% 2.20/0.65    $false | spl4_32),
% 2.20/0.65    inference(subsumption_resolution,[],[f95,f519])).
% 2.20/0.65  fof(f519,plain,(
% 2.20/0.65    ~v1_relat_1(sK3) | spl4_32),
% 2.20/0.65    inference(avatar_component_clause,[],[f517])).
% 2.20/0.65  fof(f505,plain,(
% 2.20/0.65    ~spl4_6 | ~spl4_26 | ~spl4_27 | ~spl4_1 | spl4_30 | ~spl4_25),
% 2.20/0.65    inference(avatar_split_clause,[],[f502,f412,f483,f154,f458,f454,f233])).
% 2.20/0.65  fof(f454,plain,(
% 2.20/0.65    spl4_26 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.20/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 2.20/0.65  fof(f458,plain,(
% 2.20/0.65    spl4_27 <=> v1_funct_1(sK3)),
% 2.20/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).
% 2.20/0.65  fof(f154,plain,(
% 2.20/0.65    spl4_1 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.20/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 2.20/0.65  fof(f412,plain,(
% 2.20/0.65    spl4_25 <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)),
% 2.20/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 2.20/0.65  fof(f502,plain,(
% 2.20/0.65    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK2) | ~spl4_25),
% 2.20/0.65    inference(superposition,[],[f81,f414])).
% 2.20/0.65  fof(f414,plain,(
% 2.20/0.65    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) | ~spl4_25),
% 2.20/0.65    inference(avatar_component_clause,[],[f412])).
% 2.20/0.65  fof(f81,plain,(
% 2.20/0.65    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X4)) )),
% 2.20/0.65    inference(cnf_transformation,[],[f41])).
% 2.20/0.65  fof(f41,plain,(
% 2.20/0.65    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.20/0.65    inference(flattening,[],[f40])).
% 2.20/0.65  fof(f40,plain,(
% 2.20/0.65    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.20/0.65    inference(ennf_transformation,[],[f17])).
% 2.20/0.65  fof(f17,axiom,(
% 2.20/0.65    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 2.20/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 2.20/0.65  fof(f498,plain,(
% 2.20/0.65    spl4_24),
% 2.20/0.65    inference(avatar_contradiction_clause,[],[f487])).
% 2.20/0.65  fof(f487,plain,(
% 2.20/0.65    $false | spl4_24),
% 2.20/0.65    inference(unit_resulting_resolution,[],[f53,f44,f46,f55,f410,f83])).
% 2.20/0.65  fof(f83,plain,(
% 2.20/0.65    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X4)) )),
% 2.20/0.65    inference(cnf_transformation,[],[f43])).
% 2.20/0.65  fof(f43,plain,(
% 2.20/0.65    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.20/0.65    inference(flattening,[],[f42])).
% 2.20/0.65  fof(f42,plain,(
% 2.20/0.65    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.20/0.65    inference(ennf_transformation,[],[f16])).
% 2.20/0.65  fof(f16,axiom,(
% 2.20/0.65    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 2.20/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 2.20/0.65  fof(f410,plain,(
% 2.20/0.65    ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl4_24),
% 2.20/0.65    inference(avatar_component_clause,[],[f408])).
% 2.20/0.65  fof(f408,plain,(
% 2.20/0.65    spl4_24 <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.20/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 2.20/0.65  fof(f44,plain,(
% 2.20/0.65    v1_funct_1(sK3)),
% 2.20/0.65    inference(cnf_transformation,[],[f22])).
% 2.20/0.65  fof(f53,plain,(
% 2.20/0.65    v1_funct_1(sK2)),
% 2.20/0.65    inference(cnf_transformation,[],[f22])).
% 2.20/0.65  fof(f474,plain,(
% 2.20/0.65    spl4_27),
% 2.20/0.65    inference(avatar_contradiction_clause,[],[f473])).
% 2.20/0.65  fof(f473,plain,(
% 2.20/0.65    $false | spl4_27),
% 2.20/0.65    inference(subsumption_resolution,[],[f44,f460])).
% 2.20/0.65  fof(f460,plain,(
% 2.20/0.65    ~v1_funct_1(sK3) | spl4_27),
% 2.20/0.65    inference(avatar_component_clause,[],[f458])).
% 2.20/0.65  fof(f472,plain,(
% 2.20/0.65    spl4_26),
% 2.20/0.65    inference(avatar_contradiction_clause,[],[f471])).
% 2.20/0.65  fof(f471,plain,(
% 2.20/0.65    $false | spl4_26),
% 2.20/0.65    inference(subsumption_resolution,[],[f46,f456])).
% 2.20/0.65  fof(f456,plain,(
% 2.20/0.65    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl4_26),
% 2.20/0.65    inference(avatar_component_clause,[],[f454])).
% 2.20/0.65  fof(f415,plain,(
% 2.20/0.65    ~spl4_24 | spl4_25),
% 2.20/0.65    inference(avatar_split_clause,[],[f405,f412,f408])).
% 2.20/0.65  fof(f405,plain,(
% 2.20/0.65    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) | ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.20/0.65    inference(resolution,[],[f378,f48])).
% 2.20/0.65  fof(f48,plain,(
% 2.20/0.65    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 2.20/0.65    inference(cnf_transformation,[],[f22])).
% 2.20/0.65  fof(f378,plain,(
% 2.20/0.65    ( ! [X2,X1] : (~r2_relset_1(X2,X2,X1,k6_partfun1(X2)) | k6_partfun1(X2) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))) )),
% 2.20/0.65    inference(resolution,[],[f80,f84])).
% 2.20/0.65  fof(f84,plain,(
% 2.20/0.65    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.20/0.65    inference(definition_unfolding,[],[f57,f56])).
% 2.20/0.65  fof(f57,plain,(
% 2.20/0.65    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.20/0.65    inference(cnf_transformation,[],[f15])).
% 2.20/0.65  fof(f15,axiom,(
% 2.20/0.65    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 2.20/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).
% 2.20/0.65  fof(f80,plain,(
% 2.20/0.65    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 = X3 | ~r2_relset_1(X0,X1,X2,X3)) )),
% 2.20/0.65    inference(cnf_transformation,[],[f39])).
% 2.20/0.65  fof(f39,plain,(
% 2.20/0.65    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.20/0.65    inference(flattening,[],[f38])).
% 2.20/0.65  fof(f38,plain,(
% 2.20/0.65    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.20/0.65    inference(ennf_transformation,[],[f14])).
% 2.20/0.65  fof(f14,axiom,(
% 2.20/0.65    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 2.20/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 2.20/0.65  fof(f251,plain,(
% 2.20/0.65    spl4_7),
% 2.20/0.65    inference(avatar_contradiction_clause,[],[f249])).
% 2.20/0.65  fof(f249,plain,(
% 2.20/0.65    $false | spl4_7),
% 2.20/0.65    inference(unit_resulting_resolution,[],[f96,f53,f239,f63])).
% 2.20/0.65  fof(f63,plain,(
% 2.20/0.65    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.20/0.65    inference(cnf_transformation,[],[f27])).
% 2.20/0.65  fof(f27,plain,(
% 2.20/0.65    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.20/0.65    inference(flattening,[],[f26])).
% 2.20/0.65  fof(f26,plain,(
% 2.20/0.65    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.20/0.65    inference(ennf_transformation,[],[f8])).
% 2.20/0.65  fof(f8,axiom,(
% 2.20/0.65    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 2.20/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 2.20/0.65  fof(f239,plain,(
% 2.20/0.65    ~v1_relat_1(k2_funct_1(sK2)) | spl4_7),
% 2.20/0.65    inference(avatar_component_clause,[],[f237])).
% 2.20/0.65  fof(f248,plain,(
% 2.20/0.65    spl4_6),
% 2.20/0.65    inference(avatar_contradiction_clause,[],[f247])).
% 2.20/0.65  fof(f247,plain,(
% 2.20/0.65    $false | spl4_6),
% 2.20/0.65    inference(subsumption_resolution,[],[f53,f235])).
% 2.20/0.65  fof(f235,plain,(
% 2.20/0.65    ~v1_funct_1(sK2) | spl4_6),
% 2.20/0.65    inference(avatar_component_clause,[],[f233])).
% 2.20/0.65  fof(f246,plain,(
% 2.20/0.65    spl4_5),
% 2.20/0.65    inference(avatar_contradiction_clause,[],[f245])).
% 2.20/0.65  fof(f245,plain,(
% 2.20/0.65    $false | spl4_5),
% 2.20/0.65    inference(subsumption_resolution,[],[f49,f231])).
% 2.20/0.65  fof(f231,plain,(
% 2.20/0.65    ~v2_funct_1(sK2) | spl4_5),
% 2.20/0.65    inference(avatar_component_clause,[],[f229])).
% 2.20/0.65  fof(f49,plain,(
% 2.20/0.65    v2_funct_1(sK2)),
% 2.20/0.65    inference(cnf_transformation,[],[f22])).
% 2.20/0.65  fof(f176,plain,(
% 2.20/0.65    spl4_3),
% 2.20/0.65    inference(avatar_contradiction_clause,[],[f175])).
% 2.20/0.65  fof(f175,plain,(
% 2.20/0.65    $false | spl4_3),
% 2.20/0.65    inference(subsumption_resolution,[],[f96,f169])).
% 2.20/0.65  fof(f169,plain,(
% 2.20/0.65    ~v1_relat_1(sK2) | spl4_3),
% 2.20/0.65    inference(avatar_component_clause,[],[f167])).
% 2.20/0.65  fof(f164,plain,(
% 2.20/0.65    spl4_1),
% 2.20/0.65    inference(avatar_contradiction_clause,[],[f163])).
% 2.20/0.65  fof(f163,plain,(
% 2.20/0.65    $false | spl4_1),
% 2.20/0.65    inference(subsumption_resolution,[],[f55,f156])).
% 2.20/0.65  fof(f156,plain,(
% 2.20/0.65    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl4_1),
% 2.20/0.65    inference(avatar_component_clause,[],[f154])).
% 2.20/0.65  fof(f162,plain,(
% 2.20/0.65    ~spl4_1 | spl4_2),
% 2.20/0.65    inference(avatar_split_clause,[],[f152,f158,f154])).
% 2.20/0.65  fof(f152,plain,(
% 2.20/0.65    sK1 = k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.20/0.65    inference(superposition,[],[f47,f76])).
% 2.20/0.65  fof(f76,plain,(
% 2.20/0.65    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.20/0.65    inference(cnf_transformation,[],[f36])).
% 2.20/0.65  fof(f36,plain,(
% 2.20/0.65    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.20/0.65    inference(ennf_transformation,[],[f13])).
% 2.20/0.65  fof(f13,axiom,(
% 2.20/0.65    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 2.20/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 2.20/0.65  fof(f47,plain,(
% 2.20/0.65    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 2.20/0.65    inference(cnf_transformation,[],[f22])).
% 2.20/0.65  % SZS output end Proof for theBenchmark
% 2.20/0.65  % (25937)------------------------------
% 2.20/0.65  % (25937)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.20/0.65  % (25937)Termination reason: Refutation
% 2.20/0.65  
% 2.20/0.65  % (25937)Memory used [KB]: 7675
% 2.20/0.65  % (25937)Time elapsed: 0.209 s
% 2.20/0.65  % (25937)------------------------------
% 2.20/0.65  % (25937)------------------------------
% 2.20/0.65  % (25922)Success in time 0.29 s
%------------------------------------------------------------------------------
