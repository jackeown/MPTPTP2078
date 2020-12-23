%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:39 EST 2020

% Result     : Theorem 4.97s
% Output     : Refutation 4.97s
% Verified   : 
% Statistics : Number of formulae       :  362 (1428 expanded)
%              Number of leaves         :   55 ( 444 expanded)
%              Depth                    :   27
%              Number of atoms          : 1542 (9363 expanded)
%              Number of equality atoms :  284 ( 722 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8257,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f308,f506,f676,f813,f932,f955,f4474,f4705,f5343,f5370,f5377,f5381,f5574,f6442,f7035,f7668,f7953,f8027,f8067,f8097,f8106,f8172,f8224,f8256])).

fof(f8256,plain,
    ( ~ spl7_10
    | spl7_30
    | spl7_154
    | ~ spl7_272 ),
    inference(avatar_contradiction_clause,[],[f8255])).

fof(f8255,plain,
    ( $false
    | ~ spl7_10
    | spl7_30
    | spl7_154
    | ~ spl7_272 ),
    inference(subsumption_resolution,[],[f8254,f3913])).

fof(f3913,plain,
    ( k6_partfun1(sK0) != k6_relat_1(sK0)
    | spl7_154 ),
    inference(avatar_component_clause,[],[f3912])).

fof(f3912,plain,
    ( spl7_154
  <=> k6_partfun1(sK0) = k6_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_154])])).

fof(f8254,plain,
    ( k6_partfun1(sK0) = k6_relat_1(sK0)
    | ~ spl7_10
    | spl7_30
    | ~ spl7_272 ),
    inference(backward_demodulation,[],[f8247,f7907])).

fof(f7907,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK0)
    | ~ spl7_10
    | ~ spl7_272 ),
    inference(forward_demodulation,[],[f287,f7877])).

fof(f7877,plain,
    ( sK0 = k2_relat_1(sK2)
    | ~ spl7_272 ),
    inference(subsumption_resolution,[],[f7871,f123])).

fof(f123,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f103])).

fof(f103,plain,
    ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1))
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0))
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v3_funct_2(sK2,sK0,sK0)
    & v1_funct_2(sK2,sK0,sK0)
    & v1_funct_1(sK2)
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v3_funct_2(sK1,sK0,sK0)
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f44,f102,f101])).

fof(f101,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1))
            & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v3_funct_2(X2,X0,X0)
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( ? [X2] :
          ( ~ r2_relset_1(sK0,sK0,X2,k2_funct_2(sK0,sK1))
          & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0))
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
          & v3_funct_2(X2,sK0,sK0)
          & v1_funct_2(X2,sK0,sK0)
          & v1_funct_1(X2) )
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v3_funct_2(sK1,sK0,sK0)
      & v1_funct_2(sK1,sK0,sK0)
      & v1_funct_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f102,plain,
    ( ? [X2] :
        ( ~ r2_relset_1(sK0,sK0,X2,k2_funct_2(sK0,sK1))
        & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        & v3_funct_2(X2,sK0,sK0)
        & v1_funct_2(X2,sK0,sK0)
        & v1_funct_1(X2) )
   => ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1))
      & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0))
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v3_funct_2(sK2,sK0,sK0)
      & v1_funct_2(sK2,sK0,sK0)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X2,X0,X0)
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X2,X0,X0)
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f42])).

fof(f42,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X1,X0,X0)
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ! [X2] :
            ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v3_funct_2(X2,X0,X0)
              & v1_funct_2(X2,X0,X0)
              & v1_funct_1(X2) )
           => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
             => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f41])).

fof(f41,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v3_funct_2(X2,X0,X0)
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
         => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
           => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_funct_2)).

fof(f7871,plain,
    ( sK0 = k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl7_272 ),
    inference(superposition,[],[f7007,f174])).

fof(f174,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f75,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f7007,plain,
    ( sK0 = k2_relset_1(sK0,sK0,sK2)
    | ~ spl7_272 ),
    inference(avatar_component_clause,[],[f7005])).

fof(f7005,plain,
    ( spl7_272
  <=> sK0 = k2_relset_1(sK0,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_272])])).

fof(f287,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2))
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f285])).

fof(f285,plain,
    ( spl7_10
  <=> k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f8247,plain,
    ( k6_partfun1(sK0) = k5_relat_1(k2_funct_1(sK2),sK2)
    | spl7_30 ),
    inference(subsumption_resolution,[],[f8246,f120])).

fof(f120,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f103])).

fof(f8246,plain,
    ( k6_partfun1(sK0) = k5_relat_1(k2_funct_1(sK2),sK2)
    | ~ v1_funct_1(sK2)
    | spl7_30 ),
    inference(subsumption_resolution,[],[f8245,f121])).

fof(f121,plain,(
    v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f103])).

fof(f8245,plain,
    ( k6_partfun1(sK0) = k5_relat_1(k2_funct_1(sK2),sK2)
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2)
    | spl7_30 ),
    inference(subsumption_resolution,[],[f8244,f123])).

fof(f8244,plain,
    ( k6_partfun1(sK0) = k5_relat_1(k2_funct_1(sK2),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2)
    | spl7_30 ),
    inference(subsumption_resolution,[],[f8243,f222])).

fof(f222,plain,(
    v2_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f221,f123])).

fof(f221,plain,
    ( v2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f218,f120])).

fof(f218,plain,
    ( v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f184,f122])).

fof(f122,plain,(
    v3_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f103])).

fof(f184,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_funct_2(X2,X0,X1)
      | v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f81])).

fof(f81,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f80])).

fof(f80,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).

fof(f8243,plain,
    ( ~ v2_funct_1(sK2)
    | k6_partfun1(sK0) = k5_relat_1(k2_funct_1(sK2),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2)
    | spl7_30 ),
    inference(subsumption_resolution,[],[f8242,f605])).

fof(f605,plain,
    ( k1_xboole_0 != sK0
    | spl7_30 ),
    inference(avatar_component_clause,[],[f604])).

fof(f604,plain,
    ( spl7_30
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).

fof(f8242,plain,
    ( k1_xboole_0 = sK0
    | ~ v2_funct_1(sK2)
    | k6_partfun1(sK0) = k5_relat_1(k2_funct_1(sK2),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2) ),
    inference(trivial_inequality_removal,[],[f8238])).

fof(f8238,plain,
    ( sK0 != sK0
    | k1_xboole_0 = sK0
    | ~ v2_funct_1(sK2)
    | k6_partfun1(sK0) = k5_relat_1(k2_funct_1(sK2),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2) ),
    inference(superposition,[],[f187,f8230])).

fof(f8230,plain,(
    sK0 = k2_relset_1(sK0,sK0,sK2) ),
    inference(subsumption_resolution,[],[f8229,f120])).

fof(f8229,plain,
    ( sK0 = k2_relset_1(sK0,sK0,sK2)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f8228,f121])).

fof(f8228,plain,
    ( sK0 = k2_relset_1(sK0,sK0,sK2)
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f8227,f123])).

fof(f8227,plain,
    ( sK0 = k2_relset_1(sK0,sK0,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f8226,f116])).

fof(f116,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f103])).

fof(f8226,plain,
    ( sK0 = k2_relset_1(sK0,sK0,sK2)
    | ~ v1_funct_1(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f8225,f117])).

fof(f117,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f103])).

fof(f8225,plain,
    ( sK0 = k2_relset_1(sK0,sK0,sK2)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f8208,f119])).

fof(f119,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f103])).

fof(f8208,plain,
    ( sK0 = k2_relset_1(sK0,sK0,sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f124,f188])).

fof(f188,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | k2_relset_1(X0,X1,X2) = X1
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f85])).

fof(f85,plain,(
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
    inference(flattening,[],[f84])).

fof(f84,plain,(
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
    inference(ennf_transformation,[],[f36])).

fof(f36,axiom,(
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

fof(f124,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f103])).

fof(f187,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f83])).

fof(f83,plain,(
    ! [X0,X1,X2] :
      ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f82])).

fof(f82,plain,(
    ! [X0,X1,X2] :
      ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f39])).

fof(f39,axiom,(
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

fof(f8224,plain,(
    spl7_272 ),
    inference(avatar_contradiction_clause,[],[f8223])).

fof(f8223,plain,
    ( $false
    | spl7_272 ),
    inference(subsumption_resolution,[],[f8222,f120])).

fof(f8222,plain,
    ( ~ v1_funct_1(sK2)
    | spl7_272 ),
    inference(subsumption_resolution,[],[f8221,f121])).

fof(f8221,plain,
    ( ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2)
    | spl7_272 ),
    inference(subsumption_resolution,[],[f8220,f123])).

fof(f8220,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2)
    | spl7_272 ),
    inference(subsumption_resolution,[],[f8219,f116])).

fof(f8219,plain,
    ( ~ v1_funct_1(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2)
    | spl7_272 ),
    inference(subsumption_resolution,[],[f8218,f117])).

fof(f8218,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2)
    | spl7_272 ),
    inference(subsumption_resolution,[],[f8217,f119])).

fof(f8217,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2)
    | spl7_272 ),
    inference(subsumption_resolution,[],[f8208,f7006])).

fof(f7006,plain,
    ( sK0 != k2_relset_1(sK0,sK0,sK2)
    | spl7_272 ),
    inference(avatar_component_clause,[],[f7005])).

fof(f8172,plain,
    ( ~ spl7_8
    | ~ spl7_10
    | spl7_151
    | ~ spl7_272 ),
    inference(avatar_contradiction_clause,[],[f8171])).

fof(f8171,plain,
    ( $false
    | ~ spl7_8
    | ~ spl7_10
    | spl7_151
    | ~ spl7_272 ),
    inference(subsumption_resolution,[],[f7909,f8167])).

fof(f8167,plain,
    ( sK0 != k2_relat_1(k6_relat_1(sK0))
    | spl7_151 ),
    inference(subsumption_resolution,[],[f8166,f127])).

fof(f127,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

fof(f8166,plain,
    ( sK0 != k2_relat_1(k6_relat_1(sK0))
    | ~ m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl7_151 ),
    inference(superposition,[],[f3847,f174])).

fof(f3847,plain,
    ( sK0 != k2_relset_1(sK0,sK0,k6_relat_1(sK0))
    | spl7_151 ),
    inference(avatar_component_clause,[],[f3845])).

fof(f3845,plain,
    ( spl7_151
  <=> sK0 = k2_relset_1(sK0,sK0,k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_151])])).

% (13599)dis+11_10_av=off:lma=on:nm=64:nwc=5:sp=reverse_arity_3 on theBenchmark
fof(f7909,plain,
    ( sK0 = k2_relat_1(k6_relat_1(sK0))
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_272 ),
    inference(forward_demodulation,[],[f312,f7877])).

fof(f312,plain,
    ( k2_relat_1(sK2) = k2_relat_1(k6_relat_1(k2_relat_1(sK2)))
    | ~ spl7_8
    | ~ spl7_10 ),
    inference(backward_demodulation,[],[f275,f287])).

fof(f275,plain,
    ( k2_relat_1(sK2) = k2_relat_1(k5_relat_1(k2_funct_1(sK2),sK2))
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f273])).

fof(f273,plain,
    ( spl7_8
  <=> k2_relat_1(sK2) = k2_relat_1(k5_relat_1(k2_funct_1(sK2),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f8106,plain,
    ( spl7_349
    | ~ spl7_151
    | spl7_30
    | ~ spl7_341 ),
    inference(avatar_split_clause,[],[f8105,f7665,f604,f3845,f8060])).

fof(f8060,plain,
    ( spl7_349
  <=> sK0 = k2_relset_1(sK0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_349])])).

fof(f7665,plain,
    ( spl7_341
  <=> k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k6_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_341])])).

fof(f8105,plain,
    ( sK0 != k2_relset_1(sK0,sK0,k6_relat_1(sK0))
    | sK0 = k2_relset_1(sK0,sK0,sK1)
    | spl7_30
    | ~ spl7_341 ),
    inference(subsumption_resolution,[],[f8104,f116])).

fof(f8104,plain,
    ( sK0 != k2_relset_1(sK0,sK0,k6_relat_1(sK0))
    | sK0 = k2_relset_1(sK0,sK0,sK1)
    | ~ v1_funct_1(sK1)
    | spl7_30
    | ~ spl7_341 ),
    inference(subsumption_resolution,[],[f8103,f117])).

fof(f8103,plain,
    ( sK0 != k2_relset_1(sK0,sK0,k6_relat_1(sK0))
    | sK0 = k2_relset_1(sK0,sK0,sK1)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | spl7_30
    | ~ spl7_341 ),
    inference(subsumption_resolution,[],[f8102,f119])).

fof(f8102,plain,
    ( sK0 != k2_relset_1(sK0,sK0,k6_relat_1(sK0))
    | sK0 = k2_relset_1(sK0,sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | spl7_30
    | ~ spl7_341 ),
    inference(subsumption_resolution,[],[f8101,f120])).

fof(f8101,plain,
    ( sK0 != k2_relset_1(sK0,sK0,k6_relat_1(sK0))
    | sK0 = k2_relset_1(sK0,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | spl7_30
    | ~ spl7_341 ),
    inference(subsumption_resolution,[],[f8100,f121])).

fof(f8100,plain,
    ( sK0 != k2_relset_1(sK0,sK0,k6_relat_1(sK0))
    | sK0 = k2_relset_1(sK0,sK0,sK1)
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | spl7_30
    | ~ spl7_341 ),
    inference(subsumption_resolution,[],[f8099,f123])).

fof(f8099,plain,
    ( sK0 != k2_relset_1(sK0,sK0,k6_relat_1(sK0))
    | sK0 = k2_relset_1(sK0,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | spl7_30
    | ~ spl7_341 ),
    inference(subsumption_resolution,[],[f8098,f222])).

fof(f8098,plain,
    ( sK0 != k2_relset_1(sK0,sK0,k6_relat_1(sK0))
    | ~ v2_funct_1(sK2)
    | sK0 = k2_relset_1(sK0,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | spl7_30
    | ~ spl7_341 ),
    inference(subsumption_resolution,[],[f8048,f605])).

fof(f8048,plain,
    ( sK0 != k2_relset_1(sK0,sK0,k6_relat_1(sK0))
    | k1_xboole_0 = sK0
    | ~ v2_funct_1(sK2)
    | sK0 = k2_relset_1(sK0,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ spl7_341 ),
    inference(superposition,[],[f194,f7667])).

fof(f7667,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k6_relat_1(sK0)
    | ~ spl7_341 ),
    inference(avatar_component_clause,[],[f7665])).

fof(f194,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) != X2
      | k1_xboole_0 = X2
      | ~ v2_funct_1(X4)
      | k2_relset_1(X0,X1,X3) = X1
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X4,X1,X2)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f94])).

fof(f94,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k2_relset_1(X0,X1,X3) = X1
          | k1_xboole_0 = X2
          | ~ v2_funct_1(X4)
          | k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) != X2
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f93])).

fof(f93,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k2_relset_1(X0,X1,X3) = X1
          | k1_xboole_0 = X2
          | ~ v2_funct_1(X4)
          | k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) != X2
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f37])).

fof(f37,axiom,(
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

fof(f8097,plain,(
    ~ spl7_350 ),
    inference(avatar_contradiction_clause,[],[f8096])).

fof(f8096,plain,
    ( $false
    | ~ spl7_350 ),
    inference(subsumption_resolution,[],[f8095,f123])).

fof(f8095,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl7_350 ),
    inference(resolution,[],[f8091,f208])).

fof(f208,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(duplicate_literal_removal,[],[f207])).

fof(f207,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f196])).

fof(f196,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f115])).

fof(f115,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f96])).

fof(f96,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f95])).

fof(f95,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f8091,plain,
    ( ~ r2_relset_1(sK0,sK0,sK2,sK2)
    | ~ spl7_350 ),
    inference(backward_demodulation,[],[f7392,f8066])).

fof(f8066,plain,
    ( sK2 = k2_funct_1(sK1)
    | ~ spl7_350 ),
    inference(avatar_component_clause,[],[f8064])).

fof(f8064,plain,
    ( spl7_350
  <=> sK2 = k2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_350])])).

fof(f7392,plain,(
    ~ r2_relset_1(sK0,sK0,sK2,k2_funct_1(sK1)) ),
    inference(forward_demodulation,[],[f125,f7070])).

fof(f7070,plain,(
    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(global_subsumption,[],[f119,f7069])).

fof(f7069,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f7068,f116])).

fof(f7068,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f7058,f117])).

fof(f7058,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(resolution,[],[f118,f160])).

fof(f160,plain,(
    ! [X0,X1] :
      ( ~ v3_funct_2(X1,X0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f35])).

fof(f35,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_2(X0,X1) = k2_funct_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

fof(f118,plain,(
    v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f103])).

fof(f125,plain,(
    ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f103])).

fof(f8067,plain,
    ( ~ spl7_349
    | spl7_350
    | spl7_30
    | ~ spl7_154
    | ~ spl7_341
    | ~ spl7_347 ),
    inference(avatar_split_clause,[],[f8058,f7947,f7665,f3912,f604,f8064,f8060])).

fof(f7947,plain,
    ( spl7_347
  <=> r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_347])])).

fof(f8058,plain,
    ( sK2 = k2_funct_1(sK1)
    | sK0 != k2_relset_1(sK0,sK0,sK1)
    | spl7_30
    | ~ spl7_154
    | ~ spl7_341
    | ~ spl7_347 ),
    inference(subsumption_resolution,[],[f8057,f7948])).

fof(f7948,plain,
    ( r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0))
    | ~ spl7_347 ),
    inference(avatar_component_clause,[],[f7947])).

fof(f8057,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0))
    | sK2 = k2_funct_1(sK1)
    | sK0 != k2_relset_1(sK0,sK0,sK1)
    | spl7_30
    | ~ spl7_154
    | ~ spl7_341 ),
    inference(forward_demodulation,[],[f8056,f3914])).

fof(f3914,plain,
    ( k6_partfun1(sK0) = k6_relat_1(sK0)
    | ~ spl7_154 ),
    inference(avatar_component_clause,[],[f3912])).

fof(f8056,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_partfun1(sK0))
    | sK2 = k2_funct_1(sK1)
    | sK0 != k2_relset_1(sK0,sK0,sK1)
    | spl7_30
    | ~ spl7_341 ),
    inference(subsumption_resolution,[],[f8055,f120])).

fof(f8055,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_partfun1(sK0))
    | sK2 = k2_funct_1(sK1)
    | sK0 != k2_relset_1(sK0,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl7_30
    | ~ spl7_341 ),
    inference(subsumption_resolution,[],[f8054,f116])).

fof(f8054,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_partfun1(sK0))
    | sK2 = k2_funct_1(sK1)
    | sK0 != k2_relset_1(sK0,sK0,sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_funct_1(sK2)
    | spl7_30
    | ~ spl7_341 ),
    inference(subsumption_resolution,[],[f8053,f119])).

fof(f8053,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_partfun1(sK0))
    | sK2 = k2_funct_1(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | sK0 != k2_relset_1(sK0,sK0,sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_funct_1(sK2)
    | spl7_30
    | ~ spl7_341 ),
    inference(subsumption_resolution,[],[f8052,f117])).

fof(f8052,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_partfun1(sK0))
    | sK2 = k2_funct_1(sK1)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | sK0 != k2_relset_1(sK0,sK0,sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_funct_1(sK2)
    | spl7_30
    | ~ spl7_341 ),
    inference(subsumption_resolution,[],[f8051,f605])).

fof(f8051,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_partfun1(sK0))
    | sK2 = k2_funct_1(sK1)
    | k1_xboole_0 = sK0
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | sK0 != k2_relset_1(sK0,sK0,sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl7_341 ),
    inference(subsumption_resolution,[],[f8050,f121])).

fof(f8050,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_partfun1(sK0))
    | sK2 = k2_funct_1(sK1)
    | ~ v1_funct_2(sK2,sK0,sK0)
    | k1_xboole_0 = sK0
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | sK0 != k2_relset_1(sK0,sK0,sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl7_341 ),
    inference(subsumption_resolution,[],[f8049,f123])).

fof(f8049,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_partfun1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | sK2 = k2_funct_1(sK1)
    | ~ v1_funct_2(sK2,sK0,sK0)
    | k1_xboole_0 = sK0
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | sK0 != k2_relset_1(sK0,sK0,sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl7_341 ),
    inference(duplicate_literal_removal,[],[f8045])).

fof(f8045,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_partfun1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | sK2 = k2_funct_1(sK1)
    | ~ v1_funct_2(sK2,sK0,sK0)
    | k1_xboole_0 = sK0
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | sK0 != k2_relset_1(sK0,sK0,sK1)
    | ~ v1_funct_1(sK1)
    | k1_xboole_0 = sK0
    | ~ v1_funct_1(sK2)
    | ~ spl7_341 ),
    inference(superposition,[],[f209,f7667])).

fof(f209,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_funct_1(X2) = X3
      | ~ v1_funct_2(X3,X1,X0)
      | k1_xboole_0 = X1
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v1_funct_1(X2)
      | k1_xboole_0 = X0
      | ~ v1_funct_1(X3) ) ),
    inference(global_subsumption,[],[f189,f191])).

fof(f191,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_funct_1(X2) = X3
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ v2_funct_1(X2)
      | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f89])).

fof(f89,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_funct_1(X2) = X3
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0
          | ~ v2_funct_1(X2)
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          | k2_relset_1(X0,X1,X2) != X1
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f88])).

fof(f88,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_funct_1(X2) = X3
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0
          | ~ v2_funct_1(X2)
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          | k2_relset_1(X0,X1,X2) != X1
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f40])).

fof(f40,axiom,(
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

fof(f189,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
      | v2_funct_1(X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f87])).

fof(f87,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( v2_funct_2(X3,X0)
            & v2_funct_1(X2) )
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f86])).

fof(f86,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( v2_funct_2(X3,X0)
            & v2_funct_1(X2) )
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f38])).

fof(f38,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
           => ( v2_funct_2(X3,X0)
              & v2_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_funct_2)).

fof(f8027,plain,(
    spl7_340 ),
    inference(avatar_contradiction_clause,[],[f8026])).

fof(f8026,plain,
    ( $false
    | spl7_340 ),
    inference(subsumption_resolution,[],[f8025,f116])).

fof(f8025,plain,
    ( ~ v1_funct_1(sK1)
    | spl7_340 ),
    inference(subsumption_resolution,[],[f8024,f119])).

fof(f8024,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | spl7_340 ),
    inference(subsumption_resolution,[],[f8023,f120])).

fof(f8023,plain,
    ( ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | spl7_340 ),
    inference(subsumption_resolution,[],[f8020,f123])).

fof(f8020,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | spl7_340 ),
    inference(resolution,[],[f7663,f199])).

fof(f199,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f100])).

fof(f100,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f99])).

fof(f99,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f7663,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl7_340 ),
    inference(avatar_component_clause,[],[f7661])).

fof(f7661,plain,
    ( spl7_340
  <=> m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_340])])).

fof(f7953,plain,(
    spl7_347 ),
    inference(avatar_contradiction_clause,[],[f7952])).

fof(f7952,plain,
    ( $false
    | spl7_347 ),
    inference(subsumption_resolution,[],[f7951,f127])).

fof(f7951,plain,
    ( ~ m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl7_347 ),
    inference(resolution,[],[f7949,f208])).

fof(f7949,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0))
    | spl7_347 ),
    inference(avatar_component_clause,[],[f7947])).

fof(f7668,plain,
    ( ~ spl7_340
    | spl7_341
    | ~ spl7_154 ),
    inference(avatar_split_clause,[],[f7659,f3912,f7665,f7661])).

fof(f7659,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k6_relat_1(sK0)
    | ~ m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl7_154 ),
    inference(subsumption_resolution,[],[f7658,f127])).

fof(f7658,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k6_relat_1(sK0)
    | ~ m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl7_154 ),
    inference(resolution,[],[f7475,f195])).

fof(f195,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f115])).

fof(f7475,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_relat_1(sK0))
    | ~ spl7_154 ),
    inference(forward_demodulation,[],[f124,f3914])).

fof(f7035,plain,
    ( spl7_22
    | spl7_23 ),
    inference(avatar_split_clause,[],[f7033,f418,f414])).

fof(f414,plain,
    ( spl7_22
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f418,plain,
    ( spl7_23
  <=> ! [X1] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
        | ~ v1_xboole_0(X1)
        | k1_xboole_0 = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).

fof(f7033,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
      | k1_xboole_0 = sK1
      | k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f116,f403])).

fof(f403,plain,(
    ! [X2,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | ~ v1_xboole_0(X1) ) ),
    inference(condensation,[],[f402])).

fof(f402,plain,(
    ! [X2,X3,X1] :
      ( k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
      | k1_xboole_0 = X2
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
      | ~ v1_xboole_0(X1) ) ),
    inference(resolution,[],[f386,f150])).

fof(f150,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_partfun1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_partfun1)).

fof(f386,plain,(
    ! [X2,X1] :
      ( ~ v1_partfun1(X1,X2)
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,k1_xboole_0)))
      | k1_xboole_0 = X1
      | ~ v1_funct_1(X1) ) ),
    inference(duplicate_literal_removal,[],[f385])).

fof(f385,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,k1_xboole_0)))
      | ~ v1_partfun1(X1,X2)
      | ~ v1_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,k1_xboole_0))) ) ),
    inference(resolution,[],[f204,f182])).

fof(f182,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f79,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f78])).

fof(f78,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v1_partfun1(X2,X0)
          & v1_funct_1(X2) )
       => ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_2)).

fof(f204,plain,(
    ! [X2,X0] :
      ( ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f179])).

fof(f179,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f114])).

fof(f114,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f77])).

fof(f77,plain,(
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
    inference(flattening,[],[f76])).

fof(f76,plain,(
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
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
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

fof(f6442,plain,
    ( ~ spl7_20
    | spl7_24
    | ~ spl7_25
    | ~ spl7_28
    | ~ spl7_196 ),
    inference(avatar_contradiction_clause,[],[f6441])).

fof(f6441,plain,
    ( $false
    | ~ spl7_20
    | spl7_24
    | ~ spl7_25
    | ~ spl7_28
    | ~ spl7_196 ),
    inference(subsumption_resolution,[],[f6431,f423])).

fof(f423,plain,
    ( k1_xboole_0 != sK2
    | spl7_24 ),
    inference(avatar_component_clause,[],[f422])).

fof(f422,plain,
    ( spl7_24
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).

fof(f6431,plain,
    ( k1_xboole_0 = sK2
    | ~ spl7_20
    | ~ spl7_25
    | ~ spl7_28
    | ~ spl7_196 ),
    inference(resolution,[],[f6426,f5358])).

fof(f5358,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl7_196 ),
    inference(avatar_component_clause,[],[f5357])).

fof(f5357,plain,
    ( spl7_196
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_196])])).

fof(f6426,plain,
    ( ! [X14,X13] :
        ( ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X14,k1_xboole_0)))
        | k1_xboole_0 = X13 )
    | ~ spl7_20
    | ~ spl7_25
    | ~ spl7_28
    | ~ spl7_196 ),
    inference(resolution,[],[f6230,f494])).

fof(f494,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl7_28 ),
    inference(avatar_component_clause,[],[f493])).

fof(f493,plain,
    ( spl7_28
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).

fof(f6230,plain,
    ( ! [X4,X2,X3] :
        ( ~ v1_xboole_0(X4)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
        | k1_xboole_0 = X2 )
    | ~ spl7_20
    | ~ spl7_25
    | ~ spl7_196 ),
    inference(resolution,[],[f6055,f149])).

fof(f149,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

fof(f6055,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = X0 )
    | ~ spl7_20
    | ~ spl7_25
    | ~ spl7_196 ),
    inference(subsumption_resolution,[],[f6054,f381])).

fof(f381,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl7_20 ),
    inference(backward_demodulation,[],[f335,f374])).

fof(f374,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl7_20 ),
    inference(avatar_component_clause,[],[f372])).

fof(f372,plain,
    ( spl7_20
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f335,plain,(
    ! [X0] : r1_tarski(k1_relat_1(k1_xboole_0),X0) ),
    inference(subsumption_resolution,[],[f334,f143])).

fof(f143,plain,(
    ! [X0] : v1_relat_1(sK3(X0)) ),
    inference(cnf_transformation,[],[f105])).

fof(f105,plain,(
    ! [X0] :
      ( ! [X2] :
          ( np__1 = k1_funct_1(sK3(X0),X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(sK3(X0)) = X0
      & v1_funct_1(sK3(X0))
      & v1_relat_1(sK3(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f58,f104])).

fof(f104,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( k1_funct_1(X1,X2) = np__1
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( ! [X2] :
            ( np__1 = k1_funct_1(sK3(X0),X2)
            | ~ r2_hidden(X2,X0) )
        & k1_relat_1(sK3(X0)) = X0
        & v1_funct_1(sK3(X0))
        & v1_relat_1(sK3(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( k1_funct_1(X1,X2) = np__1
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => k1_funct_1(X1,X2) = np__1 )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e7_25__funct_1)).

fof(f334,plain,(
    ! [X0] :
      ( r1_tarski(k1_relat_1(k1_xboole_0),X0)
      | ~ v1_relat_1(sK3(X0)) ) ),
    inference(subsumption_resolution,[],[f331,f144])).

fof(f144,plain,(
    ! [X0] : v1_funct_1(sK3(X0)) ),
    inference(cnf_transformation,[],[f105])).

fof(f331,plain,(
    ! [X0] :
      ( r1_tarski(k1_relat_1(k1_xboole_0),X0)
      | ~ v1_funct_1(sK3(X0))
      | ~ v1_relat_1(sK3(X0)) ) ),
    inference(superposition,[],[f330,f145])).

fof(f145,plain,(
    ! [X0] : k1_relat_1(sK3(X0)) = X0 ),
    inference(cnf_transformation,[],[f105])).

fof(f330,plain,(
    ! [X0] :
      ( r1_tarski(k1_relat_1(k1_xboole_0),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f329,f128])).

fof(f128,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( v5_ordinal1(k1_xboole_0)
      & v1_funct_1(k1_xboole_0)
      & v5_relat_1(k1_xboole_0,X0)
      & v1_relat_1(k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_ordinal1)).

fof(f329,plain,(
    ! [X0] :
      ( r1_tarski(k1_relat_1(k1_xboole_0),k1_relat_1(X0))
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f328,f130])).

fof(f130,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f20])).

fof(f328,plain,(
    ! [X0] :
      ( r1_tarski(k1_relat_1(k1_xboole_0),k1_relat_1(X0))
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f327])).

fof(f327,plain,(
    ! [X0] :
      ( r1_tarski(k1_relat_1(k1_xboole_0),k1_relat_1(X0))
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f142,f136])).

fof(f136,plain,(
    ! [X0] :
      ( v5_funct_1(k1_xboole_0,X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( v5_funct_1(k1_xboole_0,X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( v5_funct_1(k1_xboole_0,X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => v5_funct_1(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_funct_1)).

fof(f142,plain,(
    ! [X0,X1] :
      ( ~ v5_funct_1(X1,X0)
      | r1_tarski(k1_relat_1(X1),k1_relat_1(X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(X1),k1_relat_1(X0))
          | ~ v5_funct_1(X1,X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(X1),k1_relat_1(X0))
          | ~ v5_funct_1(X1,X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v5_funct_1(X1,X0)
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
         => r1_tarski(k1_relat_1(X1),k1_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_funct_1)).

fof(f6054,plain,
    ( ! [X0] :
        ( k1_xboole_0 = X0
        | ~ r1_tarski(k1_xboole_0,X0)
        | ~ v1_xboole_0(X0) )
    | ~ spl7_20
    | ~ spl7_25
    | ~ spl7_196 ),
    inference(subsumption_resolution,[],[f6053,f381])).

fof(f6053,plain,
    ( ! [X0] :
        ( k1_xboole_0 = X0
        | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
        | ~ r1_tarski(k1_xboole_0,X0)
        | ~ v1_xboole_0(X0) )
    | ~ spl7_25
    | ~ spl7_196 ),
    inference(resolution,[],[f5358,f5621])).

fof(f5621,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        | k1_xboole_0 = X0
        | ~ r1_tarski(X1,k1_xboole_0)
        | ~ r1_tarski(X2,X0)
        | ~ v1_xboole_0(X0) )
    | ~ spl7_25 ),
    inference(resolution,[],[f427,f197])).

fof(f197,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(cnf_transformation,[],[f98])).

fof(f98,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(flattening,[],[f97])).

fof(f97,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => ( ( r1_tarski(X2,X3)
          & r1_tarski(X0,X1) )
       => m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_relset_1)).

fof(f427,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,k1_xboole_0)))
        | ~ v1_xboole_0(X2)
        | k1_xboole_0 = X2 )
    | ~ spl7_25 ),
    inference(avatar_component_clause,[],[f426])).

fof(f426,plain,
    ( spl7_25
  <=> ! [X2] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,k1_xboole_0)))
        | ~ v1_xboole_0(X2)
        | k1_xboole_0 = X2 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).

fof(f5574,plain,
    ( ~ spl7_30
    | spl7_196 ),
    inference(avatar_contradiction_clause,[],[f5573])).

fof(f5573,plain,
    ( $false
    | ~ spl7_30
    | spl7_196 ),
    inference(subsumption_resolution,[],[f5359,f3943])).

fof(f3943,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl7_30 ),
    inference(backward_demodulation,[],[f123,f606])).

fof(f606,plain,
    ( k1_xboole_0 = sK0
    | ~ spl7_30 ),
    inference(avatar_component_clause,[],[f604])).

fof(f5359,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | spl7_196 ),
    inference(avatar_component_clause,[],[f5357])).

fof(f5381,plain,
    ( ~ spl7_7
    | spl7_10 ),
    inference(avatar_split_clause,[],[f5380,f285,f269])).

fof(f269,plain,
    ( spl7_7
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f5380,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f5373,f120])).

fof(f5373,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f222,f139])).

fof(f139,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

fof(f5377,plain,
    ( ~ spl7_7
    | spl7_8 ),
    inference(avatar_split_clause,[],[f5376,f273,f269])).

fof(f5376,plain,
    ( k2_relat_1(sK2) = k2_relat_1(k5_relat_1(k2_funct_1(sK2),sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f5371,f120])).

fof(f5371,plain,
    ( k2_relat_1(sK2) = k2_relat_1(k5_relat_1(k2_funct_1(sK2),sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f222,f141])).

fof(f141,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
        & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
        & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
          & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_funct_1)).

fof(f5370,plain,
    ( spl7_24
    | spl7_25 ),
    inference(avatar_split_clause,[],[f5368,f426,f422])).

fof(f5368,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
      | k1_xboole_0 = sK2
      | k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f120,f403])).

fof(f5343,plain,
    ( ~ spl7_20
    | ~ spl7_22
    | ~ spl7_28
    | spl7_168
    | ~ spl7_190 ),
    inference(avatar_contradiction_clause,[],[f5342])).

fof(f5342,plain,
    ( $false
    | ~ spl7_20
    | ~ spl7_22
    | ~ spl7_28
    | spl7_168
    | ~ spl7_190 ),
    inference(subsumption_resolution,[],[f5335,f4252])).

fof(f4252,plain,
    ( k1_xboole_0 != k2_funct_1(k1_xboole_0)
    | spl7_168 ),
    inference(avatar_component_clause,[],[f4251])).

fof(f4251,plain,
    ( spl7_168
  <=> k1_xboole_0 = k2_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_168])])).

fof(f5335,plain,
    ( k1_xboole_0 = k2_funct_1(k1_xboole_0)
    | ~ spl7_20
    | ~ spl7_22
    | ~ spl7_28
    | spl7_168
    | ~ spl7_190 ),
    inference(resolution,[],[f5330,f4604])).

fof(f4604,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl7_190 ),
    inference(avatar_component_clause,[],[f4603])).

fof(f4603,plain,
    ( spl7_190
  <=> m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_190])])).

fof(f5330,plain,
    ( ! [X14,X13] :
        ( ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X14,k1_xboole_0)))
        | k1_xboole_0 = X13 )
    | ~ spl7_20
    | ~ spl7_22
    | ~ spl7_28
    | spl7_168
    | ~ spl7_190 ),
    inference(resolution,[],[f5296,f494])).

fof(f5296,plain,
    ( ! [X4,X2,X3] :
        ( ~ v1_xboole_0(X4)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
        | k1_xboole_0 = X2 )
    | ~ spl7_20
    | ~ spl7_22
    | spl7_168
    | ~ spl7_190 ),
    inference(resolution,[],[f5294,f149])).

fof(f5294,plain,
    ( ! [X5] :
        ( ~ v1_xboole_0(X5)
        | k1_xboole_0 = X5 )
    | ~ spl7_20
    | ~ spl7_22
    | spl7_168
    | ~ spl7_190 ),
    inference(subsumption_resolution,[],[f5293,f381])).

fof(f5293,plain,
    ( ! [X5] :
        ( ~ v1_xboole_0(X5)
        | ~ r1_tarski(k1_xboole_0,X5)
        | k1_xboole_0 = X5 )
    | ~ spl7_20
    | ~ spl7_22
    | spl7_168
    | ~ spl7_190 ),
    inference(subsumption_resolution,[],[f5291,f381])).

fof(f5291,plain,
    ( ! [X5] :
        ( ~ v1_xboole_0(X5)
        | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
        | ~ r1_tarski(k1_xboole_0,X5)
        | k1_xboole_0 = X5 )
    | ~ spl7_22
    | spl7_168
    | ~ spl7_190 ),
    inference(resolution,[],[f5286,f4604])).

fof(f5286,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        | ~ v1_xboole_0(X0)
        | ~ r1_tarski(X1,k1_xboole_0)
        | ~ r1_tarski(X2,X0)
        | k1_xboole_0 = X0 )
    | ~ spl7_22
    | spl7_168 ),
    inference(resolution,[],[f5217,f197])).

fof(f5217,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
        | k1_xboole_0 = X1
        | ~ v1_xboole_0(X1) )
    | ~ spl7_22
    | spl7_168 ),
    inference(subsumption_resolution,[],[f5211,f4252])).

fof(f5211,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
        | k1_xboole_0 = k2_funct_1(k1_xboole_0)
        | k1_xboole_0 = X1
        | ~ v1_xboole_0(X1) )
    | ~ spl7_22 ),
    inference(resolution,[],[f403,f3260])).

fof(f3260,plain,
    ( v1_funct_1(k2_funct_1(k1_xboole_0))
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f3259,f130])).

fof(f3259,plain,
    ( v1_funct_1(k2_funct_1(k1_xboole_0))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f3258,f1471])).

fof(f1471,plain,
    ( v1_funct_2(k1_xboole_0,sK0,sK0)
    | ~ spl7_22 ),
    inference(backward_demodulation,[],[f117,f416])).

fof(f416,plain,
    ( k1_xboole_0 = sK1
    | ~ spl7_22 ),
    inference(avatar_component_clause,[],[f414])).

fof(f3258,plain,
    ( v1_funct_1(k2_funct_1(k1_xboole_0))
    | ~ v1_funct_2(k1_xboole_0,sK0,sK0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f3257,f1472])).

fof(f1472,plain,
    ( v3_funct_2(k1_xboole_0,sK0,sK0)
    | ~ spl7_22 ),
    inference(backward_demodulation,[],[f118,f416])).

fof(f3257,plain,
    ( v1_funct_1(k2_funct_1(k1_xboole_0))
    | ~ v3_funct_2(k1_xboole_0,sK0,sK0)
    | ~ v1_funct_2(k1_xboole_0,sK0,sK0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f3256,f126])).

fof(f126,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f3256,plain,
    ( v1_funct_1(k2_funct_1(k1_xboole_0))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v3_funct_2(k1_xboole_0,sK0,sK0)
    | ~ v1_funct_2(k1_xboole_0,sK0,sK0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ spl7_22 ),
    inference(superposition,[],[f161,f2573])).

fof(f2573,plain,
    ( k2_funct_2(sK0,k1_xboole_0) = k2_funct_1(k1_xboole_0)
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f2572,f130])).

fof(f2572,plain,
    ( k2_funct_2(sK0,k1_xboole_0) = k2_funct_1(k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f2571,f1471])).

fof(f2571,plain,
    ( k2_funct_2(sK0,k1_xboole_0) = k2_funct_1(k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,sK0,sK0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f2561,f126])).

fof(f2561,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k2_funct_2(sK0,k1_xboole_0) = k2_funct_1(k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,sK0,sK0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ spl7_22 ),
    inference(resolution,[],[f1472,f160])).

fof(f161,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k2_funct_2(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_2)).

fof(f4705,plain,
    ( ~ spl7_22
    | ~ spl7_30
    | spl7_190 ),
    inference(avatar_contradiction_clause,[],[f4704])).

fof(f4704,plain,
    ( $false
    | ~ spl7_22
    | ~ spl7_30
    | spl7_190 ),
    inference(subsumption_resolution,[],[f3972,f4605])).

fof(f4605,plain,
    ( ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | spl7_190 ),
    inference(avatar_component_clause,[],[f4603])).

fof(f3972,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl7_22
    | ~ spl7_30 ),
    inference(backward_demodulation,[],[f3358,f606])).

fof(f3358,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl7_22 ),
    inference(forward_demodulation,[],[f2564,f2573])).

fof(f2564,plain,
    ( m1_subset_1(k2_funct_2(sK0,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f2563,f130])).

fof(f2563,plain,
    ( m1_subset_1(k2_funct_2(sK0,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f2562,f1471])).

fof(f2562,plain,
    ( m1_subset_1(k2_funct_2(sK0,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(k1_xboole_0,sK0,sK0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f2558,f126])).

fof(f2558,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | m1_subset_1(k2_funct_2(sK0,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(k1_xboole_0,sK0,sK0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ spl7_22 ),
    inference(resolution,[],[f1472,f164])).

fof(f164,plain,(
    ! [X0,X1] :
      ( ~ v3_funct_2(X1,X0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f4474,plain,
    ( ~ spl7_22
    | ~ spl7_24
    | ~ spl7_30
    | ~ spl7_168 ),
    inference(avatar_contradiction_clause,[],[f4473])).

fof(f4473,plain,
    ( $false
    | ~ spl7_22
    | ~ spl7_24
    | ~ spl7_30
    | ~ spl7_168 ),
    inference(subsumption_resolution,[],[f4472,f126])).

fof(f4472,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl7_22
    | ~ spl7_24
    | ~ spl7_30
    | ~ spl7_168 ),
    inference(resolution,[],[f4283,f208])).

fof(f4283,plain,
    ( ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl7_22
    | ~ spl7_24
    | ~ spl7_30
    | ~ spl7_168 ),
    inference(forward_demodulation,[],[f4282,f424])).

fof(f424,plain,
    ( k1_xboole_0 = sK2
    | ~ spl7_24 ),
    inference(avatar_component_clause,[],[f422])).

fof(f4282,plain,
    ( ~ r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,k1_xboole_0)
    | ~ spl7_22
    | ~ spl7_30
    | ~ spl7_168 ),
    inference(forward_demodulation,[],[f3968,f4253])).

fof(f4253,plain,
    ( k1_xboole_0 = k2_funct_1(k1_xboole_0)
    | ~ spl7_168 ),
    inference(avatar_component_clause,[],[f4251])).

fof(f3968,plain,
    ( ~ r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,k2_funct_1(k1_xboole_0))
    | ~ spl7_22
    | ~ spl7_30 ),
    inference(backward_demodulation,[],[f3254,f606])).

fof(f3254,plain,
    ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_1(k1_xboole_0))
    | ~ spl7_22 ),
    inference(backward_demodulation,[],[f2492,f2573])).

fof(f2492,plain,
    ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,k1_xboole_0))
    | ~ spl7_22 ),
    inference(forward_demodulation,[],[f125,f416])).

fof(f955,plain,(
    ~ spl7_21 ),
    inference(avatar_contradiction_clause,[],[f943])).

fof(f943,plain,
    ( $false
    | ~ spl7_21 ),
    inference(resolution,[],[f379,f127])).

fof(f379,plain,
    ( ! [X2,X1] : ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ spl7_21 ),
    inference(avatar_component_clause,[],[f378])).

fof(f378,plain,
    ( spl7_21
  <=> ! [X1,X2] : ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).

fof(f932,plain,
    ( spl7_20
    | spl7_21 ),
    inference(avatar_split_clause,[],[f931,f378,f372])).

fof(f931,plain,(
    ! [X6,X5] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(X6))
      | k1_xboole_0 = k1_relat_1(k1_xboole_0) ) ),
    inference(global_subsumption,[],[f929])).

fof(f929,plain,(
    ! [X4,X3] :
      ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X4)) ) ),
    inference(subsumption_resolution,[],[f924,f335])).

fof(f924,plain,(
    ! [X4,X3] :
      ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
      | ~ r1_tarski(k1_relat_1(k1_xboole_0),X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X4)) ) ),
    inference(resolution,[],[f335,f172])).

fof(f172,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,k3_subset_1(X0,X2))
      | k1_xboole_0 = X1
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X1
      | ~ r1_tarski(X1,k3_subset_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f72])).

fof(f72,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X1
      | ~ r1_tarski(X1,k3_subset_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => ( ( r1_tarski(X1,k3_subset_1(X0,X2))
          & r1_tarski(X1,X2) )
       => k1_xboole_0 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_subset_1)).

fof(f813,plain,
    ( ~ spl7_20
    | spl7_22
    | ~ spl7_23
    | ~ spl7_28
    | ~ spl7_33 ),
    inference(avatar_contradiction_clause,[],[f812])).

fof(f812,plain,
    ( $false
    | ~ spl7_20
    | spl7_22
    | ~ spl7_23
    | ~ spl7_28
    | ~ spl7_33 ),
    inference(subsumption_resolution,[],[f805,f415])).

fof(f415,plain,
    ( k1_xboole_0 != sK1
    | spl7_22 ),
    inference(avatar_component_clause,[],[f414])).

fof(f805,plain,
    ( k1_xboole_0 = sK1
    | ~ spl7_20
    | ~ spl7_23
    | ~ spl7_28
    | ~ spl7_33 ),
    inference(resolution,[],[f801,f666])).

fof(f666,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl7_33 ),
    inference(avatar_component_clause,[],[f665])).

fof(f665,plain,
    ( spl7_33
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_33])])).

fof(f801,plain,
    ( ! [X14,X13] :
        ( ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X14,k1_xboole_0)))
        | k1_xboole_0 = X13 )
    | ~ spl7_20
    | ~ spl7_23
    | ~ spl7_28
    | ~ spl7_33 ),
    inference(resolution,[],[f760,f494])).

fof(f760,plain,
    ( ! [X6,X4,X5] :
        ( ~ v1_xboole_0(X6)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
        | k1_xboole_0 = X4 )
    | ~ spl7_20
    | ~ spl7_23
    | ~ spl7_33 ),
    inference(resolution,[],[f750,f149])).

fof(f750,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = X0 )
    | ~ spl7_20
    | ~ spl7_23
    | ~ spl7_33 ),
    inference(subsumption_resolution,[],[f749,f381])).

fof(f749,plain,
    ( ! [X0] :
        ( k1_xboole_0 = X0
        | ~ r1_tarski(k1_xboole_0,X0)
        | ~ v1_xboole_0(X0) )
    | ~ spl7_20
    | ~ spl7_23
    | ~ spl7_33 ),
    inference(subsumption_resolution,[],[f747,f381])).

fof(f747,plain,
    ( ! [X0] :
        ( k1_xboole_0 = X0
        | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
        | ~ r1_tarski(k1_xboole_0,X0)
        | ~ v1_xboole_0(X0) )
    | ~ spl7_23
    | ~ spl7_33 ),
    inference(resolution,[],[f666,f702])).

fof(f702,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        | k1_xboole_0 = X0
        | ~ r1_tarski(X1,k1_xboole_0)
        | ~ r1_tarski(X2,X0)
        | ~ v1_xboole_0(X0) )
    | ~ spl7_23 ),
    inference(resolution,[],[f419,f197])).

fof(f419,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
        | ~ v1_xboole_0(X1)
        | k1_xboole_0 = X1 )
    | ~ spl7_23 ),
    inference(avatar_component_clause,[],[f418])).

fof(f676,plain,
    ( ~ spl7_30
    | spl7_33 ),
    inference(avatar_contradiction_clause,[],[f675])).

fof(f675,plain,
    ( $false
    | ~ spl7_30
    | spl7_33 ),
    inference(subsumption_resolution,[],[f667,f673])).

fof(f673,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl7_30 ),
    inference(forward_demodulation,[],[f119,f606])).

fof(f667,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | spl7_33 ),
    inference(avatar_component_clause,[],[f665])).

fof(f506,plain,(
    spl7_28 ),
    inference(avatar_contradiction_clause,[],[f505])).

fof(f505,plain,
    ( $false
    | spl7_28 ),
    inference(resolution,[],[f503,f168])).

fof(f168,plain,(
    ! [X0,X1] : v1_xboole_0(sK6(X0,X1)) ),
    inference(cnf_transformation,[],[f113])).

fof(f113,plain,(
    ! [X0,X1] :
      ( v5_relat_1(sK6(X0,X1),X1)
      & v4_relat_1(sK6(X0,X1),X0)
      & v1_relat_1(sK6(X0,X1))
      & v1_xboole_0(sK6(X0,X1))
      & m1_subset_1(sK6(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f34,f112])).

fof(f112,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( v5_relat_1(X2,X1)
          & v4_relat_1(X2,X0)
          & v1_relat_1(X2)
          & v1_xboole_0(X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( v5_relat_1(sK6(X0,X1),X1)
        & v4_relat_1(sK6(X0,X1),X0)
        & v1_relat_1(sK6(X0,X1))
        & v1_xboole_0(sK6(X0,X1))
        & m1_subset_1(sK6(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( v5_relat_1(X2,X1)
      & v4_relat_1(X2,X0)
      & v1_relat_1(X2)
      & v1_xboole_0(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_relset_1)).

fof(f503,plain,
    ( ! [X2] : ~ v1_xboole_0(X2)
    | spl7_28 ),
    inference(subsumption_resolution,[],[f501,f126])).

fof(f501,plain,
    ( ! [X2,X1] :
        ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ v1_xboole_0(X2) )
    | spl7_28 ),
    inference(resolution,[],[f495,f149])).

fof(f495,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl7_28 ),
    inference(avatar_component_clause,[],[f493])).

fof(f308,plain,(
    spl7_7 ),
    inference(avatar_contradiction_clause,[],[f306])).

fof(f306,plain,
    ( $false
    | spl7_7 ),
    inference(resolution,[],[f302,f123])).

fof(f302,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl7_7 ),
    inference(resolution,[],[f271,f173])).

fof(f173,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f271,plain,
    ( ~ v1_relat_1(sK2)
    | spl7_7 ),
    inference(avatar_component_clause,[],[f269])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.32  % Computer   : n017.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % WCLimit    : 600
% 0.13/0.32  % DateTime   : Tue Dec  1 17:34:46 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.20/0.46  % (13385)ott+1010_5:4_av=off:bd=off:fde=none:irw=on:lma=on:nm=32:nwc=2.5:sd=2:ss=axioms:st=3.0:urr=on_5 on theBenchmark
% 0.20/0.47  % (13395)lrs+1003_2_acc=on:afp=4000:afq=2.0:amm=sco:bd=off:ccuc=small_ones:fsr=off:fde=unused:gsp=input_only:nm=64:newcnf=on:nwc=2.5:nicw=on:stl=30:urr=ec_only_8 on theBenchmark
% 0.20/0.47  % (13393)dis-3_5_av=off:cond=on:gs=on:gsem=off:lcm=predicate:nm=0:nwc=1:sos=on:sp=reverse_arity_3 on theBenchmark
% 0.20/0.48  % (13401)dis+1010_4_afp=10000:afq=1.2:anc=none:irw=on:lma=on:nm=64:nwc=10:sas=z3:sac=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.48  % (13383)ott+11_2:1_add=large:afp=40000:afq=2.0:amm=sco:anc=none:br=off:cond=on:irw=on:nwc=1:sd=2:ss=axioms:st=2.0:sos=all:urr=on:updr=off_3 on theBenchmark
% 0.20/0.49  % (13408)dis+11_5_av=off:bd=off:bs=unit_only:bsr=on:cond=on:lcm=reverse:nm=0:nwc=1.2_5 on theBenchmark
% 0.20/0.49  % (13387)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.49  % (13389)ott+1002_2_av=off:bd=preordered:irw=on:lma=on:nm=64:nwc=10:sp=reverse_arity:updr=off_22 on theBenchmark
% 0.20/0.50  % (13406)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.20/0.50  % (13404)dis+11_28_av=off:fsr=off:irw=on:lcm=predicate:nm=2:newcnf=on:nwc=5:sp=occurrence:urr=on:updr=off_2 on theBenchmark
% 0.20/0.50  % (13398)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_4 on theBenchmark
% 0.20/0.50  % (13391)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.51  % (13412)lrs+10_6_aac=none:acc=model:add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bd=off:ccuc=small_ones:irw=on:lcm=reverse:nm=0:nwc=1:nicw=on:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (13384)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_2 on theBenchmark
% 0.20/0.51  % (13390)lrs+1_2:3_aac=none:afr=on:afp=100000:afq=1.0:amm=sco:bd=off:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off:uhcvi=on_16 on theBenchmark
% 0.20/0.51  % (13407)lrs+1011_4:1_av=off:fsr=off:irw=on:nwc=1:stl=30:sd=4:ss=axioms:st=1.5:sp=reverse_arity_12 on theBenchmark
% 0.20/0.51  % (13403)ott+1004_12_awrs=converge:awrsf=64:aac=none:afr=on:afp=4000:afq=1.4:amm=sco:anc=none:bs=on:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=on:lma=on:nwc=5:nicw=on:sas=z3:sos=all:sac=on:sp=occurrence:urr=ec_only_2 on theBenchmark
% 0.20/0.51  % (13394)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_5 on theBenchmark
% 0.20/0.51  % (13396)lrs+2_1_add=large:afp=100000:afq=1.0:amm=off:anc=none:bd=off:bs=unit_only:bsr=on:gsp=input_only:lma=on:lwlo=on:newcnf=on:nwc=1:stl=30:sos=theory:sp=reverse_arity:updr=off_14 on theBenchmark
% 0.20/0.52  % (13388)dis+1011_10_aac=none:add=large:afp=10000:afq=1.1:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=6:newcnf=on:nwc=2.5:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  % (13392)dis+11_4_afr=on:afp=1000:afq=1.4:amm=off:anc=none:lcm=reverse:lma=on:lwlo=on:nm=6:newcnf=on:nwc=1:sd=2:ss=axioms:st=2.0:sp=reverse_arity_2 on theBenchmark
% 0.20/0.52  % (13386)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_3 on theBenchmark
% 0.20/0.52  % (13405)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_72 on theBenchmark
% 0.20/0.52  % (13400)lrs+1002_3_aac=none:acc=on:add=off:afp=4000:afq=1.1:amm=sco:anc=none:cond=on:fsr=off:gs=on:irw=on:nm=32:newcnf=on:nwc=1.1:nicw=on:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=occurrence:updr=off_24 on theBenchmark
% 0.20/0.53  % (13413)ott+11_8_amm=off:anc=none:bsr=on:cond=on:irw=on:nm=2:nwc=1.1:ss=axioms:st=2.0:sac=on_1 on theBenchmark
% 0.20/0.53  % (13411)dis+1003_64_add=off:afr=on:afp=100000:afq=1.1:anc=none:cond=fast:fde=none:irw=on:nm=6:newcnf=on:nwc=1.3:uhcvi=on_5 on theBenchmark
% 0.20/0.53  % (13399)dis+11_3:1_add=off:afr=on:afp=100000:afq=1.2:amm=off:anc=none:bd=off:bs=unit_only:irw=on:lcm=predicate:lma=on:nm=2:nwc=1:sd=2:ss=axioms:sos=all:sp=occurrence:updr=off_1 on theBenchmark
% 0.20/0.54  % (13410)ott+1002_128_av=off:bd=off:bs=on:bsr=on:cond=on:fsr=off:nm=6:newcnf=on:nwc=1:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.54  % (13397)ott+1_8_av=off:bd=off:bs=on:cond=on:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:lwlo=on:nwc=1:sos=on_10 on theBenchmark
% 0.20/0.54  % (13402)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_36 on theBenchmark
% 0.20/0.57  % (13384)Refutation not found, incomplete strategy% (13384)------------------------------
% 0.20/0.57  % (13384)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.58  % (13384)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.58  
% 0.20/0.58  % (13384)Memory used [KB]: 11257
% 0.20/0.58  % (13384)Time elapsed: 0.187 s
% 1.88/0.58  % (13384)------------------------------
% 1.88/0.58  % (13384)------------------------------
% 2.90/0.72  % (13518)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_4 on theBenchmark
% 3.48/0.80  % (13399)Time limit reached!
% 3.48/0.80  % (13399)------------------------------
% 3.48/0.80  % (13399)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.48/0.81  % (13399)Termination reason: Time limit
% 3.48/0.81  
% 3.48/0.81  % (13399)Memory used [KB]: 7291
% 3.48/0.81  % (13399)Time elapsed: 0.419 s
% 3.48/0.81  % (13399)------------------------------
% 3.48/0.81  % (13399)------------------------------
% 3.48/0.81  % (13413)Time limit reached!
% 3.48/0.81  % (13413)------------------------------
% 3.48/0.81  % (13413)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.48/0.81  % (13413)Termination reason: Time limit
% 3.48/0.81  
% 3.48/0.81  % (13413)Memory used [KB]: 7803
% 3.48/0.81  % (13413)Time elapsed: 0.426 s
% 3.48/0.81  % (13413)------------------------------
% 3.48/0.81  % (13413)------------------------------
% 4.07/0.88  % (13401)Time limit reached!
% 4.07/0.88  % (13401)------------------------------
% 4.07/0.88  % (13401)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.07/0.88  % (13392)Time limit reached!
% 4.07/0.88  % (13392)------------------------------
% 4.07/0.88  % (13392)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.07/0.89  % (13392)Termination reason: Time limit
% 4.07/0.89  % (13392)Termination phase: Saturation
% 4.07/0.89  
% 4.07/0.89  % (13392)Memory used [KB]: 10106
% 4.07/0.89  % (13392)Time elapsed: 0.500 s
% 4.07/0.89  % (13392)------------------------------
% 4.07/0.89  % (13392)------------------------------
% 4.07/0.89  % (13401)Termination reason: Time limit
% 4.07/0.89  
% 4.07/0.89  % (13401)Memory used [KB]: 2430
% 4.07/0.89  % (13401)Time elapsed: 0.503 s
% 4.07/0.89  % (13401)------------------------------
% 4.07/0.89  % (13401)------------------------------
% 4.07/0.89  % (13387)Time limit reached!
% 4.07/0.89  % (13387)------------------------------
% 4.07/0.89  % (13387)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.07/0.89  % (13387)Termination reason: Time limit
% 4.07/0.89  % (13387)Termination phase: Saturation
% 4.07/0.89  
% 4.07/0.89  % (13387)Memory used [KB]: 10362
% 4.07/0.89  % (13387)Time elapsed: 0.500 s
% 4.07/0.89  % (13387)------------------------------
% 4.07/0.89  % (13387)------------------------------
% 4.07/0.89  % (13404)Time limit reached!
% 4.07/0.89  % (13404)------------------------------
% 4.07/0.89  % (13404)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.07/0.89  % (13404)Termination reason: Time limit
% 4.07/0.89  
% 4.07/0.89  % (13404)Memory used [KB]: 6268
% 4.07/0.89  % (13404)Time elapsed: 0.511 s
% 4.07/0.89  % (13404)------------------------------
% 4.07/0.89  % (13404)------------------------------
% 4.07/0.89  % (13412)Time limit reached!
% 4.07/0.89  % (13412)------------------------------
% 4.07/0.89  % (13412)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.07/0.89  % (13412)Termination reason: Time limit
% 4.07/0.89  
% 4.07/0.89  % (13412)Memory used [KB]: 11897
% 4.07/0.89  % (13412)Time elapsed: 0.517 s
% 4.07/0.89  % (13412)------------------------------
% 4.07/0.89  % (13412)------------------------------
% 4.07/0.90  % (13388)Time limit reached!
% 4.07/0.90  % (13388)------------------------------
% 4.07/0.90  % (13388)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.07/0.90  % (13388)Termination reason: Time limit
% 4.07/0.90  
% 4.07/0.90  % (13388)Memory used [KB]: 12920
% 4.07/0.90  % (13388)Time elapsed: 0.515 s
% 4.07/0.90  % (13388)------------------------------
% 4.07/0.90  % (13388)------------------------------
% 4.07/0.90  % (13403)Time limit reached!
% 4.07/0.90  % (13403)------------------------------
% 4.07/0.90  % (13403)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.07/0.90  % (13403)Termination reason: Time limit
% 4.07/0.90  
% 4.07/0.90  % (13403)Memory used [KB]: 7803
% 4.07/0.90  % (13403)Time elapsed: 0.528 s
% 4.07/0.90  % (13403)------------------------------
% 4.07/0.90  % (13403)------------------------------
% 4.33/0.92  % (13590)lrs+10_1_afr=on:afp=100000:afq=1.2:amm=sco:anc=none:br=off:cond=on:gs=on:gsem=on:irw=on:nm=16:nwc=1:stl=30:sac=on:sp=occurrence:urr=on:updr=off_12 on theBenchmark
% 4.45/0.93  % (13406)Time limit reached!
% 4.45/0.93  % (13406)------------------------------
% 4.45/0.93  % (13406)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.45/0.93  % (13406)Termination reason: Time limit
% 4.45/0.93  
% 4.45/0.93  % (13406)Memory used [KB]: 16247
% 4.45/0.93  % (13406)Time elapsed: 0.508 s
% 4.45/0.93  % (13406)------------------------------
% 4.45/0.93  % (13406)------------------------------
% 4.45/0.95  % (13591)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_17 on theBenchmark
% 4.45/0.99  % (13593)dis+11_32_av=off:ep=RST:fsr=off:lwlo=on:nm=6:nwc=1.1:sd=5:ss=axioms:st=5.0:sp=reverse_arity:uhcvi=on_2 on theBenchmark
% 4.45/0.99  % (13592)lrs+10_2:3_afp=1000:afq=1.1:amm=sco:anc=none:er=known:lcm=reverse:lwlo=on:nm=64:newcnf=on:nwc=2:stl=30:sd=5:ss=axioms:sos=theory:sac=on:sp=occurrence_233 on theBenchmark
% 4.45/0.99  % (13393)Time limit reached!
% 4.45/0.99  % (13393)------------------------------
% 4.45/0.99  % (13393)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.45/1.00  % (13393)Termination reason: Time limit
% 4.45/1.00  
% 4.45/1.00  % (13393)Memory used [KB]: 9978
% 4.45/1.00  % (13393)Time elapsed: 0.616 s
% 4.45/1.00  % (13393)------------------------------
% 4.45/1.00  % (13393)------------------------------
% 4.45/1.01  % (13386)Time limit reached!
% 4.45/1.01  % (13386)------------------------------
% 4.45/1.01  % (13386)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.45/1.01  % (13383)Time limit reached!
% 4.45/1.01  % (13383)------------------------------
% 4.45/1.01  % (13383)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.45/1.01  % (13383)Termination reason: Time limit
% 4.45/1.01  
% 4.45/1.01  % (13383)Memory used [KB]: 8955
% 4.45/1.01  % (13383)Time elapsed: 0.610 s
% 4.45/1.01  % (13383)------------------------------
% 4.45/1.01  % (13383)------------------------------
% 4.45/1.01  % (13594)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_125 on theBenchmark
% 4.45/1.01  % (13386)Termination reason: Time limit
% 4.45/1.01  
% 4.45/1.01  % (13386)Memory used [KB]: 12792
% 4.45/1.01  % (13386)Time elapsed: 0.616 s
% 4.45/1.01  % (13386)------------------------------
% 4.45/1.01  % (13386)------------------------------
% 4.45/1.02  % (13595)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_205 on theBenchmark
% 4.97/1.02  % (13597)dis+1002_8_add=large:afp=100000:afq=1.2:amm=off:bs=on:irw=on:nm=2:newcnf=on:nwc=1.1:sos=on:sp=reverse_arity:urr=ec_only:updr=off_259 on theBenchmark
% 4.97/1.03  % (13596)lrs+1011_2:1_av=off:irw=on:lwlo=on:nm=16:newcnf=on:nwc=2:stl=30:sd=4:ss=axioms:st=3.0:sp=occurrence_30 on theBenchmark
% 4.97/1.03  % (13598)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 4.97/1.05  % (13391)Refutation found. Thanks to Tanya!
% 4.97/1.05  % SZS status Theorem for theBenchmark
% 4.97/1.05  % SZS output start Proof for theBenchmark
% 4.97/1.05  fof(f8257,plain,(
% 4.97/1.05    $false),
% 4.97/1.05    inference(avatar_sat_refutation,[],[f308,f506,f676,f813,f932,f955,f4474,f4705,f5343,f5370,f5377,f5381,f5574,f6442,f7035,f7668,f7953,f8027,f8067,f8097,f8106,f8172,f8224,f8256])).
% 4.97/1.06  fof(f8256,plain,(
% 4.97/1.06    ~spl7_10 | spl7_30 | spl7_154 | ~spl7_272),
% 4.97/1.06    inference(avatar_contradiction_clause,[],[f8255])).
% 4.97/1.06  fof(f8255,plain,(
% 4.97/1.06    $false | (~spl7_10 | spl7_30 | spl7_154 | ~spl7_272)),
% 4.97/1.06    inference(subsumption_resolution,[],[f8254,f3913])).
% 4.97/1.06  fof(f3913,plain,(
% 4.97/1.06    k6_partfun1(sK0) != k6_relat_1(sK0) | spl7_154),
% 4.97/1.06    inference(avatar_component_clause,[],[f3912])).
% 4.97/1.06  fof(f3912,plain,(
% 4.97/1.06    spl7_154 <=> k6_partfun1(sK0) = k6_relat_1(sK0)),
% 4.97/1.06    introduced(avatar_definition,[new_symbols(naming,[spl7_154])])).
% 4.97/1.06  fof(f8254,plain,(
% 4.97/1.06    k6_partfun1(sK0) = k6_relat_1(sK0) | (~spl7_10 | spl7_30 | ~spl7_272)),
% 4.97/1.06    inference(backward_demodulation,[],[f8247,f7907])).
% 4.97/1.06  fof(f7907,plain,(
% 4.97/1.06    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK0) | (~spl7_10 | ~spl7_272)),
% 4.97/1.06    inference(forward_demodulation,[],[f287,f7877])).
% 4.97/1.06  fof(f7877,plain,(
% 4.97/1.06    sK0 = k2_relat_1(sK2) | ~spl7_272),
% 4.97/1.06    inference(subsumption_resolution,[],[f7871,f123])).
% 4.97/1.06  fof(f123,plain,(
% 4.97/1.06    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 4.97/1.06    inference(cnf_transformation,[],[f103])).
% 4.97/1.06  fof(f103,plain,(
% 4.97/1.06    (~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK2,sK0,sK0) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 4.97/1.06    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f44,f102,f101])).
% 4.97/1.06  fof(f101,plain,(
% 4.97/1.06    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (? [X2] : (~r2_relset_1(sK0,sK0,X2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(X2,sK0,sK0) & v1_funct_2(X2,sK0,sK0) & v1_funct_1(X2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 4.97/1.06    introduced(choice_axiom,[])).
% 4.97/1.06  fof(f102,plain,(
% 4.97/1.06    ? [X2] : (~r2_relset_1(sK0,sK0,X2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(X2,sK0,sK0) & v1_funct_2(X2,sK0,sK0) & v1_funct_1(X2)) => (~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK2,sK0,sK0) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2))),
% 4.97/1.06    introduced(choice_axiom,[])).
% 4.97/1.06  fof(f44,plain,(
% 4.97/1.06    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 4.97/1.06    inference(flattening,[],[f43])).
% 4.97/1.06  fof(f43,plain,(
% 4.97/1.06    ? [X0,X1] : (? [X2] : ((~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 4.97/1.06    inference(ennf_transformation,[],[f42])).
% 4.97/1.06  fof(f42,negated_conjecture,(
% 4.97/1.06    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 4.97/1.06    inference(negated_conjecture,[],[f41])).
% 4.97/1.06  fof(f41,conjecture,(
% 4.97/1.06    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 4.97/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_funct_2)).
% 4.97/1.06  fof(f7871,plain,(
% 4.97/1.06    sK0 = k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl7_272),
% 4.97/1.06    inference(superposition,[],[f7007,f174])).
% 4.97/1.06  fof(f174,plain,(
% 4.97/1.06    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.97/1.06    inference(cnf_transformation,[],[f75])).
% 4.97/1.06  fof(f75,plain,(
% 4.97/1.06    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.97/1.06    inference(ennf_transformation,[],[f23])).
% 4.97/1.06  fof(f23,axiom,(
% 4.97/1.06    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 4.97/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 4.97/1.06  fof(f7007,plain,(
% 4.97/1.06    sK0 = k2_relset_1(sK0,sK0,sK2) | ~spl7_272),
% 4.97/1.06    inference(avatar_component_clause,[],[f7005])).
% 4.97/1.06  fof(f7005,plain,(
% 4.97/1.06    spl7_272 <=> sK0 = k2_relset_1(sK0,sK0,sK2)),
% 4.97/1.06    introduced(avatar_definition,[new_symbols(naming,[spl7_272])])).
% 4.97/1.06  fof(f287,plain,(
% 4.97/1.06    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2)) | ~spl7_10),
% 4.97/1.06    inference(avatar_component_clause,[],[f285])).
% 4.97/1.06  fof(f285,plain,(
% 4.97/1.06    spl7_10 <=> k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2))),
% 4.97/1.06    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 4.97/1.06  fof(f8247,plain,(
% 4.97/1.06    k6_partfun1(sK0) = k5_relat_1(k2_funct_1(sK2),sK2) | spl7_30),
% 4.97/1.06    inference(subsumption_resolution,[],[f8246,f120])).
% 4.97/1.06  fof(f120,plain,(
% 4.97/1.06    v1_funct_1(sK2)),
% 4.97/1.06    inference(cnf_transformation,[],[f103])).
% 4.97/1.06  fof(f8246,plain,(
% 4.97/1.06    k6_partfun1(sK0) = k5_relat_1(k2_funct_1(sK2),sK2) | ~v1_funct_1(sK2) | spl7_30),
% 4.97/1.06    inference(subsumption_resolution,[],[f8245,f121])).
% 4.97/1.06  fof(f121,plain,(
% 4.97/1.06    v1_funct_2(sK2,sK0,sK0)),
% 4.97/1.06    inference(cnf_transformation,[],[f103])).
% 4.97/1.06  fof(f8245,plain,(
% 4.97/1.06    k6_partfun1(sK0) = k5_relat_1(k2_funct_1(sK2),sK2) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2) | spl7_30),
% 4.97/1.06    inference(subsumption_resolution,[],[f8244,f123])).
% 4.97/1.06  fof(f8244,plain,(
% 4.97/1.06    k6_partfun1(sK0) = k5_relat_1(k2_funct_1(sK2),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2) | spl7_30),
% 4.97/1.06    inference(subsumption_resolution,[],[f8243,f222])).
% 4.97/1.06  fof(f222,plain,(
% 4.97/1.06    v2_funct_1(sK2)),
% 4.97/1.06    inference(subsumption_resolution,[],[f221,f123])).
% 4.97/1.06  fof(f221,plain,(
% 4.97/1.06    v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 4.97/1.06    inference(subsumption_resolution,[],[f218,f120])).
% 4.97/1.06  fof(f218,plain,(
% 4.97/1.06    v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 4.97/1.06    inference(resolution,[],[f184,f122])).
% 4.97/1.06  fof(f122,plain,(
% 4.97/1.06    v3_funct_2(sK2,sK0,sK0)),
% 4.97/1.06    inference(cnf_transformation,[],[f103])).
% 4.97/1.06  fof(f184,plain,(
% 4.97/1.06    ( ! [X2,X0,X1] : (~v3_funct_2(X2,X0,X1) | v2_funct_1(X2) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.97/1.06    inference(cnf_transformation,[],[f81])).
% 4.97/1.06  fof(f81,plain,(
% 4.97/1.06    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.97/1.06    inference(flattening,[],[f80])).
% 4.97/1.06  fof(f80,plain,(
% 4.97/1.06    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.97/1.06    inference(ennf_transformation,[],[f29])).
% 4.97/1.06  fof(f29,axiom,(
% 4.97/1.06    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 4.97/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).
% 4.97/1.06  fof(f8243,plain,(
% 4.97/1.06    ~v2_funct_1(sK2) | k6_partfun1(sK0) = k5_relat_1(k2_funct_1(sK2),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2) | spl7_30),
% 4.97/1.06    inference(subsumption_resolution,[],[f8242,f605])).
% 4.97/1.06  fof(f605,plain,(
% 4.97/1.06    k1_xboole_0 != sK0 | spl7_30),
% 4.97/1.06    inference(avatar_component_clause,[],[f604])).
% 4.97/1.06  fof(f604,plain,(
% 4.97/1.06    spl7_30 <=> k1_xboole_0 = sK0),
% 4.97/1.06    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).
% 4.97/1.06  fof(f8242,plain,(
% 4.97/1.06    k1_xboole_0 = sK0 | ~v2_funct_1(sK2) | k6_partfun1(sK0) = k5_relat_1(k2_funct_1(sK2),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2)),
% 4.97/1.06    inference(trivial_inequality_removal,[],[f8238])).
% 4.97/1.06  fof(f8238,plain,(
% 4.97/1.06    sK0 != sK0 | k1_xboole_0 = sK0 | ~v2_funct_1(sK2) | k6_partfun1(sK0) = k5_relat_1(k2_funct_1(sK2),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2)),
% 4.97/1.06    inference(superposition,[],[f187,f8230])).
% 4.97/1.06  fof(f8230,plain,(
% 4.97/1.06    sK0 = k2_relset_1(sK0,sK0,sK2)),
% 4.97/1.06    inference(subsumption_resolution,[],[f8229,f120])).
% 4.97/1.06  fof(f8229,plain,(
% 4.97/1.06    sK0 = k2_relset_1(sK0,sK0,sK2) | ~v1_funct_1(sK2)),
% 4.97/1.06    inference(subsumption_resolution,[],[f8228,f121])).
% 4.97/1.06  fof(f8228,plain,(
% 4.97/1.06    sK0 = k2_relset_1(sK0,sK0,sK2) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2)),
% 4.97/1.06    inference(subsumption_resolution,[],[f8227,f123])).
% 4.97/1.06  fof(f8227,plain,(
% 4.97/1.06    sK0 = k2_relset_1(sK0,sK0,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2)),
% 4.97/1.06    inference(subsumption_resolution,[],[f8226,f116])).
% 4.97/1.06  fof(f116,plain,(
% 4.97/1.06    v1_funct_1(sK1)),
% 4.97/1.06    inference(cnf_transformation,[],[f103])).
% 4.97/1.06  fof(f8226,plain,(
% 4.97/1.06    sK0 = k2_relset_1(sK0,sK0,sK2) | ~v1_funct_1(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2)),
% 4.97/1.06    inference(subsumption_resolution,[],[f8225,f117])).
% 4.97/1.06  fof(f117,plain,(
% 4.97/1.06    v1_funct_2(sK1,sK0,sK0)),
% 4.97/1.06    inference(cnf_transformation,[],[f103])).
% 4.97/1.06  fof(f8225,plain,(
% 4.97/1.06    sK0 = k2_relset_1(sK0,sK0,sK2) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2)),
% 4.97/1.06    inference(subsumption_resolution,[],[f8208,f119])).
% 4.97/1.06  fof(f119,plain,(
% 4.97/1.06    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 4.97/1.06    inference(cnf_transformation,[],[f103])).
% 4.97/1.06  fof(f8208,plain,(
% 4.97/1.06    sK0 = k2_relset_1(sK0,sK0,sK2) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2)),
% 4.97/1.06    inference(resolution,[],[f124,f188])).
% 4.97/1.06  fof(f188,plain,(
% 4.97/1.06    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | k2_relset_1(X0,X1,X2) = X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 4.97/1.06    inference(cnf_transformation,[],[f85])).
% 4.97/1.06  fof(f85,plain,(
% 4.97/1.06    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 4.97/1.06    inference(flattening,[],[f84])).
% 4.97/1.06  fof(f84,plain,(
% 4.97/1.06    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 4.97/1.06    inference(ennf_transformation,[],[f36])).
% 4.97/1.06  fof(f36,axiom,(
% 4.97/1.06    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 4.97/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_2)).
% 4.97/1.06  fof(f124,plain,(
% 4.97/1.06    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0))),
% 4.97/1.06    inference(cnf_transformation,[],[f103])).
% 4.97/1.06  fof(f187,plain,(
% 4.97/1.06    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 4.97/1.06    inference(cnf_transformation,[],[f83])).
% 4.97/1.06  fof(f83,plain,(
% 4.97/1.06    ! [X0,X1,X2] : ((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 4.97/1.06    inference(flattening,[],[f82])).
% 4.97/1.06  fof(f82,plain,(
% 4.97/1.06    ! [X0,X1,X2] : ((((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 4.97/1.06    inference(ennf_transformation,[],[f39])).
% 4.97/1.06  fof(f39,axiom,(
% 4.97/1.06    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1)))),
% 4.97/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).
% 4.97/1.06  fof(f8224,plain,(
% 4.97/1.06    spl7_272),
% 4.97/1.06    inference(avatar_contradiction_clause,[],[f8223])).
% 4.97/1.06  fof(f8223,plain,(
% 4.97/1.06    $false | spl7_272),
% 4.97/1.06    inference(subsumption_resolution,[],[f8222,f120])).
% 4.97/1.06  fof(f8222,plain,(
% 4.97/1.06    ~v1_funct_1(sK2) | spl7_272),
% 4.97/1.06    inference(subsumption_resolution,[],[f8221,f121])).
% 4.97/1.06  fof(f8221,plain,(
% 4.97/1.06    ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2) | spl7_272),
% 4.97/1.06    inference(subsumption_resolution,[],[f8220,f123])).
% 4.97/1.06  fof(f8220,plain,(
% 4.97/1.06    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2) | spl7_272),
% 4.97/1.06    inference(subsumption_resolution,[],[f8219,f116])).
% 4.97/1.06  fof(f8219,plain,(
% 4.97/1.06    ~v1_funct_1(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2) | spl7_272),
% 4.97/1.06    inference(subsumption_resolution,[],[f8218,f117])).
% 4.97/1.06  fof(f8218,plain,(
% 4.97/1.06    ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2) | spl7_272),
% 4.97/1.06    inference(subsumption_resolution,[],[f8217,f119])).
% 4.97/1.06  fof(f8217,plain,(
% 4.97/1.06    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2) | spl7_272),
% 4.97/1.06    inference(subsumption_resolution,[],[f8208,f7006])).
% 4.97/1.06  fof(f7006,plain,(
% 4.97/1.06    sK0 != k2_relset_1(sK0,sK0,sK2) | spl7_272),
% 4.97/1.06    inference(avatar_component_clause,[],[f7005])).
% 4.97/1.06  fof(f8172,plain,(
% 4.97/1.06    ~spl7_8 | ~spl7_10 | spl7_151 | ~spl7_272),
% 4.97/1.06    inference(avatar_contradiction_clause,[],[f8171])).
% 4.97/1.06  fof(f8171,plain,(
% 4.97/1.06    $false | (~spl7_8 | ~spl7_10 | spl7_151 | ~spl7_272)),
% 4.97/1.06    inference(subsumption_resolution,[],[f7909,f8167])).
% 4.97/1.06  fof(f8167,plain,(
% 4.97/1.06    sK0 != k2_relat_1(k6_relat_1(sK0)) | spl7_151),
% 4.97/1.06    inference(subsumption_resolution,[],[f8166,f127])).
% 4.97/1.06  fof(f127,plain,(
% 4.97/1.06    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 4.97/1.06    inference(cnf_transformation,[],[f26])).
% 4.97/1.06  fof(f26,axiom,(
% 4.97/1.06    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 4.97/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).
% 4.97/1.06  fof(f8166,plain,(
% 4.97/1.06    sK0 != k2_relat_1(k6_relat_1(sK0)) | ~m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl7_151),
% 4.97/1.06    inference(superposition,[],[f3847,f174])).
% 4.97/1.06  fof(f3847,plain,(
% 4.97/1.06    sK0 != k2_relset_1(sK0,sK0,k6_relat_1(sK0)) | spl7_151),
% 4.97/1.06    inference(avatar_component_clause,[],[f3845])).
% 4.97/1.06  fof(f3845,plain,(
% 4.97/1.06    spl7_151 <=> sK0 = k2_relset_1(sK0,sK0,k6_relat_1(sK0))),
% 4.97/1.06    introduced(avatar_definition,[new_symbols(naming,[spl7_151])])).
% 4.97/1.06  % (13599)dis+11_10_av=off:lma=on:nm=64:nwc=5:sp=reverse_arity_3 on theBenchmark
% 4.97/1.06  fof(f7909,plain,(
% 4.97/1.06    sK0 = k2_relat_1(k6_relat_1(sK0)) | (~spl7_8 | ~spl7_10 | ~spl7_272)),
% 4.97/1.06    inference(forward_demodulation,[],[f312,f7877])).
% 4.97/1.06  fof(f312,plain,(
% 4.97/1.06    k2_relat_1(sK2) = k2_relat_1(k6_relat_1(k2_relat_1(sK2))) | (~spl7_8 | ~spl7_10)),
% 4.97/1.06    inference(backward_demodulation,[],[f275,f287])).
% 4.97/1.06  fof(f275,plain,(
% 4.97/1.06    k2_relat_1(sK2) = k2_relat_1(k5_relat_1(k2_funct_1(sK2),sK2)) | ~spl7_8),
% 4.97/1.06    inference(avatar_component_clause,[],[f273])).
% 4.97/1.06  fof(f273,plain,(
% 4.97/1.06    spl7_8 <=> k2_relat_1(sK2) = k2_relat_1(k5_relat_1(k2_funct_1(sK2),sK2))),
% 4.97/1.06    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 4.97/1.06  fof(f8106,plain,(
% 4.97/1.06    spl7_349 | ~spl7_151 | spl7_30 | ~spl7_341),
% 4.97/1.06    inference(avatar_split_clause,[],[f8105,f7665,f604,f3845,f8060])).
% 4.97/1.06  fof(f8060,plain,(
% 4.97/1.06    spl7_349 <=> sK0 = k2_relset_1(sK0,sK0,sK1)),
% 4.97/1.06    introduced(avatar_definition,[new_symbols(naming,[spl7_349])])).
% 4.97/1.06  fof(f7665,plain,(
% 4.97/1.06    spl7_341 <=> k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k6_relat_1(sK0)),
% 4.97/1.06    introduced(avatar_definition,[new_symbols(naming,[spl7_341])])).
% 4.97/1.06  fof(f8105,plain,(
% 4.97/1.06    sK0 != k2_relset_1(sK0,sK0,k6_relat_1(sK0)) | sK0 = k2_relset_1(sK0,sK0,sK1) | (spl7_30 | ~spl7_341)),
% 4.97/1.06    inference(subsumption_resolution,[],[f8104,f116])).
% 4.97/1.06  fof(f8104,plain,(
% 4.97/1.06    sK0 != k2_relset_1(sK0,sK0,k6_relat_1(sK0)) | sK0 = k2_relset_1(sK0,sK0,sK1) | ~v1_funct_1(sK1) | (spl7_30 | ~spl7_341)),
% 4.97/1.06    inference(subsumption_resolution,[],[f8103,f117])).
% 4.97/1.06  fof(f8103,plain,(
% 4.97/1.06    sK0 != k2_relset_1(sK0,sK0,k6_relat_1(sK0)) | sK0 = k2_relset_1(sK0,sK0,sK1) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | (spl7_30 | ~spl7_341)),
% 4.97/1.06    inference(subsumption_resolution,[],[f8102,f119])).
% 4.97/1.06  fof(f8102,plain,(
% 4.97/1.06    sK0 != k2_relset_1(sK0,sK0,k6_relat_1(sK0)) | sK0 = k2_relset_1(sK0,sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | (spl7_30 | ~spl7_341)),
% 4.97/1.06    inference(subsumption_resolution,[],[f8101,f120])).
% 4.97/1.06  fof(f8101,plain,(
% 4.97/1.06    sK0 != k2_relset_1(sK0,sK0,k6_relat_1(sK0)) | sK0 = k2_relset_1(sK0,sK0,sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | (spl7_30 | ~spl7_341)),
% 4.97/1.06    inference(subsumption_resolution,[],[f8100,f121])).
% 4.97/1.06  fof(f8100,plain,(
% 4.97/1.06    sK0 != k2_relset_1(sK0,sK0,k6_relat_1(sK0)) | sK0 = k2_relset_1(sK0,sK0,sK1) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | (spl7_30 | ~spl7_341)),
% 4.97/1.06    inference(subsumption_resolution,[],[f8099,f123])).
% 4.97/1.06  fof(f8099,plain,(
% 4.97/1.06    sK0 != k2_relset_1(sK0,sK0,k6_relat_1(sK0)) | sK0 = k2_relset_1(sK0,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | (spl7_30 | ~spl7_341)),
% 4.97/1.06    inference(subsumption_resolution,[],[f8098,f222])).
% 4.97/1.06  fof(f8098,plain,(
% 4.97/1.06    sK0 != k2_relset_1(sK0,sK0,k6_relat_1(sK0)) | ~v2_funct_1(sK2) | sK0 = k2_relset_1(sK0,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | (spl7_30 | ~spl7_341)),
% 4.97/1.06    inference(subsumption_resolution,[],[f8048,f605])).
% 4.97/1.07  fof(f8048,plain,(
% 4.97/1.07    sK0 != k2_relset_1(sK0,sK0,k6_relat_1(sK0)) | k1_xboole_0 = sK0 | ~v2_funct_1(sK2) | sK0 = k2_relset_1(sK0,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | ~spl7_341),
% 4.97/1.07    inference(superposition,[],[f194,f7667])).
% 4.97/1.07  fof(f7667,plain,(
% 4.97/1.07    k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k6_relat_1(sK0) | ~spl7_341),
% 4.97/1.07    inference(avatar_component_clause,[],[f7665])).
% 4.97/1.07  fof(f194,plain,(
% 4.97/1.07    ( ! [X4,X2,X0,X3,X1] : (k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) != X2 | k1_xboole_0 = X2 | ~v2_funct_1(X4) | k2_relset_1(X0,X1,X3) = X1 | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 4.97/1.07    inference(cnf_transformation,[],[f94])).
% 4.97/1.07  fof(f94,plain,(
% 4.97/1.07    ! [X0,X1,X2,X3] : (! [X4] : (k2_relset_1(X0,X1,X3) = X1 | k1_xboole_0 = X2 | ~v2_funct_1(X4) | k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) != X2 | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 4.97/1.07    inference(flattening,[],[f93])).
% 4.97/1.07  fof(f93,plain,(
% 4.97/1.07    ! [X0,X1,X2,X3] : (! [X4] : (((k2_relset_1(X0,X1,X3) = X1 | k1_xboole_0 = X2) | (~v2_funct_1(X4) | k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) != X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 4.97/1.07    inference(ennf_transformation,[],[f37])).
% 4.97/1.07  fof(f37,axiom,(
% 4.97/1.07    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2) => (k2_relset_1(X0,X1,X3) = X1 | k1_xboole_0 = X2))))),
% 4.97/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_funct_2)).
% 4.97/1.07  fof(f8097,plain,(
% 4.97/1.07    ~spl7_350),
% 4.97/1.07    inference(avatar_contradiction_clause,[],[f8096])).
% 4.97/1.07  fof(f8096,plain,(
% 4.97/1.07    $false | ~spl7_350),
% 4.97/1.07    inference(subsumption_resolution,[],[f8095,f123])).
% 4.97/1.07  fof(f8095,plain,(
% 4.97/1.07    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl7_350),
% 4.97/1.07    inference(resolution,[],[f8091,f208])).
% 4.97/1.07  fof(f208,plain,(
% 4.97/1.07    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.97/1.07    inference(duplicate_literal_removal,[],[f207])).
% 4.97/1.07  fof(f207,plain,(
% 4.97/1.07    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.97/1.07    inference(equality_resolution,[],[f196])).
% 4.97/1.07  fof(f196,plain,(
% 4.97/1.07    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.97/1.07    inference(cnf_transformation,[],[f115])).
% 4.97/1.07  fof(f115,plain,(
% 4.97/1.07    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.97/1.07    inference(nnf_transformation,[],[f96])).
% 4.97/1.07  fof(f96,plain,(
% 4.97/1.07    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.97/1.07    inference(flattening,[],[f95])).
% 4.97/1.07  fof(f95,plain,(
% 4.97/1.07    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 4.97/1.07    inference(ennf_transformation,[],[f24])).
% 4.97/1.07  fof(f24,axiom,(
% 4.97/1.07    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 4.97/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 4.97/1.07  fof(f8091,plain,(
% 4.97/1.07    ~r2_relset_1(sK0,sK0,sK2,sK2) | ~spl7_350),
% 4.97/1.07    inference(backward_demodulation,[],[f7392,f8066])).
% 4.97/1.07  fof(f8066,plain,(
% 4.97/1.07    sK2 = k2_funct_1(sK1) | ~spl7_350),
% 4.97/1.07    inference(avatar_component_clause,[],[f8064])).
% 4.97/1.07  fof(f8064,plain,(
% 4.97/1.07    spl7_350 <=> sK2 = k2_funct_1(sK1)),
% 4.97/1.07    introduced(avatar_definition,[new_symbols(naming,[spl7_350])])).
% 4.97/1.07  fof(f7392,plain,(
% 4.97/1.07    ~r2_relset_1(sK0,sK0,sK2,k2_funct_1(sK1))),
% 4.97/1.07    inference(forward_demodulation,[],[f125,f7070])).
% 4.97/1.07  fof(f7070,plain,(
% 4.97/1.07    k2_funct_2(sK0,sK1) = k2_funct_1(sK1)),
% 4.97/1.07    inference(global_subsumption,[],[f119,f7069])).
% 4.97/1.07  fof(f7069,plain,(
% 4.97/1.07    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k2_funct_2(sK0,sK1) = k2_funct_1(sK1)),
% 4.97/1.07    inference(subsumption_resolution,[],[f7068,f116])).
% 4.97/1.07  fof(f7068,plain,(
% 4.97/1.07    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | ~v1_funct_1(sK1)),
% 4.97/1.07    inference(subsumption_resolution,[],[f7058,f117])).
% 4.97/1.07  fof(f7058,plain,(
% 4.97/1.07    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 4.97/1.07    inference(resolution,[],[f118,f160])).
% 4.97/1.07  fof(f160,plain,(
% 4.97/1.07    ( ! [X0,X1] : (~v3_funct_2(X1,X0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | k2_funct_2(X0,X1) = k2_funct_1(X1) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 4.97/1.07    inference(cnf_transformation,[],[f69])).
% 4.97/1.07  fof(f69,plain,(
% 4.97/1.07    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 4.97/1.07    inference(flattening,[],[f68])).
% 4.97/1.07  fof(f68,plain,(
% 4.97/1.07    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 4.97/1.07    inference(ennf_transformation,[],[f35])).
% 4.97/1.07  fof(f35,axiom,(
% 4.97/1.07    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_2(X0,X1) = k2_funct_1(X1))),
% 4.97/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).
% 4.97/1.07  fof(f118,plain,(
% 4.97/1.07    v3_funct_2(sK1,sK0,sK0)),
% 4.97/1.07    inference(cnf_transformation,[],[f103])).
% 4.97/1.07  fof(f125,plain,(
% 4.97/1.07    ~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1))),
% 4.97/1.07    inference(cnf_transformation,[],[f103])).
% 4.97/1.07  fof(f8067,plain,(
% 4.97/1.07    ~spl7_349 | spl7_350 | spl7_30 | ~spl7_154 | ~spl7_341 | ~spl7_347),
% 4.97/1.07    inference(avatar_split_clause,[],[f8058,f7947,f7665,f3912,f604,f8064,f8060])).
% 4.97/1.07  fof(f7947,plain,(
% 4.97/1.07    spl7_347 <=> r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0))),
% 4.97/1.07    introduced(avatar_definition,[new_symbols(naming,[spl7_347])])).
% 4.97/1.07  fof(f8058,plain,(
% 4.97/1.07    sK2 = k2_funct_1(sK1) | sK0 != k2_relset_1(sK0,sK0,sK1) | (spl7_30 | ~spl7_154 | ~spl7_341 | ~spl7_347)),
% 4.97/1.07    inference(subsumption_resolution,[],[f8057,f7948])).
% 4.97/1.07  fof(f7948,plain,(
% 4.97/1.07    r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0)) | ~spl7_347),
% 4.97/1.07    inference(avatar_component_clause,[],[f7947])).
% 4.97/1.07  fof(f8057,plain,(
% 4.97/1.07    ~r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0)) | sK2 = k2_funct_1(sK1) | sK0 != k2_relset_1(sK0,sK0,sK1) | (spl7_30 | ~spl7_154 | ~spl7_341)),
% 4.97/1.07    inference(forward_demodulation,[],[f8056,f3914])).
% 4.97/1.07  fof(f3914,plain,(
% 4.97/1.07    k6_partfun1(sK0) = k6_relat_1(sK0) | ~spl7_154),
% 4.97/1.07    inference(avatar_component_clause,[],[f3912])).
% 4.97/1.07  fof(f8056,plain,(
% 4.97/1.07    ~r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_partfun1(sK0)) | sK2 = k2_funct_1(sK1) | sK0 != k2_relset_1(sK0,sK0,sK1) | (spl7_30 | ~spl7_341)),
% 4.97/1.07    inference(subsumption_resolution,[],[f8055,f120])).
% 4.97/1.07  fof(f8055,plain,(
% 4.97/1.07    ~r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_partfun1(sK0)) | sK2 = k2_funct_1(sK1) | sK0 != k2_relset_1(sK0,sK0,sK1) | ~v1_funct_1(sK2) | (spl7_30 | ~spl7_341)),
% 4.97/1.07    inference(subsumption_resolution,[],[f8054,f116])).
% 4.97/1.07  fof(f8054,plain,(
% 4.97/1.07    ~r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_partfun1(sK0)) | sK2 = k2_funct_1(sK1) | sK0 != k2_relset_1(sK0,sK0,sK1) | ~v1_funct_1(sK1) | ~v1_funct_1(sK2) | (spl7_30 | ~spl7_341)),
% 4.97/1.07    inference(subsumption_resolution,[],[f8053,f119])).
% 4.97/1.07  fof(f8053,plain,(
% 4.97/1.07    ~r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_partfun1(sK0)) | sK2 = k2_funct_1(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | sK0 != k2_relset_1(sK0,sK0,sK1) | ~v1_funct_1(sK1) | ~v1_funct_1(sK2) | (spl7_30 | ~spl7_341)),
% 4.97/1.07    inference(subsumption_resolution,[],[f8052,f117])).
% 4.97/1.07  fof(f8052,plain,(
% 4.97/1.07    ~r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_partfun1(sK0)) | sK2 = k2_funct_1(sK1) | ~v1_funct_2(sK1,sK0,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | sK0 != k2_relset_1(sK0,sK0,sK1) | ~v1_funct_1(sK1) | ~v1_funct_1(sK2) | (spl7_30 | ~spl7_341)),
% 4.97/1.07    inference(subsumption_resolution,[],[f8051,f605])).
% 4.97/1.07  fof(f8051,plain,(
% 4.97/1.07    ~r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_partfun1(sK0)) | sK2 = k2_funct_1(sK1) | k1_xboole_0 = sK0 | ~v1_funct_2(sK1,sK0,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | sK0 != k2_relset_1(sK0,sK0,sK1) | ~v1_funct_1(sK1) | ~v1_funct_1(sK2) | ~spl7_341),
% 4.97/1.07    inference(subsumption_resolution,[],[f8050,f121])).
% 4.97/1.07  fof(f8050,plain,(
% 4.97/1.07    ~r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_partfun1(sK0)) | sK2 = k2_funct_1(sK1) | ~v1_funct_2(sK2,sK0,sK0) | k1_xboole_0 = sK0 | ~v1_funct_2(sK1,sK0,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | sK0 != k2_relset_1(sK0,sK0,sK1) | ~v1_funct_1(sK1) | ~v1_funct_1(sK2) | ~spl7_341),
% 4.97/1.07    inference(subsumption_resolution,[],[f8049,f123])).
% 4.97/1.07  fof(f8049,plain,(
% 4.97/1.07    ~r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_partfun1(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | sK2 = k2_funct_1(sK1) | ~v1_funct_2(sK2,sK0,sK0) | k1_xboole_0 = sK0 | ~v1_funct_2(sK1,sK0,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | sK0 != k2_relset_1(sK0,sK0,sK1) | ~v1_funct_1(sK1) | ~v1_funct_1(sK2) | ~spl7_341),
% 4.97/1.07    inference(duplicate_literal_removal,[],[f8045])).
% 4.97/1.07  fof(f8045,plain,(
% 4.97/1.07    ~r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_partfun1(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | sK2 = k2_funct_1(sK1) | ~v1_funct_2(sK2,sK0,sK0) | k1_xboole_0 = sK0 | ~v1_funct_2(sK1,sK0,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | sK0 != k2_relset_1(sK0,sK0,sK1) | ~v1_funct_1(sK1) | k1_xboole_0 = sK0 | ~v1_funct_1(sK2) | ~spl7_341),
% 4.97/1.07    inference(superposition,[],[f209,f7667])).
% 4.97/1.07  fof(f209,plain,(
% 4.97/1.07    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_funct_1(X2) = X3 | ~v1_funct_2(X3,X1,X0) | k1_xboole_0 = X1 | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) != X1 | ~v1_funct_1(X2) | k1_xboole_0 = X0 | ~v1_funct_1(X3)) )),
% 4.97/1.07    inference(global_subsumption,[],[f189,f191])).
% 4.97/1.07  fof(f191,plain,(
% 4.97/1.07    ( ! [X2,X0,X3,X1] : (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 4.97/1.07    inference(cnf_transformation,[],[f89])).
% 4.97/1.07  fof(f89,plain,(
% 4.97/1.07    ! [X0,X1,X2] : (! [X3] : (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 4.97/1.07    inference(flattening,[],[f88])).
% 4.97/1.07  fof(f88,plain,(
% 4.97/1.07    ! [X0,X1,X2] : (! [X3] : (((k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0) | (~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 4.97/1.07    inference(ennf_transformation,[],[f40])).
% 4.97/1.07  fof(f40,axiom,(
% 4.97/1.07    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 4.97/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).
% 4.97/1.07  fof(f189,plain,(
% 4.97/1.07    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | v2_funct_1(X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 4.97/1.07    inference(cnf_transformation,[],[f87])).
% 4.97/1.07  fof(f87,plain,(
% 4.97/1.07    ! [X0,X1,X2] : (! [X3] : ((v2_funct_2(X3,X0) & v2_funct_1(X2)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 4.97/1.07    inference(flattening,[],[f86])).
% 4.97/1.07  fof(f86,plain,(
% 4.97/1.07    ! [X0,X1,X2] : (! [X3] : (((v2_funct_2(X3,X0) & v2_funct_1(X2)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 4.97/1.07    inference(ennf_transformation,[],[f38])).
% 4.97/1.07  fof(f38,axiom,(
% 4.97/1.07    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 4.97/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_funct_2)).
% 4.97/1.07  fof(f8027,plain,(
% 4.97/1.07    spl7_340),
% 4.97/1.07    inference(avatar_contradiction_clause,[],[f8026])).
% 4.97/1.07  fof(f8026,plain,(
% 4.97/1.07    $false | spl7_340),
% 4.97/1.07    inference(subsumption_resolution,[],[f8025,f116])).
% 4.97/1.07  fof(f8025,plain,(
% 4.97/1.07    ~v1_funct_1(sK1) | spl7_340),
% 4.97/1.07    inference(subsumption_resolution,[],[f8024,f119])).
% 4.97/1.07  fof(f8024,plain,(
% 4.97/1.07    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1) | spl7_340),
% 4.97/1.07    inference(subsumption_resolution,[],[f8023,f120])).
% 4.97/1.07  fof(f8023,plain,(
% 4.97/1.07    ~v1_funct_1(sK2) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1) | spl7_340),
% 4.97/1.07    inference(subsumption_resolution,[],[f8020,f123])).
% 4.97/1.07  fof(f8020,plain,(
% 4.97/1.07    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1) | spl7_340),
% 4.97/1.07    inference(resolution,[],[f7663,f199])).
% 4.97/1.07  fof(f199,plain,(
% 4.97/1.07    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 4.97/1.07    inference(cnf_transformation,[],[f100])).
% 4.97/1.07  fof(f100,plain,(
% 4.97/1.07    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 4.97/1.07    inference(flattening,[],[f99])).
% 4.97/1.07  fof(f99,plain,(
% 4.97/1.07    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 4.97/1.07    inference(ennf_transformation,[],[f31])).
% 4.97/1.07  fof(f31,axiom,(
% 4.97/1.07    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 4.97/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 4.97/1.07  fof(f7663,plain,(
% 4.97/1.07    ~m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl7_340),
% 4.97/1.07    inference(avatar_component_clause,[],[f7661])).
% 4.97/1.07  fof(f7661,plain,(
% 4.97/1.07    spl7_340 <=> m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 4.97/1.07    introduced(avatar_definition,[new_symbols(naming,[spl7_340])])).
% 4.97/1.07  fof(f7953,plain,(
% 4.97/1.07    spl7_347),
% 4.97/1.07    inference(avatar_contradiction_clause,[],[f7952])).
% 4.97/1.07  fof(f7952,plain,(
% 4.97/1.07    $false | spl7_347),
% 4.97/1.07    inference(subsumption_resolution,[],[f7951,f127])).
% 4.97/1.07  fof(f7951,plain,(
% 4.97/1.07    ~m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl7_347),
% 4.97/1.07    inference(resolution,[],[f7949,f208])).
% 4.97/1.07  fof(f7949,plain,(
% 4.97/1.07    ~r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0)) | spl7_347),
% 4.97/1.07    inference(avatar_component_clause,[],[f7947])).
% 4.97/1.07  fof(f7668,plain,(
% 4.97/1.07    ~spl7_340 | spl7_341 | ~spl7_154),
% 4.97/1.07    inference(avatar_split_clause,[],[f7659,f3912,f7665,f7661])).
% 4.97/1.07  fof(f7659,plain,(
% 4.97/1.07    k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k6_relat_1(sK0) | ~m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl7_154),
% 4.97/1.07    inference(subsumption_resolution,[],[f7658,f127])).
% 4.97/1.07  fof(f7658,plain,(
% 4.97/1.07    k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k6_relat_1(sK0) | ~m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl7_154),
% 4.97/1.07    inference(resolution,[],[f7475,f195])).
% 4.97/1.07  fof(f195,plain,(
% 4.97/1.07    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.97/1.07    inference(cnf_transformation,[],[f115])).
% 4.97/1.07  fof(f7475,plain,(
% 4.97/1.07    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_relat_1(sK0)) | ~spl7_154),
% 4.97/1.07    inference(forward_demodulation,[],[f124,f3914])).
% 4.97/1.07  fof(f7035,plain,(
% 4.97/1.07    spl7_22 | spl7_23),
% 4.97/1.07    inference(avatar_split_clause,[],[f7033,f418,f414])).
% 4.97/1.07  fof(f414,plain,(
% 4.97/1.07    spl7_22 <=> k1_xboole_0 = sK1),
% 4.97/1.07    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).
% 4.97/1.07  fof(f418,plain,(
% 4.97/1.07    spl7_23 <=> ! [X1] : (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) | ~v1_xboole_0(X1) | k1_xboole_0 = X1)),
% 4.97/1.07    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).
% 4.97/1.07  fof(f7033,plain,(
% 4.97/1.07    ( ! [X0] : (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | k1_xboole_0 = sK1 | k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 4.97/1.07    inference(resolution,[],[f116,f403])).
% 4.97/1.07  fof(f403,plain,(
% 4.97/1.07    ( ! [X2,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | ~v1_xboole_0(X1)) )),
% 4.97/1.07    inference(condensation,[],[f402])).
% 4.97/1.07  fof(f402,plain,(
% 4.97/1.07    ( ! [X2,X3,X1] : (k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) | k1_xboole_0 = X2 | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) | ~v1_xboole_0(X1)) )),
% 4.97/1.07    inference(resolution,[],[f386,f150])).
% 4.97/1.07  fof(f150,plain,(
% 4.97/1.07    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0)) )),
% 4.97/1.07    inference(cnf_transformation,[],[f60])).
% 4.97/1.07  fof(f60,plain,(
% 4.97/1.07    ! [X0,X1] : (! [X2] : (v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 4.97/1.07    inference(ennf_transformation,[],[f28])).
% 4.97/1.07  fof(f28,axiom,(
% 4.97/1.07    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_partfun1(X2,X0)))),
% 4.97/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_partfun1)).
% 4.97/1.07  fof(f386,plain,(
% 4.97/1.07    ( ! [X2,X1] : (~v1_partfun1(X1,X2) | k1_xboole_0 = X2 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,k1_xboole_0))) | k1_xboole_0 = X1 | ~v1_funct_1(X1)) )),
% 4.97/1.07    inference(duplicate_literal_removal,[],[f385])).
% 4.97/1.07  fof(f385,plain,(
% 4.97/1.07    ( ! [X2,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X2 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,k1_xboole_0))) | ~v1_partfun1(X1,X2) | ~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,k1_xboole_0)))) )),
% 4.97/1.07    inference(resolution,[],[f204,f182])).
% 4.97/1.07  fof(f182,plain,(
% 4.97/1.07    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.97/1.07    inference(cnf_transformation,[],[f79])).
% 4.97/1.07  fof(f79,plain,(
% 4.97/1.07    ! [X0,X1,X2] : ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.97/1.07    inference(flattening,[],[f78])).
% 4.97/1.07  fof(f78,plain,(
% 4.97/1.07    ! [X0,X1,X2] : (((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~v1_partfun1(X2,X0) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.97/1.07    inference(ennf_transformation,[],[f27])).
% 4.97/1.07  fof(f27,axiom,(
% 4.97/1.07    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_partfun1(X2,X0) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 4.97/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_2)).
% 4.97/1.07  fof(f204,plain,(
% 4.97/1.07    ( ! [X2,X0] : (~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X2 | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 4.97/1.07    inference(equality_resolution,[],[f179])).
% 4.97/1.07  fof(f179,plain,(
% 4.97/1.07    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.97/1.07    inference(cnf_transformation,[],[f114])).
% 4.97/1.07  fof(f114,plain,(
% 4.97/1.07    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.97/1.07    inference(nnf_transformation,[],[f77])).
% 4.97/1.07  fof(f77,plain,(
% 4.97/1.07    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.97/1.07    inference(flattening,[],[f76])).
% 4.97/1.07  fof(f76,plain,(
% 4.97/1.07    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.97/1.07    inference(ennf_transformation,[],[f30])).
% 4.97/1.07  fof(f30,axiom,(
% 4.97/1.07    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 4.97/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 4.97/1.07  fof(f6442,plain,(
% 4.97/1.07    ~spl7_20 | spl7_24 | ~spl7_25 | ~spl7_28 | ~spl7_196),
% 4.97/1.07    inference(avatar_contradiction_clause,[],[f6441])).
% 4.97/1.07  fof(f6441,plain,(
% 4.97/1.07    $false | (~spl7_20 | spl7_24 | ~spl7_25 | ~spl7_28 | ~spl7_196)),
% 4.97/1.07    inference(subsumption_resolution,[],[f6431,f423])).
% 4.97/1.07  fof(f423,plain,(
% 4.97/1.07    k1_xboole_0 != sK2 | spl7_24),
% 4.97/1.07    inference(avatar_component_clause,[],[f422])).
% 4.97/1.07  fof(f422,plain,(
% 4.97/1.07    spl7_24 <=> k1_xboole_0 = sK2),
% 4.97/1.07    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).
% 4.97/1.07  fof(f6431,plain,(
% 4.97/1.07    k1_xboole_0 = sK2 | (~spl7_20 | ~spl7_25 | ~spl7_28 | ~spl7_196)),
% 4.97/1.07    inference(resolution,[],[f6426,f5358])).
% 4.97/1.08  fof(f5358,plain,(
% 4.97/1.08    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~spl7_196),
% 4.97/1.08    inference(avatar_component_clause,[],[f5357])).
% 4.97/1.08  fof(f5357,plain,(
% 4.97/1.08    spl7_196 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 4.97/1.08    introduced(avatar_definition,[new_symbols(naming,[spl7_196])])).
% 4.97/1.08  fof(f6426,plain,(
% 4.97/1.08    ( ! [X14,X13] : (~m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X14,k1_xboole_0))) | k1_xboole_0 = X13) ) | (~spl7_20 | ~spl7_25 | ~spl7_28 | ~spl7_196)),
% 4.97/1.08    inference(resolution,[],[f6230,f494])).
% 4.97/1.08  fof(f494,plain,(
% 4.97/1.08    v1_xboole_0(k1_xboole_0) | ~spl7_28),
% 4.97/1.08    inference(avatar_component_clause,[],[f493])).
% 4.97/1.08  fof(f493,plain,(
% 4.97/1.08    spl7_28 <=> v1_xboole_0(k1_xboole_0)),
% 4.97/1.08    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).
% 4.97/1.08  fof(f6230,plain,(
% 4.97/1.08    ( ! [X4,X2,X3] : (~v1_xboole_0(X4) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | k1_xboole_0 = X2) ) | (~spl7_20 | ~spl7_25 | ~spl7_196)),
% 4.97/1.08    inference(resolution,[],[f6055,f149])).
% 4.97/1.08  fof(f149,plain,(
% 4.97/1.08    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0)) )),
% 4.97/1.08    inference(cnf_transformation,[],[f59])).
% 4.97/1.08  fof(f59,plain,(
% 4.97/1.08    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 4.97/1.08    inference(ennf_transformation,[],[f22])).
% 4.97/1.08  fof(f22,axiom,(
% 4.97/1.08    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 4.97/1.08    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).
% 4.97/1.08  fof(f6055,plain,(
% 4.97/1.08    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) ) | (~spl7_20 | ~spl7_25 | ~spl7_196)),
% 4.97/1.08    inference(subsumption_resolution,[],[f6054,f381])).
% 4.97/1.08  fof(f381,plain,(
% 4.97/1.08    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | ~spl7_20),
% 4.97/1.08    inference(backward_demodulation,[],[f335,f374])).
% 4.97/1.08  fof(f374,plain,(
% 4.97/1.08    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl7_20),
% 4.97/1.08    inference(avatar_component_clause,[],[f372])).
% 4.97/1.08  fof(f372,plain,(
% 4.97/1.08    spl7_20 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 4.97/1.08    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).
% 4.97/1.08  fof(f335,plain,(
% 4.97/1.08    ( ! [X0] : (r1_tarski(k1_relat_1(k1_xboole_0),X0)) )),
% 4.97/1.08    inference(subsumption_resolution,[],[f334,f143])).
% 4.97/1.08  fof(f143,plain,(
% 4.97/1.08    ( ! [X0] : (v1_relat_1(sK3(X0))) )),
% 4.97/1.08    inference(cnf_transformation,[],[f105])).
% 4.97/1.08  fof(f105,plain,(
% 4.97/1.08    ! [X0] : (! [X2] : (np__1 = k1_funct_1(sK3(X0),X2) | ~r2_hidden(X2,X0)) & k1_relat_1(sK3(X0)) = X0 & v1_funct_1(sK3(X0)) & v1_relat_1(sK3(X0)))),
% 4.97/1.08    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f58,f104])).
% 4.97/1.08  fof(f104,plain,(
% 4.97/1.08    ! [X0] : (? [X1] : (! [X2] : (k1_funct_1(X1,X2) = np__1 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1)) => (! [X2] : (np__1 = k1_funct_1(sK3(X0),X2) | ~r2_hidden(X2,X0)) & k1_relat_1(sK3(X0)) = X0 & v1_funct_1(sK3(X0)) & v1_relat_1(sK3(X0))))),
% 4.97/1.08    introduced(choice_axiom,[])).
% 4.97/1.08  fof(f58,plain,(
% 4.97/1.08    ! [X0] : ? [X1] : (! [X2] : (k1_funct_1(X1,X2) = np__1 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 4.97/1.08    inference(ennf_transformation,[],[f14])).
% 4.97/1.08  fof(f14,axiom,(
% 4.97/1.08    ! [X0] : ? [X1] : (! [X2] : (r2_hidden(X2,X0) => k1_funct_1(X1,X2) = np__1) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 4.97/1.08    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e7_25__funct_1)).
% 4.97/1.08  fof(f334,plain,(
% 4.97/1.08    ( ! [X0] : (r1_tarski(k1_relat_1(k1_xboole_0),X0) | ~v1_relat_1(sK3(X0))) )),
% 4.97/1.08    inference(subsumption_resolution,[],[f331,f144])).
% 4.97/1.08  fof(f144,plain,(
% 4.97/1.08    ( ! [X0] : (v1_funct_1(sK3(X0))) )),
% 4.97/1.08    inference(cnf_transformation,[],[f105])).
% 4.97/1.08  fof(f331,plain,(
% 4.97/1.08    ( ! [X0] : (r1_tarski(k1_relat_1(k1_xboole_0),X0) | ~v1_funct_1(sK3(X0)) | ~v1_relat_1(sK3(X0))) )),
% 4.97/1.08    inference(superposition,[],[f330,f145])).
% 4.97/1.08  fof(f145,plain,(
% 4.97/1.08    ( ! [X0] : (k1_relat_1(sK3(X0)) = X0) )),
% 4.97/1.08    inference(cnf_transformation,[],[f105])).
% 4.97/1.08  fof(f330,plain,(
% 4.97/1.08    ( ! [X0] : (r1_tarski(k1_relat_1(k1_xboole_0),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 4.97/1.08    inference(subsumption_resolution,[],[f329,f128])).
% 4.97/1.08  fof(f128,plain,(
% 4.97/1.08    v1_relat_1(k1_xboole_0)),
% 4.97/1.08    inference(cnf_transformation,[],[f20])).
% 4.97/1.08  fof(f20,axiom,(
% 4.97/1.08    ! [X0] : (v5_ordinal1(k1_xboole_0) & v1_funct_1(k1_xboole_0) & v5_relat_1(k1_xboole_0,X0) & v1_relat_1(k1_xboole_0))),
% 4.97/1.08    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_ordinal1)).
% 4.97/1.08  fof(f329,plain,(
% 4.97/1.08    ( ! [X0] : (r1_tarski(k1_relat_1(k1_xboole_0),k1_relat_1(X0)) | ~v1_relat_1(k1_xboole_0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 4.97/1.08    inference(subsumption_resolution,[],[f328,f130])).
% 4.97/1.08  fof(f130,plain,(
% 4.97/1.08    v1_funct_1(k1_xboole_0)),
% 4.97/1.08    inference(cnf_transformation,[],[f20])).
% 4.97/1.08  fof(f328,plain,(
% 4.97/1.08    ( ! [X0] : (r1_tarski(k1_relat_1(k1_xboole_0),k1_relat_1(X0)) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 4.97/1.08    inference(duplicate_literal_removal,[],[f327])).
% 4.97/1.08  fof(f327,plain,(
% 4.97/1.08    ( ! [X0] : (r1_tarski(k1_relat_1(k1_xboole_0),k1_relat_1(X0)) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 4.97/1.08    inference(resolution,[],[f142,f136])).
% 4.97/1.08  fof(f136,plain,(
% 4.97/1.08    ( ! [X0] : (v5_funct_1(k1_xboole_0,X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 4.97/1.08    inference(cnf_transformation,[],[f49])).
% 4.97/1.08  fof(f49,plain,(
% 4.97/1.08    ! [X0] : (v5_funct_1(k1_xboole_0,X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 4.97/1.08    inference(flattening,[],[f48])).
% 4.97/1.08  fof(f48,plain,(
% 4.97/1.08    ! [X0] : (v5_funct_1(k1_xboole_0,X0) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 4.97/1.08    inference(ennf_transformation,[],[f15])).
% 4.97/1.08  fof(f15,axiom,(
% 4.97/1.08    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => v5_funct_1(k1_xboole_0,X0))),
% 4.97/1.08    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_funct_1)).
% 4.97/1.08  fof(f142,plain,(
% 4.97/1.08    ( ! [X0,X1] : (~v5_funct_1(X1,X0) | r1_tarski(k1_relat_1(X1),k1_relat_1(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 4.97/1.08    inference(cnf_transformation,[],[f57])).
% 4.97/1.08  fof(f57,plain,(
% 4.97/1.08    ! [X0] : (! [X1] : (r1_tarski(k1_relat_1(X1),k1_relat_1(X0)) | ~v5_funct_1(X1,X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 4.97/1.08    inference(flattening,[],[f56])).
% 4.97/1.08  fof(f56,plain,(
% 4.97/1.08    ! [X0] : (! [X1] : (r1_tarski(k1_relat_1(X1),k1_relat_1(X0)) | (~v5_funct_1(X1,X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 4.97/1.08    inference(ennf_transformation,[],[f16])).
% 4.97/1.08  fof(f16,axiom,(
% 4.97/1.08    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v5_funct_1(X1,X0) & v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k1_relat_1(X1),k1_relat_1(X0))))),
% 4.97/1.08    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_funct_1)).
% 4.97/1.08  fof(f6054,plain,(
% 4.97/1.08    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(k1_xboole_0,X0) | ~v1_xboole_0(X0)) ) | (~spl7_20 | ~spl7_25 | ~spl7_196)),
% 4.97/1.08    inference(subsumption_resolution,[],[f6053,f381])).
% 4.97/1.08  fof(f6053,plain,(
% 4.97/1.08    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(k1_xboole_0,k1_xboole_0) | ~r1_tarski(k1_xboole_0,X0) | ~v1_xboole_0(X0)) ) | (~spl7_25 | ~spl7_196)),
% 4.97/1.08    inference(resolution,[],[f5358,f5621])).
% 4.97/1.08  fof(f5621,plain,(
% 4.97/1.08    ( ! [X2,X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | k1_xboole_0 = X0 | ~r1_tarski(X1,k1_xboole_0) | ~r1_tarski(X2,X0) | ~v1_xboole_0(X0)) ) | ~spl7_25),
% 4.97/1.08    inference(resolution,[],[f427,f197])).
% 4.97/1.08  fof(f197,plain,(
% 4.97/1.08    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) )),
% 4.97/1.08    inference(cnf_transformation,[],[f98])).
% 4.97/1.08  fof(f98,plain,(
% 4.97/1.08    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 4.97/1.08    inference(flattening,[],[f97])).
% 4.97/1.08  fof(f97,plain,(
% 4.97/1.08    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) | (~r1_tarski(X2,X3) | ~r1_tarski(X0,X1))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 4.97/1.08    inference(ennf_transformation,[],[f25])).
% 4.97/1.08  fof(f25,axiom,(
% 4.97/1.08    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))))),
% 4.97/1.08    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_relset_1)).
% 4.97/1.08  fof(f427,plain,(
% 4.97/1.08    ( ! [X2] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,k1_xboole_0))) | ~v1_xboole_0(X2) | k1_xboole_0 = X2) ) | ~spl7_25),
% 4.97/1.08    inference(avatar_component_clause,[],[f426])).
% 4.97/1.08  fof(f426,plain,(
% 4.97/1.08    spl7_25 <=> ! [X2] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,k1_xboole_0))) | ~v1_xboole_0(X2) | k1_xboole_0 = X2)),
% 4.97/1.08    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).
% 4.97/1.08  fof(f5574,plain,(
% 4.97/1.08    ~spl7_30 | spl7_196),
% 4.97/1.08    inference(avatar_contradiction_clause,[],[f5573])).
% 4.97/1.08  fof(f5573,plain,(
% 4.97/1.08    $false | (~spl7_30 | spl7_196)),
% 4.97/1.08    inference(subsumption_resolution,[],[f5359,f3943])).
% 4.97/1.08  fof(f3943,plain,(
% 4.97/1.08    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~spl7_30),
% 4.97/1.08    inference(backward_demodulation,[],[f123,f606])).
% 4.97/1.08  fof(f606,plain,(
% 4.97/1.08    k1_xboole_0 = sK0 | ~spl7_30),
% 4.97/1.08    inference(avatar_component_clause,[],[f604])).
% 4.97/1.08  fof(f5359,plain,(
% 4.97/1.08    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | spl7_196),
% 4.97/1.08    inference(avatar_component_clause,[],[f5357])).
% 4.97/1.08  fof(f5381,plain,(
% 4.97/1.08    ~spl7_7 | spl7_10),
% 4.97/1.08    inference(avatar_split_clause,[],[f5380,f285,f269])).
% 4.97/1.08  fof(f269,plain,(
% 4.97/1.08    spl7_7 <=> v1_relat_1(sK2)),
% 4.97/1.08    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 4.97/1.08  fof(f5380,plain,(
% 4.97/1.08    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2)) | ~v1_relat_1(sK2)),
% 4.97/1.08    inference(subsumption_resolution,[],[f5373,f120])).
% 4.97/1.08  fof(f5373,plain,(
% 4.97/1.08    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 4.97/1.08    inference(resolution,[],[f222,f139])).
% 4.97/1.08  fof(f139,plain,(
% 4.97/1.08    ( ! [X0] : (~v2_funct_1(X0) | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 4.97/1.08    inference(cnf_transformation,[],[f53])).
% 4.97/1.08  fof(f53,plain,(
% 4.97/1.08    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 4.97/1.08    inference(flattening,[],[f52])).
% 4.97/1.08  fof(f52,plain,(
% 4.97/1.08    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 4.97/1.08    inference(ennf_transformation,[],[f18])).
% 4.97/1.08  fof(f18,axiom,(
% 4.97/1.08    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 4.97/1.08    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).
% 4.97/1.08  fof(f5377,plain,(
% 4.97/1.08    ~spl7_7 | spl7_8),
% 4.97/1.08    inference(avatar_split_clause,[],[f5376,f273,f269])).
% 4.97/1.08  fof(f5376,plain,(
% 4.97/1.08    k2_relat_1(sK2) = k2_relat_1(k5_relat_1(k2_funct_1(sK2),sK2)) | ~v1_relat_1(sK2)),
% 4.97/1.08    inference(subsumption_resolution,[],[f5371,f120])).
% 4.97/1.08  fof(f5371,plain,(
% 4.97/1.08    k2_relat_1(sK2) = k2_relat_1(k5_relat_1(k2_funct_1(sK2),sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 4.97/1.08    inference(resolution,[],[f222,f141])).
% 4.97/1.08  fof(f141,plain,(
% 4.97/1.08    ( ! [X0] : (~v2_funct_1(X0) | k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 4.97/1.08    inference(cnf_transformation,[],[f55])).
% 4.97/1.08  fof(f55,plain,(
% 4.97/1.08    ! [X0] : ((k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 4.97/1.08    inference(flattening,[],[f54])).
% 4.97/1.08  fof(f54,plain,(
% 4.97/1.08    ! [X0] : (((k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 4.97/1.08    inference(ennf_transformation,[],[f17])).
% 4.97/1.08  fof(f17,axiom,(
% 4.97/1.08    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0))))),
% 4.97/1.08    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_funct_1)).
% 4.97/1.08  fof(f5370,plain,(
% 4.97/1.08    spl7_24 | spl7_25),
% 4.97/1.08    inference(avatar_split_clause,[],[f5368,f426,f422])).
% 4.97/1.08  fof(f5368,plain,(
% 4.97/1.08    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | k1_xboole_0 = sK2 | k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 4.97/1.08    inference(resolution,[],[f120,f403])).
% 4.97/1.08  fof(f5343,plain,(
% 4.97/1.08    ~spl7_20 | ~spl7_22 | ~spl7_28 | spl7_168 | ~spl7_190),
% 4.97/1.08    inference(avatar_contradiction_clause,[],[f5342])).
% 4.97/1.08  fof(f5342,plain,(
% 4.97/1.08    $false | (~spl7_20 | ~spl7_22 | ~spl7_28 | spl7_168 | ~spl7_190)),
% 4.97/1.08    inference(subsumption_resolution,[],[f5335,f4252])).
% 4.97/1.08  fof(f4252,plain,(
% 4.97/1.08    k1_xboole_0 != k2_funct_1(k1_xboole_0) | spl7_168),
% 4.97/1.08    inference(avatar_component_clause,[],[f4251])).
% 4.97/1.08  fof(f4251,plain,(
% 4.97/1.08    spl7_168 <=> k1_xboole_0 = k2_funct_1(k1_xboole_0)),
% 4.97/1.08    introduced(avatar_definition,[new_symbols(naming,[spl7_168])])).
% 4.97/1.08  fof(f5335,plain,(
% 4.97/1.08    k1_xboole_0 = k2_funct_1(k1_xboole_0) | (~spl7_20 | ~spl7_22 | ~spl7_28 | spl7_168 | ~spl7_190)),
% 4.97/1.08    inference(resolution,[],[f5330,f4604])).
% 4.97/1.08  fof(f4604,plain,(
% 4.97/1.08    m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~spl7_190),
% 4.97/1.08    inference(avatar_component_clause,[],[f4603])).
% 4.97/1.08  fof(f4603,plain,(
% 4.97/1.08    spl7_190 <=> m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 4.97/1.08    introduced(avatar_definition,[new_symbols(naming,[spl7_190])])).
% 4.97/1.08  fof(f5330,plain,(
% 4.97/1.08    ( ! [X14,X13] : (~m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X14,k1_xboole_0))) | k1_xboole_0 = X13) ) | (~spl7_20 | ~spl7_22 | ~spl7_28 | spl7_168 | ~spl7_190)),
% 4.97/1.08    inference(resolution,[],[f5296,f494])).
% 4.97/1.08  fof(f5296,plain,(
% 4.97/1.08    ( ! [X4,X2,X3] : (~v1_xboole_0(X4) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | k1_xboole_0 = X2) ) | (~spl7_20 | ~spl7_22 | spl7_168 | ~spl7_190)),
% 4.97/1.08    inference(resolution,[],[f5294,f149])).
% 4.97/1.08  fof(f5294,plain,(
% 4.97/1.08    ( ! [X5] : (~v1_xboole_0(X5) | k1_xboole_0 = X5) ) | (~spl7_20 | ~spl7_22 | spl7_168 | ~spl7_190)),
% 4.97/1.08    inference(subsumption_resolution,[],[f5293,f381])).
% 4.97/1.08  fof(f5293,plain,(
% 4.97/1.08    ( ! [X5] : (~v1_xboole_0(X5) | ~r1_tarski(k1_xboole_0,X5) | k1_xboole_0 = X5) ) | (~spl7_20 | ~spl7_22 | spl7_168 | ~spl7_190)),
% 4.97/1.08    inference(subsumption_resolution,[],[f5291,f381])).
% 4.97/1.08  fof(f5291,plain,(
% 4.97/1.08    ( ! [X5] : (~v1_xboole_0(X5) | ~r1_tarski(k1_xboole_0,k1_xboole_0) | ~r1_tarski(k1_xboole_0,X5) | k1_xboole_0 = X5) ) | (~spl7_22 | spl7_168 | ~spl7_190)),
% 4.97/1.08    inference(resolution,[],[f5286,f4604])).
% 4.97/1.08  fof(f5286,plain,(
% 4.97/1.08    ( ! [X2,X0,X1] : (~m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_xboole_0(X0) | ~r1_tarski(X1,k1_xboole_0) | ~r1_tarski(X2,X0) | k1_xboole_0 = X0) ) | (~spl7_22 | spl7_168)),
% 4.97/1.08    inference(resolution,[],[f5217,f197])).
% 4.97/1.08  fof(f5217,plain,(
% 4.97/1.08    ( ! [X1] : (~m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) | k1_xboole_0 = X1 | ~v1_xboole_0(X1)) ) | (~spl7_22 | spl7_168)),
% 4.97/1.08    inference(subsumption_resolution,[],[f5211,f4252])).
% 4.97/1.08  fof(f5211,plain,(
% 4.97/1.08    ( ! [X1] : (~m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) | k1_xboole_0 = k2_funct_1(k1_xboole_0) | k1_xboole_0 = X1 | ~v1_xboole_0(X1)) ) | ~spl7_22),
% 4.97/1.08    inference(resolution,[],[f403,f3260])).
% 4.97/1.08  fof(f3260,plain,(
% 4.97/1.08    v1_funct_1(k2_funct_1(k1_xboole_0)) | ~spl7_22),
% 4.97/1.08    inference(subsumption_resolution,[],[f3259,f130])).
% 4.97/1.08  fof(f3259,plain,(
% 4.97/1.08    v1_funct_1(k2_funct_1(k1_xboole_0)) | ~v1_funct_1(k1_xboole_0) | ~spl7_22),
% 4.97/1.08    inference(subsumption_resolution,[],[f3258,f1471])).
% 4.97/1.08  fof(f1471,plain,(
% 4.97/1.08    v1_funct_2(k1_xboole_0,sK0,sK0) | ~spl7_22),
% 4.97/1.08    inference(backward_demodulation,[],[f117,f416])).
% 4.97/1.08  fof(f416,plain,(
% 4.97/1.08    k1_xboole_0 = sK1 | ~spl7_22),
% 4.97/1.08    inference(avatar_component_clause,[],[f414])).
% 4.97/1.08  fof(f3258,plain,(
% 4.97/1.08    v1_funct_1(k2_funct_1(k1_xboole_0)) | ~v1_funct_2(k1_xboole_0,sK0,sK0) | ~v1_funct_1(k1_xboole_0) | ~spl7_22),
% 4.97/1.08    inference(subsumption_resolution,[],[f3257,f1472])).
% 4.97/1.08  fof(f1472,plain,(
% 4.97/1.08    v3_funct_2(k1_xboole_0,sK0,sK0) | ~spl7_22),
% 4.97/1.08    inference(backward_demodulation,[],[f118,f416])).
% 4.97/1.08  fof(f3257,plain,(
% 4.97/1.08    v1_funct_1(k2_funct_1(k1_xboole_0)) | ~v3_funct_2(k1_xboole_0,sK0,sK0) | ~v1_funct_2(k1_xboole_0,sK0,sK0) | ~v1_funct_1(k1_xboole_0) | ~spl7_22),
% 4.97/1.08    inference(subsumption_resolution,[],[f3256,f126])).
% 4.97/1.08  fof(f126,plain,(
% 4.97/1.08    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 4.97/1.08    inference(cnf_transformation,[],[f4])).
% 4.97/1.08  fof(f4,axiom,(
% 4.97/1.08    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 4.97/1.08    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 4.97/1.08  fof(f3256,plain,(
% 4.97/1.08    v1_funct_1(k2_funct_1(k1_xboole_0)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v3_funct_2(k1_xboole_0,sK0,sK0) | ~v1_funct_2(k1_xboole_0,sK0,sK0) | ~v1_funct_1(k1_xboole_0) | ~spl7_22),
% 4.97/1.08    inference(superposition,[],[f161,f2573])).
% 4.97/1.08  fof(f2573,plain,(
% 4.97/1.08    k2_funct_2(sK0,k1_xboole_0) = k2_funct_1(k1_xboole_0) | ~spl7_22),
% 4.97/1.08    inference(subsumption_resolution,[],[f2572,f130])).
% 4.97/1.08  fof(f2572,plain,(
% 4.97/1.08    k2_funct_2(sK0,k1_xboole_0) = k2_funct_1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~spl7_22),
% 4.97/1.08    inference(subsumption_resolution,[],[f2571,f1471])).
% 4.97/1.08  fof(f2571,plain,(
% 4.97/1.08    k2_funct_2(sK0,k1_xboole_0) = k2_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,sK0,sK0) | ~v1_funct_1(k1_xboole_0) | ~spl7_22),
% 4.97/1.08    inference(subsumption_resolution,[],[f2561,f126])).
% 4.97/1.08  fof(f2561,plain,(
% 4.97/1.08    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k2_funct_2(sK0,k1_xboole_0) = k2_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,sK0,sK0) | ~v1_funct_1(k1_xboole_0) | ~spl7_22),
% 4.97/1.08    inference(resolution,[],[f1472,f160])).
% 4.97/1.08  fof(f161,plain,(
% 4.97/1.08    ( ! [X0,X1] : (v1_funct_1(k2_funct_2(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 4.97/1.08    inference(cnf_transformation,[],[f71])).
% 4.97/1.08  fof(f71,plain,(
% 4.97/1.08    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 4.97/1.08    inference(flattening,[],[f70])).
% 4.97/1.08  fof(f70,plain,(
% 4.97/1.08    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 4.97/1.08    inference(ennf_transformation,[],[f32])).
% 4.97/1.08  fof(f32,axiom,(
% 4.97/1.08    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))))),
% 4.97/1.08    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_2)).
% 4.97/1.08  fof(f4705,plain,(
% 4.97/1.08    ~spl7_22 | ~spl7_30 | spl7_190),
% 4.97/1.08    inference(avatar_contradiction_clause,[],[f4704])).
% 4.97/1.08  fof(f4704,plain,(
% 4.97/1.08    $false | (~spl7_22 | ~spl7_30 | spl7_190)),
% 4.97/1.08    inference(subsumption_resolution,[],[f3972,f4605])).
% 4.97/1.08  fof(f4605,plain,(
% 4.97/1.08    ~m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | spl7_190),
% 4.97/1.08    inference(avatar_component_clause,[],[f4603])).
% 4.97/1.08  fof(f3972,plain,(
% 4.97/1.08    m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl7_22 | ~spl7_30)),
% 4.97/1.08    inference(backward_demodulation,[],[f3358,f606])).
% 4.97/1.08  fof(f3358,plain,(
% 4.97/1.08    m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl7_22),
% 4.97/1.08    inference(forward_demodulation,[],[f2564,f2573])).
% 4.97/1.08  fof(f2564,plain,(
% 4.97/1.08    m1_subset_1(k2_funct_2(sK0,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl7_22),
% 4.97/1.08    inference(subsumption_resolution,[],[f2563,f130])).
% 4.97/1.08  fof(f2563,plain,(
% 4.97/1.08    m1_subset_1(k2_funct_2(sK0,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(k1_xboole_0) | ~spl7_22),
% 4.97/1.08    inference(subsumption_resolution,[],[f2562,f1471])).
% 4.97/1.08  fof(f2562,plain,(
% 4.97/1.08    m1_subset_1(k2_funct_2(sK0,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(k1_xboole_0,sK0,sK0) | ~v1_funct_1(k1_xboole_0) | ~spl7_22),
% 4.97/1.08    inference(subsumption_resolution,[],[f2558,f126])).
% 4.97/1.08  fof(f2558,plain,(
% 4.97/1.08    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | m1_subset_1(k2_funct_2(sK0,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(k1_xboole_0,sK0,sK0) | ~v1_funct_1(k1_xboole_0) | ~spl7_22),
% 4.97/1.08    inference(resolution,[],[f1472,f164])).
% 4.97/1.08  fof(f164,plain,(
% 4.97/1.08    ( ! [X0,X1] : (~v3_funct_2(X1,X0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 4.97/1.08    inference(cnf_transformation,[],[f71])).
% 4.97/1.08  fof(f4474,plain,(
% 4.97/1.08    ~spl7_22 | ~spl7_24 | ~spl7_30 | ~spl7_168),
% 4.97/1.08    inference(avatar_contradiction_clause,[],[f4473])).
% 4.97/1.08  fof(f4473,plain,(
% 4.97/1.08    $false | (~spl7_22 | ~spl7_24 | ~spl7_30 | ~spl7_168)),
% 4.97/1.08    inference(subsumption_resolution,[],[f4472,f126])).
% 4.97/1.08  fof(f4472,plain,(
% 4.97/1.08    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl7_22 | ~spl7_24 | ~spl7_30 | ~spl7_168)),
% 4.97/1.08    inference(resolution,[],[f4283,f208])).
% 4.97/1.08  fof(f4283,plain,(
% 4.97/1.08    ~r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl7_22 | ~spl7_24 | ~spl7_30 | ~spl7_168)),
% 4.97/1.08    inference(forward_demodulation,[],[f4282,f424])).
% 4.97/1.08  fof(f424,plain,(
% 4.97/1.08    k1_xboole_0 = sK2 | ~spl7_24),
% 4.97/1.08    inference(avatar_component_clause,[],[f422])).
% 4.97/1.08  fof(f4282,plain,(
% 4.97/1.08    ~r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,k1_xboole_0) | (~spl7_22 | ~spl7_30 | ~spl7_168)),
% 4.97/1.08    inference(forward_demodulation,[],[f3968,f4253])).
% 4.97/1.08  fof(f4253,plain,(
% 4.97/1.08    k1_xboole_0 = k2_funct_1(k1_xboole_0) | ~spl7_168),
% 4.97/1.08    inference(avatar_component_clause,[],[f4251])).
% 4.97/1.08  fof(f3968,plain,(
% 4.97/1.08    ~r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,k2_funct_1(k1_xboole_0)) | (~spl7_22 | ~spl7_30)),
% 4.97/1.08    inference(backward_demodulation,[],[f3254,f606])).
% 4.97/1.08  fof(f3254,plain,(
% 4.97/1.08    ~r2_relset_1(sK0,sK0,sK2,k2_funct_1(k1_xboole_0)) | ~spl7_22),
% 4.97/1.08    inference(backward_demodulation,[],[f2492,f2573])).
% 4.97/1.08  fof(f2492,plain,(
% 4.97/1.08    ~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,k1_xboole_0)) | ~spl7_22),
% 4.97/1.08    inference(forward_demodulation,[],[f125,f416])).
% 4.97/1.08  fof(f955,plain,(
% 4.97/1.08    ~spl7_21),
% 4.97/1.08    inference(avatar_contradiction_clause,[],[f943])).
% 4.97/1.08  fof(f943,plain,(
% 4.97/1.08    $false | ~spl7_21),
% 4.97/1.08    inference(resolution,[],[f379,f127])).
% 4.97/1.08  fof(f379,plain,(
% 4.97/1.08    ( ! [X2,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2))) ) | ~spl7_21),
% 4.97/1.08    inference(avatar_component_clause,[],[f378])).
% 4.97/1.08  fof(f378,plain,(
% 4.97/1.08    spl7_21 <=> ! [X1,X2] : ~m1_subset_1(X1,k1_zfmisc_1(X2))),
% 4.97/1.08    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).
% 4.97/1.08  fof(f932,plain,(
% 4.97/1.08    spl7_20 | spl7_21),
% 4.97/1.08    inference(avatar_split_clause,[],[f931,f378,f372])).
% 4.97/1.08  fof(f931,plain,(
% 4.97/1.08    ( ! [X6,X5] : (~m1_subset_1(X5,k1_zfmisc_1(X6)) | k1_xboole_0 = k1_relat_1(k1_xboole_0)) )),
% 4.97/1.08    inference(global_subsumption,[],[f929])).
% 4.97/1.08  fof(f929,plain,(
% 4.97/1.08    ( ! [X4,X3] : (k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~m1_subset_1(X3,k1_zfmisc_1(X4))) )),
% 4.97/1.08    inference(subsumption_resolution,[],[f924,f335])).
% 4.97/1.08  fof(f924,plain,(
% 4.97/1.08    ( ! [X4,X3] : (k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~r1_tarski(k1_relat_1(k1_xboole_0),X3) | ~m1_subset_1(X3,k1_zfmisc_1(X4))) )),
% 4.97/1.08    inference(resolution,[],[f335,f172])).
% 4.97/1.08  fof(f172,plain,(
% 4.97/1.08    ( ! [X2,X0,X1] : (~r1_tarski(X1,k3_subset_1(X0,X2)) | k1_xboole_0 = X1 | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 4.97/1.08    inference(cnf_transformation,[],[f73])).
% 4.97/1.08  fof(f73,plain,(
% 4.97/1.08    ! [X0,X1,X2] : (k1_xboole_0 = X1 | ~r1_tarski(X1,k3_subset_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 4.97/1.08    inference(flattening,[],[f72])).
% 4.97/1.08  fof(f72,plain,(
% 4.97/1.08    ! [X0,X1,X2] : ((k1_xboole_0 = X1 | (~r1_tarski(X1,k3_subset_1(X0,X2)) | ~r1_tarski(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 4.97/1.08    inference(ennf_transformation,[],[f3])).
% 4.97/1.08  fof(f3,axiom,(
% 4.97/1.08    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ((r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2)) => k1_xboole_0 = X1))),
% 4.97/1.08    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_subset_1)).
% 4.97/1.08  fof(f813,plain,(
% 4.97/1.08    ~spl7_20 | spl7_22 | ~spl7_23 | ~spl7_28 | ~spl7_33),
% 4.97/1.08    inference(avatar_contradiction_clause,[],[f812])).
% 4.97/1.08  fof(f812,plain,(
% 4.97/1.08    $false | (~spl7_20 | spl7_22 | ~spl7_23 | ~spl7_28 | ~spl7_33)),
% 4.97/1.08    inference(subsumption_resolution,[],[f805,f415])).
% 4.97/1.08  fof(f415,plain,(
% 4.97/1.08    k1_xboole_0 != sK1 | spl7_22),
% 4.97/1.08    inference(avatar_component_clause,[],[f414])).
% 4.97/1.08  fof(f805,plain,(
% 4.97/1.08    k1_xboole_0 = sK1 | (~spl7_20 | ~spl7_23 | ~spl7_28 | ~spl7_33)),
% 4.97/1.08    inference(resolution,[],[f801,f666])).
% 4.97/1.08  fof(f666,plain,(
% 4.97/1.08    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~spl7_33),
% 4.97/1.08    inference(avatar_component_clause,[],[f665])).
% 4.97/1.08  fof(f665,plain,(
% 4.97/1.08    spl7_33 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 4.97/1.08    introduced(avatar_definition,[new_symbols(naming,[spl7_33])])).
% 4.97/1.08  fof(f801,plain,(
% 4.97/1.08    ( ! [X14,X13] : (~m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X14,k1_xboole_0))) | k1_xboole_0 = X13) ) | (~spl7_20 | ~spl7_23 | ~spl7_28 | ~spl7_33)),
% 4.97/1.08    inference(resolution,[],[f760,f494])).
% 4.97/1.08  fof(f760,plain,(
% 4.97/1.08    ( ! [X6,X4,X5] : (~v1_xboole_0(X6) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) | k1_xboole_0 = X4) ) | (~spl7_20 | ~spl7_23 | ~spl7_33)),
% 4.97/1.08    inference(resolution,[],[f750,f149])).
% 4.97/1.08  fof(f750,plain,(
% 4.97/1.08    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) ) | (~spl7_20 | ~spl7_23 | ~spl7_33)),
% 4.97/1.08    inference(subsumption_resolution,[],[f749,f381])).
% 4.97/1.08  fof(f749,plain,(
% 4.97/1.08    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(k1_xboole_0,X0) | ~v1_xboole_0(X0)) ) | (~spl7_20 | ~spl7_23 | ~spl7_33)),
% 4.97/1.08    inference(subsumption_resolution,[],[f747,f381])).
% 4.97/1.08  fof(f747,plain,(
% 4.97/1.08    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(k1_xboole_0,k1_xboole_0) | ~r1_tarski(k1_xboole_0,X0) | ~v1_xboole_0(X0)) ) | (~spl7_23 | ~spl7_33)),
% 4.97/1.08    inference(resolution,[],[f666,f702])).
% 4.97/1.08  fof(f702,plain,(
% 4.97/1.08    ( ! [X2,X0,X1] : (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | k1_xboole_0 = X0 | ~r1_tarski(X1,k1_xboole_0) | ~r1_tarski(X2,X0) | ~v1_xboole_0(X0)) ) | ~spl7_23),
% 4.97/1.08    inference(resolution,[],[f419,f197])).
% 4.97/1.08  fof(f419,plain,(
% 4.97/1.08    ( ! [X1] : (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) | ~v1_xboole_0(X1) | k1_xboole_0 = X1) ) | ~spl7_23),
% 4.97/1.08    inference(avatar_component_clause,[],[f418])).
% 4.97/1.08  fof(f676,plain,(
% 4.97/1.08    ~spl7_30 | spl7_33),
% 4.97/1.08    inference(avatar_contradiction_clause,[],[f675])).
% 4.97/1.08  fof(f675,plain,(
% 4.97/1.08    $false | (~spl7_30 | spl7_33)),
% 4.97/1.08    inference(subsumption_resolution,[],[f667,f673])).
% 4.97/1.08  fof(f673,plain,(
% 4.97/1.08    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~spl7_30),
% 4.97/1.08    inference(forward_demodulation,[],[f119,f606])).
% 4.97/1.08  fof(f667,plain,(
% 4.97/1.08    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | spl7_33),
% 4.97/1.08    inference(avatar_component_clause,[],[f665])).
% 4.97/1.08  fof(f506,plain,(
% 4.97/1.08    spl7_28),
% 4.97/1.08    inference(avatar_contradiction_clause,[],[f505])).
% 4.97/1.08  fof(f505,plain,(
% 4.97/1.08    $false | spl7_28),
% 4.97/1.08    inference(resolution,[],[f503,f168])).
% 4.97/1.08  fof(f168,plain,(
% 4.97/1.08    ( ! [X0,X1] : (v1_xboole_0(sK6(X0,X1))) )),
% 4.97/1.08    inference(cnf_transformation,[],[f113])).
% 4.97/1.08  fof(f113,plain,(
% 4.97/1.08    ! [X0,X1] : (v5_relat_1(sK6(X0,X1),X1) & v4_relat_1(sK6(X0,X1),X0) & v1_relat_1(sK6(X0,X1)) & v1_xboole_0(sK6(X0,X1)) & m1_subset_1(sK6(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.97/1.08    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f34,f112])).
% 4.97/1.08  fof(f112,plain,(
% 4.97/1.08    ! [X1,X0] : (? [X2] : (v5_relat_1(X2,X1) & v4_relat_1(X2,X0) & v1_relat_1(X2) & v1_xboole_0(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (v5_relat_1(sK6(X0,X1),X1) & v4_relat_1(sK6(X0,X1),X0) & v1_relat_1(sK6(X0,X1)) & v1_xboole_0(sK6(X0,X1)) & m1_subset_1(sK6(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 4.97/1.08    introduced(choice_axiom,[])).
% 4.97/1.08  fof(f34,axiom,(
% 4.97/1.08    ! [X0,X1] : ? [X2] : (v5_relat_1(X2,X1) & v4_relat_1(X2,X0) & v1_relat_1(X2) & v1_xboole_0(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.97/1.08    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_relset_1)).
% 4.97/1.08  fof(f503,plain,(
% 4.97/1.08    ( ! [X2] : (~v1_xboole_0(X2)) ) | spl7_28),
% 4.97/1.08    inference(subsumption_resolution,[],[f501,f126])).
% 4.97/1.08  fof(f501,plain,(
% 4.97/1.08    ( ! [X2,X1] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_xboole_0(X2)) ) | spl7_28),
% 4.97/1.08    inference(resolution,[],[f495,f149])).
% 4.97/1.08  fof(f495,plain,(
% 4.97/1.08    ~v1_xboole_0(k1_xboole_0) | spl7_28),
% 4.97/1.08    inference(avatar_component_clause,[],[f493])).
% 4.97/1.08  fof(f308,plain,(
% 4.97/1.08    spl7_7),
% 4.97/1.08    inference(avatar_contradiction_clause,[],[f306])).
% 4.97/1.08  fof(f306,plain,(
% 4.97/1.08    $false | spl7_7),
% 4.97/1.08    inference(resolution,[],[f302,f123])).
% 4.97/1.08  fof(f302,plain,(
% 4.97/1.08    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl7_7),
% 4.97/1.08    inference(resolution,[],[f271,f173])).
% 4.97/1.08  fof(f173,plain,(
% 4.97/1.08    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.97/1.08    inference(cnf_transformation,[],[f74])).
% 4.97/1.08  fof(f74,plain,(
% 4.97/1.08    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.97/1.08    inference(ennf_transformation,[],[f21])).
% 4.97/1.08  fof(f21,axiom,(
% 4.97/1.08    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 4.97/1.08    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 4.97/1.08  fof(f271,plain,(
% 4.97/1.08    ~v1_relat_1(sK2) | spl7_7),
% 4.97/1.08    inference(avatar_component_clause,[],[f269])).
% 4.97/1.08  % SZS output end Proof for theBenchmark
% 4.97/1.08  % (13391)------------------------------
% 4.97/1.08  % (13391)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.97/1.08  % (13391)Termination reason: Refutation
% 4.97/1.08  
% 4.97/1.08  % (13391)Memory used [KB]: 14583
% 4.97/1.08  % (13391)Time elapsed: 0.668 s
% 4.97/1.08  % (13391)------------------------------
% 4.97/1.08  % (13391)------------------------------
% 4.97/1.08  % (13379)Success in time 0.73 s
%------------------------------------------------------------------------------
