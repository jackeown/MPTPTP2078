%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:39 EST 2020

% Result     : Theorem 1.48s
% Output     : Refutation 1.48s
% Verified   : 
% Statistics : Number of formulae       :  180 ( 929 expanded)
%              Number of leaves         :   23 ( 292 expanded)
%              Depth                    :   24
%              Number of atoms          :  699 (9322 expanded)
%              Number of equality atoms :  195 (3194 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f704,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f223,f361,f420,f703])).

fof(f703,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(avatar_contradiction_clause,[],[f702])).

fof(f702,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f701,f75])).

fof(f75,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,
    ( k2_funct_1(sK2) != sK3
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & v2_funct_1(sK2)
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    & sK1 = k2_relset_1(sK0,sK1,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_2(sK3,sK1,sK0)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f29,f59,f58])).

fof(f58,plain,
    ( ? [X0,X1,X2] :
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
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( k2_funct_1(sK2) != X3
          & k1_xboole_0 != sK1
          & k1_xboole_0 != sK0
          & v2_funct_1(sK2)
          & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
          & sK1 = k2_relset_1(sK0,sK1,sK2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
          & v1_funct_2(X3,sK1,sK0)
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,
    ( ? [X3] :
        ( k2_funct_1(sK2) != X3
        & k1_xboole_0 != sK1
        & k1_xboole_0 != sK0
        & v2_funct_1(sK2)
        & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
        & sK1 = k2_relset_1(sK0,sK1,sK2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        & v1_funct_2(X3,sK1,sK0)
        & v1_funct_1(X3) )
   => ( k2_funct_1(sK2) != sK3
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0
      & v2_funct_1(sK2)
      & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
      & sK1 = k2_relset_1(sK0,sK1,sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      & v1_funct_2(sK3,sK1,sK0)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f26])).

fof(f26,negated_conjecture,(
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
    inference(negated_conjecture,[],[f25])).

fof(f25,conjecture,(
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

fof(f701,plain,
    ( k2_funct_1(sK2) = sK3
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(backward_demodulation,[],[f425,f699])).

fof(f699,plain,
    ( sK3 = k5_relat_1(k6_partfun1(sK1),k2_funct_1(sK2))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(forward_demodulation,[],[f698,f526])).

fof(f526,plain,
    ( sK3 = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(forward_demodulation,[],[f525,f427])).

fof(f427,plain,
    ( sK3 = k5_relat_1(k6_partfun1(sK1),sK3)
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(backward_demodulation,[],[f149,f408])).

fof(f408,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f407,f116])).

fof(f116,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f105,f95])).

fof(f95,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f105,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f407,plain,
    ( k1_relat_1(sK3) = k1_relat_1(k6_partfun1(sK1))
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f380,f218])).

fof(f218,plain,
    ( k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f216])).

fof(f216,plain,
    ( spl5_1
  <=> k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f380,plain,
    ( k1_relat_1(sK3) = k1_relat_1(k5_relat_1(sK3,k2_funct_1(sK3)))
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f379,f139])).

fof(f139,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f69,f101])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f69,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f60])).

fof(f379,plain,
    ( k1_relat_1(sK3) = k1_relat_1(k5_relat_1(sK3,k2_funct_1(sK3)))
    | ~ v1_relat_1(sK3)
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f370,f67])).

fof(f67,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f60])).

fof(f370,plain,
    ( k1_relat_1(sK3) = k1_relat_1(k5_relat_1(sK3,k2_funct_1(sK3)))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl5_2 ),
    inference(resolution,[],[f221,f80])).

fof(f80,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
          & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_funct_1)).

fof(f221,plain,
    ( v2_funct_1(sK3)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f220])).

fof(f220,plain,
    ( spl5_2
  <=> v2_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f149,plain,(
    sK3 = k5_relat_1(k6_partfun1(k1_relat_1(sK3)),sK3) ),
    inference(resolution,[],[f139,f113])).

fof(f113,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0 ) ),
    inference(definition_unfolding,[],[f103,f95])).

fof(f103,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).

fof(f525,plain,
    ( k5_relat_1(k6_partfun1(sK1),sK3) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0))
    | ~ spl5_3 ),
    inference(forward_demodulation,[],[f522,f173])).

fof(f173,plain,(
    k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
    inference(subsumption_resolution,[],[f172,f64])).

fof(f64,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f60])).

fof(f172,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f171,f65])).

fof(f65,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f60])).

fof(f171,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f170,f66])).

fof(f66,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f60])).

fof(f170,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f169,f72])).

fof(f72,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f60])).

fof(f169,plain,
    ( ~ v2_funct_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f157,f74])).

fof(f74,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f60])).

fof(f157,plain,
    ( k1_xboole_0 = sK1
    | ~ v2_funct_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(trivial_inequality_removal,[],[f156])).

fof(f156,plain,
    ( sK1 != sK1
    | k1_xboole_0 = sK1
    | ~ v2_funct_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(superposition,[],[f77,f70])).

fof(f70,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f60])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
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
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
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

fof(f522,plain,
    ( k5_relat_1(k5_relat_1(k2_funct_1(sK2),sK2),sK3) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0))
    | ~ spl5_3 ),
    inference(resolution,[],[f516,f411])).

fof(f411,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f410])).

fof(f410,plain,
    ( spl5_3
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f516,plain,(
    ! [X7] :
      ( ~ v1_relat_1(X7)
      | k5_relat_1(k5_relat_1(X7,sK2),sK3) = k5_relat_1(X7,k6_partfun1(sK0)) ) ),
    inference(forward_demodulation,[],[f506,f288])).

fof(f288,plain,(
    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) ),
    inference(global_subsumption,[],[f285,f287])).

fof(f287,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f286,f112])).

fof(f112,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f102,f95])).

fof(f102,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

fof(f286,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f274,f92])).

fof(f92,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f274,plain,(
    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0)) ),
    inference(backward_demodulation,[],[f71,f245])).

fof(f245,plain,(
    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f242,f67])).

fof(f242,plain,
    ( ~ v1_funct_1(sK3)
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(resolution,[],[f137,f69])).

fof(f137,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X0)
      | k1_partfun1(sK0,sK1,X1,X2,sK2,X0) = k5_relat_1(sK2,X0) ) ),
    inference(subsumption_resolution,[],[f135,f64])).

fof(f135,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X0)
      | k1_partfun1(sK0,sK1,X1,X2,sK2,X0) = k5_relat_1(sK2,X0)
      | ~ v1_funct_1(sK2) ) ),
    inference(resolution,[],[f66,f98])).

fof(f98,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f71,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f60])).

fof(f285,plain,(
    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f284,f64])).

fof(f284,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f283,f66])).

fof(f283,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f282,f67])).

fof(f282,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f277,f69])).

fof(f277,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(superposition,[],[f97,f245])).

fof(f97,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f506,plain,(
    ! [X7] :
      ( ~ v1_relat_1(X7)
      | k5_relat_1(k5_relat_1(X7,sK2),sK3) = k5_relat_1(X7,k5_relat_1(sK2,sK3)) ) ),
    inference(resolution,[],[f147,f139])).

fof(f147,plain,(
    ! [X2,X3] :
      ( ~ v1_relat_1(X2)
      | ~ v1_relat_1(X3)
      | k5_relat_1(k5_relat_1(X3,sK2),X2) = k5_relat_1(X3,k5_relat_1(sK2,X2)) ) ),
    inference(resolution,[],[f133,f99])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

fof(f133,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f66,f101])).

fof(f698,plain,
    ( k5_relat_1(k6_partfun1(sK1),k2_funct_1(sK2)) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0))
    | ~ spl5_3 ),
    inference(forward_demodulation,[],[f697,f173])).

fof(f697,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k5_relat_1(k5_relat_1(k2_funct_1(sK2),sK2),k2_funct_1(sK2))
    | ~ spl5_3 ),
    inference(forward_demodulation,[],[f690,f168])).

fof(f168,plain,(
    k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f167,f64])).

fof(f167,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f166,f65])).

fof(f166,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f165,f66])).

fof(f165,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f164,f72])).

fof(f164,plain,
    ( ~ v2_funct_1(sK2)
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f158,f74])).

fof(f158,plain,
    ( k1_xboole_0 = sK1
    | ~ v2_funct_1(sK2)
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(trivial_inequality_removal,[],[f155])).

fof(f155,plain,
    ( sK1 != sK1
    | k1_xboole_0 = sK1
    | ~ v2_funct_1(sK2)
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(superposition,[],[f76,f70])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f690,plain,
    ( k5_relat_1(k5_relat_1(k2_funct_1(sK2),sK2),k2_funct_1(sK2)) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,k2_funct_1(sK2)))
    | ~ spl5_3 ),
    inference(resolution,[],[f514,f411])).

fof(f514,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(k5_relat_1(X0,sK2),X0) = k5_relat_1(X0,k5_relat_1(sK2,X0)) ) ),
    inference(factoring,[],[f147])).

fof(f425,plain,
    ( k2_funct_1(sK2) = k5_relat_1(k6_partfun1(sK1),k2_funct_1(sK2))
    | ~ spl5_3 ),
    inference(forward_demodulation,[],[f421,f212])).

fof(f212,plain,(
    sK1 = k1_relat_1(k2_funct_1(sK2)) ),
    inference(forward_demodulation,[],[f211,f205])).

fof(f205,plain,(
    sK1 = k2_relat_1(sK2) ),
    inference(forward_demodulation,[],[f134,f70])).

fof(f134,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f66,f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f211,plain,(
    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f127,f133])).

fof(f127,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f121,f64])).

fof(f121,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f72,f82])).

fof(f82,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f421,plain,
    ( k2_funct_1(sK2) = k5_relat_1(k6_partfun1(k1_relat_1(k2_funct_1(sK2))),k2_funct_1(sK2))
    | ~ spl5_3 ),
    inference(resolution,[],[f411,f113])).

fof(f420,plain,(
    spl5_3 ),
    inference(avatar_contradiction_clause,[],[f419])).

fof(f419,plain,
    ( $false
    | spl5_3 ),
    inference(subsumption_resolution,[],[f418,f133])).

fof(f418,plain,
    ( ~ v1_relat_1(sK2)
    | spl5_3 ),
    inference(subsumption_resolution,[],[f417,f64])).

fof(f417,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl5_3 ),
    inference(resolution,[],[f412,f84])).

fof(f84,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f412,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | spl5_3 ),
    inference(avatar_component_clause,[],[f410])).

fof(f361,plain,(
    spl5_2 ),
    inference(avatar_contradiction_clause,[],[f360])).

fof(f360,plain,
    ( $false
    | spl5_2 ),
    inference(subsumption_resolution,[],[f359,f111])).

fof(f111,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f91,f95])).

fof(f91,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_funct_1)).

fof(f359,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | spl5_2 ),
    inference(forward_demodulation,[],[f358,f291])).

fof(f291,plain,(
    k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(backward_demodulation,[],[f245,f288])).

fof(f358,plain,
    ( ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | spl5_2 ),
    inference(subsumption_resolution,[],[f357,f67])).

fof(f357,plain,
    ( ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | ~ v1_funct_1(sK3)
    | spl5_2 ),
    inference(subsumption_resolution,[],[f356,f73])).

fof(f73,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f60])).

fof(f356,plain,
    ( ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | k1_xboole_0 = sK0
    | ~ v1_funct_1(sK3)
    | spl5_2 ),
    inference(subsumption_resolution,[],[f355,f69])).

fof(f355,plain,
    ( ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | k1_xboole_0 = sK0
    | ~ v1_funct_1(sK3)
    | spl5_2 ),
    inference(subsumption_resolution,[],[f354,f222])).

fof(f222,plain,
    ( ~ v2_funct_1(sK3)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f220])).

fof(f354,plain,
    ( v2_funct_1(sK3)
    | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | k1_xboole_0 = sK0
    | ~ v1_funct_1(sK3) ),
    inference(resolution,[],[f163,f68])).

fof(f68,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f60])).

fof(f163,plain,(
    ! [X2,X3] :
      ( ~ v1_funct_2(X3,sK1,X2)
      | v2_funct_1(X3)
      | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X2,sK2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2)))
      | k1_xboole_0 = X2
      | ~ v1_funct_1(X3) ) ),
    inference(subsumption_resolution,[],[f162,f64])).

fof(f162,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 = X2
      | v2_funct_1(X3)
      | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X2,sK2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2)))
      | ~ v1_funct_2(X3,sK1,X2)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_1(sK2) ) ),
    inference(subsumption_resolution,[],[f161,f65])).

fof(f161,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 = X2
      | v2_funct_1(X3)
      | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X2,sK2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2)))
      | ~ v1_funct_2(X3,sK1,X2)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(sK2,sK0,sK1)
      | ~ v1_funct_1(sK2) ) ),
    inference(subsumption_resolution,[],[f159,f66])).

fof(f159,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 = X2
      | v2_funct_1(X3)
      | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X2,sK2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2)))
      | ~ v1_funct_2(X3,sK1,X2)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_2(sK2,sK0,sK1)
      | ~ v1_funct_1(sK2) ) ),
    inference(trivial_inequality_removal,[],[f154])).

fof(f154,plain,(
    ! [X2,X3] :
      ( sK1 != sK1
      | k1_xboole_0 = X2
      | v2_funct_1(X3)
      | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X2,sK2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2)))
      | ~ v1_funct_2(X3,sK1,X2)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_2(sK2,sK0,sK1)
      | ~ v1_funct_1(sK2) ) ),
    inference(superposition,[],[f88,f70])).

fof(f88,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X3) != X1
      | k1_xboole_0 = X2
      | v2_funct_1(X4)
      | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X4,X1,X2)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

fof(f40,plain,(
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
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
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

fof(f223,plain,
    ( spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f200,f220,f216])).

fof(f200,plain,
    ( ~ v2_funct_1(sK3)
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) ),
    inference(subsumption_resolution,[],[f199,f67])).

fof(f199,plain,
    ( ~ v2_funct_1(sK3)
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f198,f68])).

fof(f198,plain,
    ( ~ v2_funct_1(sK3)
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f197,f69])).

fof(f197,plain,
    ( ~ v2_funct_1(sK3)
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f188,f73])).

fof(f188,plain,
    ( k1_xboole_0 = sK0
    | ~ v2_funct_1(sK3)
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(trivial_inequality_removal,[],[f185])).

fof(f185,plain,
    ( sK0 != sK0
    | k1_xboole_0 = sK0
    | ~ v2_funct_1(sK3)
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(superposition,[],[f76,f182])).

fof(f182,plain,(
    sK0 = k2_relset_1(sK1,sK0,sK3) ),
    inference(subsumption_resolution,[],[f181,f67])).

fof(f181,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f180,f68])).

fof(f180,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f179,f69])).

fof(f179,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f178,f64])).

fof(f178,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f177,f65])).

fof(f177,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f175,f66])).

fof(f175,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(resolution,[],[f71,f94])).

fof(f94,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | k2_relset_1(X0,X1,X2) = X1
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
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
    inference(flattening,[],[f45])).

fof(f45,plain,(
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
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
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
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n001.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:08:00 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.51  % (20565)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.51  % (20556)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.51  % (20573)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.51  % (20557)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.52  % (20560)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.52  % (20562)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.52  % (20558)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  % (20575)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.53  % (20554)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.53  % (20567)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.53  % (20555)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.53  % (20552)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.53  % (20577)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.54  % (20559)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.54  % (20572)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.54  % (20569)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.54  % (20561)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.54  % (20568)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.54  % (20579)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.54  % (20564)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.54  % (20566)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.32/0.55  % (20571)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.32/0.55  % (20553)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.32/0.55  % (20576)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.32/0.55  % (20570)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.32/0.55  % (20568)Refutation not found, incomplete strategy% (20568)------------------------------
% 1.32/0.55  % (20568)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.55  % (20578)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.32/0.55  % (20563)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.32/0.55  % (20574)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.32/0.56  % (20580)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.32/0.56  % (20581)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.48/0.57  % (20568)Termination reason: Refutation not found, incomplete strategy
% 1.48/0.57  
% 1.48/0.57  % (20568)Memory used [KB]: 10746
% 1.48/0.57  % (20568)Time elapsed: 0.124 s
% 1.48/0.57  % (20568)------------------------------
% 1.48/0.57  % (20568)------------------------------
% 1.48/0.61  % (20576)Refutation found. Thanks to Tanya!
% 1.48/0.61  % SZS status Theorem for theBenchmark
% 1.48/0.61  % SZS output start Proof for theBenchmark
% 1.48/0.61  fof(f704,plain,(
% 1.48/0.61    $false),
% 1.48/0.61    inference(avatar_sat_refutation,[],[f223,f361,f420,f703])).
% 1.48/0.61  fof(f703,plain,(
% 1.48/0.61    ~spl5_1 | ~spl5_2 | ~spl5_3),
% 1.48/0.61    inference(avatar_contradiction_clause,[],[f702])).
% 1.48/0.61  fof(f702,plain,(
% 1.48/0.61    $false | (~spl5_1 | ~spl5_2 | ~spl5_3)),
% 1.48/0.61    inference(subsumption_resolution,[],[f701,f75])).
% 1.48/0.61  fof(f75,plain,(
% 1.48/0.61    k2_funct_1(sK2) != sK3),
% 1.48/0.61    inference(cnf_transformation,[],[f60])).
% 1.48/0.61  fof(f60,plain,(
% 1.48/0.61    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 1.48/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f29,f59,f58])).
% 1.48/0.61  fof(f58,plain,(
% 1.48/0.61    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 1.48/0.61    introduced(choice_axiom,[])).
% 1.48/0.61  fof(f59,plain,(
% 1.48/0.61    ? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) => (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3))),
% 1.48/0.61    introduced(choice_axiom,[])).
% 1.48/0.61  fof(f29,plain,(
% 1.48/0.61    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.48/0.61    inference(flattening,[],[f28])).
% 1.48/0.61  fof(f28,plain,(
% 1.48/0.61    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.48/0.61    inference(ennf_transformation,[],[f26])).
% 1.48/0.61  fof(f26,negated_conjecture,(
% 1.48/0.61    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.48/0.61    inference(negated_conjecture,[],[f25])).
% 1.48/0.61  fof(f25,conjecture,(
% 1.48/0.61    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.48/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).
% 1.48/0.61  fof(f701,plain,(
% 1.48/0.61    k2_funct_1(sK2) = sK3 | (~spl5_1 | ~spl5_2 | ~spl5_3)),
% 1.48/0.61    inference(backward_demodulation,[],[f425,f699])).
% 1.48/0.61  fof(f699,plain,(
% 1.48/0.61    sK3 = k5_relat_1(k6_partfun1(sK1),k2_funct_1(sK2)) | (~spl5_1 | ~spl5_2 | ~spl5_3)),
% 1.48/0.61    inference(forward_demodulation,[],[f698,f526])).
% 1.48/0.61  fof(f526,plain,(
% 1.48/0.61    sK3 = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) | (~spl5_1 | ~spl5_2 | ~spl5_3)),
% 1.48/0.61    inference(forward_demodulation,[],[f525,f427])).
% 1.48/0.61  fof(f427,plain,(
% 1.48/0.61    sK3 = k5_relat_1(k6_partfun1(sK1),sK3) | (~spl5_1 | ~spl5_2)),
% 1.48/0.61    inference(backward_demodulation,[],[f149,f408])).
% 1.48/0.61  fof(f408,plain,(
% 1.48/0.61    sK1 = k1_relat_1(sK3) | (~spl5_1 | ~spl5_2)),
% 1.48/0.61    inference(forward_demodulation,[],[f407,f116])).
% 1.48/0.61  fof(f116,plain,(
% 1.48/0.61    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 1.48/0.61    inference(definition_unfolding,[],[f105,f95])).
% 1.48/0.61  fof(f95,plain,(
% 1.48/0.61    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.48/0.61    inference(cnf_transformation,[],[f21])).
% 1.48/0.61  fof(f21,axiom,(
% 1.48/0.61    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.48/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.48/0.61  fof(f105,plain,(
% 1.48/0.61    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.48/0.61    inference(cnf_transformation,[],[f7])).
% 1.48/0.61  fof(f7,axiom,(
% 1.48/0.61    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.48/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 1.48/0.61  fof(f407,plain,(
% 1.48/0.61    k1_relat_1(sK3) = k1_relat_1(k6_partfun1(sK1)) | (~spl5_1 | ~spl5_2)),
% 1.48/0.61    inference(forward_demodulation,[],[f380,f218])).
% 1.48/0.61  fof(f218,plain,(
% 1.48/0.61    k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~spl5_1),
% 1.48/0.61    inference(avatar_component_clause,[],[f216])).
% 1.48/0.61  fof(f216,plain,(
% 1.48/0.61    spl5_1 <=> k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))),
% 1.48/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.48/0.61  fof(f380,plain,(
% 1.48/0.61    k1_relat_1(sK3) = k1_relat_1(k5_relat_1(sK3,k2_funct_1(sK3))) | ~spl5_2),
% 1.48/0.61    inference(subsumption_resolution,[],[f379,f139])).
% 1.48/0.61  fof(f139,plain,(
% 1.48/0.61    v1_relat_1(sK3)),
% 1.48/0.61    inference(resolution,[],[f69,f101])).
% 1.48/0.61  fof(f101,plain,(
% 1.48/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.48/0.61    inference(cnf_transformation,[],[f53])).
% 1.48/0.61  fof(f53,plain,(
% 1.48/0.61    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.48/0.61    inference(ennf_transformation,[],[f15])).
% 1.48/0.61  fof(f15,axiom,(
% 1.48/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.48/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.48/0.61  fof(f69,plain,(
% 1.48/0.61    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.48/0.61    inference(cnf_transformation,[],[f60])).
% 1.48/0.61  fof(f379,plain,(
% 1.48/0.61    k1_relat_1(sK3) = k1_relat_1(k5_relat_1(sK3,k2_funct_1(sK3))) | ~v1_relat_1(sK3) | ~spl5_2),
% 1.48/0.61    inference(subsumption_resolution,[],[f370,f67])).
% 1.48/0.61  fof(f67,plain,(
% 1.48/0.61    v1_funct_1(sK3)),
% 1.48/0.61    inference(cnf_transformation,[],[f60])).
% 1.48/0.61  fof(f370,plain,(
% 1.48/0.61    k1_relat_1(sK3) = k1_relat_1(k5_relat_1(sK3,k2_funct_1(sK3))) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl5_2),
% 1.48/0.61    inference(resolution,[],[f221,f80])).
% 1.48/0.61  fof(f80,plain,(
% 1.48/0.61    ( ! [X0] : (~v2_funct_1(X0) | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.48/0.61    inference(cnf_transformation,[],[f35])).
% 1.48/0.61  fof(f35,plain,(
% 1.48/0.61    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.48/0.61    inference(flattening,[],[f34])).
% 1.48/0.61  fof(f34,plain,(
% 1.48/0.61    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.48/0.61    inference(ennf_transformation,[],[f13])).
% 1.48/0.61  fof(f13,axiom,(
% 1.48/0.61    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))))))),
% 1.48/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_funct_1)).
% 1.48/0.61  fof(f221,plain,(
% 1.48/0.61    v2_funct_1(sK3) | ~spl5_2),
% 1.48/0.61    inference(avatar_component_clause,[],[f220])).
% 1.48/0.61  fof(f220,plain,(
% 1.48/0.61    spl5_2 <=> v2_funct_1(sK3)),
% 1.48/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.48/0.61  fof(f149,plain,(
% 1.48/0.61    sK3 = k5_relat_1(k6_partfun1(k1_relat_1(sK3)),sK3)),
% 1.48/0.61    inference(resolution,[],[f139,f113])).
% 1.48/0.61  fof(f113,plain,(
% 1.48/0.61    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0) )),
% 1.48/0.61    inference(definition_unfolding,[],[f103,f95])).
% 1.48/0.61  fof(f103,plain,(
% 1.48/0.61    ( ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0)) )),
% 1.48/0.61    inference(cnf_transformation,[],[f54])).
% 1.48/0.61  fof(f54,plain,(
% 1.48/0.61    ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0))),
% 1.48/0.61    inference(ennf_transformation,[],[f8])).
% 1.48/0.61  fof(f8,axiom,(
% 1.48/0.61    ! [X0] : (v1_relat_1(X0) => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0)),
% 1.48/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).
% 1.48/0.61  fof(f525,plain,(
% 1.48/0.61    k5_relat_1(k6_partfun1(sK1),sK3) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) | ~spl5_3),
% 1.48/0.61    inference(forward_demodulation,[],[f522,f173])).
% 1.48/0.61  fof(f173,plain,(
% 1.48/0.61    k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)),
% 1.48/0.61    inference(subsumption_resolution,[],[f172,f64])).
% 1.48/0.61  fof(f64,plain,(
% 1.48/0.61    v1_funct_1(sK2)),
% 1.48/0.61    inference(cnf_transformation,[],[f60])).
% 1.48/0.61  fof(f172,plain,(
% 1.48/0.61    k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) | ~v1_funct_1(sK2)),
% 1.48/0.61    inference(subsumption_resolution,[],[f171,f65])).
% 1.48/0.61  fof(f65,plain,(
% 1.48/0.61    v1_funct_2(sK2,sK0,sK1)),
% 1.48/0.61    inference(cnf_transformation,[],[f60])).
% 1.48/0.61  fof(f171,plain,(
% 1.48/0.61    k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 1.48/0.61    inference(subsumption_resolution,[],[f170,f66])).
% 1.48/0.61  fof(f66,plain,(
% 1.48/0.61    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.48/0.61    inference(cnf_transformation,[],[f60])).
% 1.48/0.61  fof(f170,plain,(
% 1.48/0.61    k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 1.48/0.61    inference(subsumption_resolution,[],[f169,f72])).
% 1.48/0.61  fof(f72,plain,(
% 1.48/0.61    v2_funct_1(sK2)),
% 1.48/0.61    inference(cnf_transformation,[],[f60])).
% 1.48/0.61  fof(f169,plain,(
% 1.48/0.61    ~v2_funct_1(sK2) | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 1.48/0.61    inference(subsumption_resolution,[],[f157,f74])).
% 1.48/0.61  fof(f74,plain,(
% 1.48/0.61    k1_xboole_0 != sK1),
% 1.48/0.61    inference(cnf_transformation,[],[f60])).
% 1.48/0.61  fof(f157,plain,(
% 1.48/0.61    k1_xboole_0 = sK1 | ~v2_funct_1(sK2) | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 1.48/0.61    inference(trivial_inequality_removal,[],[f156])).
% 1.48/0.61  fof(f156,plain,(
% 1.48/0.61    sK1 != sK1 | k1_xboole_0 = sK1 | ~v2_funct_1(sK2) | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 1.48/0.61    inference(superposition,[],[f77,f70])).
% 1.48/0.61  fof(f70,plain,(
% 1.48/0.61    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 1.48/0.61    inference(cnf_transformation,[],[f60])).
% 1.48/0.61  fof(f77,plain,(
% 1.48/0.61    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.48/0.61    inference(cnf_transformation,[],[f31])).
% 1.48/0.61  fof(f31,plain,(
% 1.48/0.61    ! [X0,X1,X2] : ((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.48/0.61    inference(flattening,[],[f30])).
% 1.48/0.61  fof(f30,plain,(
% 1.48/0.61    ! [X0,X1,X2] : ((((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.48/0.61    inference(ennf_transformation,[],[f24])).
% 1.48/0.61  fof(f24,axiom,(
% 1.48/0.61    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1)))),
% 1.48/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).
% 1.48/0.61  fof(f522,plain,(
% 1.48/0.61    k5_relat_1(k5_relat_1(k2_funct_1(sK2),sK2),sK3) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) | ~spl5_3),
% 1.48/0.61    inference(resolution,[],[f516,f411])).
% 1.48/0.61  fof(f411,plain,(
% 1.48/0.61    v1_relat_1(k2_funct_1(sK2)) | ~spl5_3),
% 1.48/0.61    inference(avatar_component_clause,[],[f410])).
% 1.48/0.61  fof(f410,plain,(
% 1.48/0.61    spl5_3 <=> v1_relat_1(k2_funct_1(sK2))),
% 1.48/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.48/0.61  fof(f516,plain,(
% 1.48/0.61    ( ! [X7] : (~v1_relat_1(X7) | k5_relat_1(k5_relat_1(X7,sK2),sK3) = k5_relat_1(X7,k6_partfun1(sK0))) )),
% 1.48/0.61    inference(forward_demodulation,[],[f506,f288])).
% 1.48/0.61  fof(f288,plain,(
% 1.48/0.61    k6_partfun1(sK0) = k5_relat_1(sK2,sK3)),
% 1.48/0.61    inference(global_subsumption,[],[f285,f287])).
% 1.48/0.61  fof(f287,plain,(
% 1.48/0.61    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.48/0.61    inference(subsumption_resolution,[],[f286,f112])).
% 1.48/0.61  fof(f112,plain,(
% 1.48/0.61    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.48/0.61    inference(definition_unfolding,[],[f102,f95])).
% 1.48/0.61  fof(f102,plain,(
% 1.48/0.61    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.48/0.61    inference(cnf_transformation,[],[f18])).
% 1.48/0.61  fof(f18,axiom,(
% 1.48/0.61    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 1.48/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).
% 1.48/0.61  fof(f286,plain,(
% 1.48/0.61    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.48/0.61    inference(resolution,[],[f274,f92])).
% 1.48/0.61  fof(f92,plain,(
% 1.48/0.61    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.48/0.61    inference(cnf_transformation,[],[f61])).
% 1.48/0.61  fof(f61,plain,(
% 1.48/0.61    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.48/0.61    inference(nnf_transformation,[],[f44])).
% 1.48/0.61  fof(f44,plain,(
% 1.48/0.61    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.48/0.61    inference(flattening,[],[f43])).
% 1.48/0.61  fof(f43,plain,(
% 1.48/0.61    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.48/0.61    inference(ennf_transformation,[],[f17])).
% 1.48/0.61  fof(f17,axiom,(
% 1.48/0.61    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.48/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.48/0.61  fof(f274,plain,(
% 1.48/0.61    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0))),
% 1.48/0.61    inference(backward_demodulation,[],[f71,f245])).
% 1.48/0.61  fof(f245,plain,(
% 1.48/0.61    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)),
% 1.48/0.61    inference(subsumption_resolution,[],[f242,f67])).
% 1.48/0.61  fof(f242,plain,(
% 1.48/0.61    ~v1_funct_1(sK3) | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)),
% 1.48/0.61    inference(resolution,[],[f137,f69])).
% 1.48/0.61  fof(f137,plain,(
% 1.48/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X0) | k1_partfun1(sK0,sK1,X1,X2,sK2,X0) = k5_relat_1(sK2,X0)) )),
% 1.48/0.61    inference(subsumption_resolution,[],[f135,f64])).
% 1.48/0.61  fof(f135,plain,(
% 1.48/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X0) | k1_partfun1(sK0,sK1,X1,X2,sK2,X0) = k5_relat_1(sK2,X0) | ~v1_funct_1(sK2)) )),
% 1.48/0.61    inference(resolution,[],[f66,f98])).
% 1.48/0.61  fof(f98,plain,(
% 1.48/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~v1_funct_1(X4)) )),
% 1.48/0.61    inference(cnf_transformation,[],[f50])).
% 1.48/0.61  fof(f50,plain,(
% 1.48/0.61    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.48/0.61    inference(flattening,[],[f49])).
% 1.48/0.61  fof(f49,plain,(
% 1.48/0.61    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.48/0.61    inference(ennf_transformation,[],[f20])).
% 1.48/0.61  fof(f20,axiom,(
% 1.48/0.61    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.48/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 1.48/0.61  fof(f71,plain,(
% 1.48/0.61    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 1.48/0.61    inference(cnf_transformation,[],[f60])).
% 1.48/0.61  fof(f285,plain,(
% 1.48/0.61    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.48/0.61    inference(subsumption_resolution,[],[f284,f64])).
% 1.48/0.61  fof(f284,plain,(
% 1.48/0.61    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK2)),
% 1.48/0.61    inference(subsumption_resolution,[],[f283,f66])).
% 1.48/0.61  fof(f283,plain,(
% 1.48/0.61    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2)),
% 1.48/0.61    inference(subsumption_resolution,[],[f282,f67])).
% 1.48/0.61  fof(f282,plain,(
% 1.48/0.61    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2)),
% 1.48/0.61    inference(subsumption_resolution,[],[f277,f69])).
% 1.48/0.61  fof(f277,plain,(
% 1.48/0.61    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2)),
% 1.48/0.61    inference(superposition,[],[f97,f245])).
% 1.48/0.61  fof(f97,plain,(
% 1.48/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.48/0.61    inference(cnf_transformation,[],[f48])).
% 1.48/0.61  fof(f48,plain,(
% 1.48/0.61    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.48/0.61    inference(flattening,[],[f47])).
% 1.48/0.61  fof(f47,plain,(
% 1.48/0.61    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.48/0.61    inference(ennf_transformation,[],[f19])).
% 1.48/0.61  fof(f19,axiom,(
% 1.48/0.61    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 1.48/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 1.48/0.61  fof(f506,plain,(
% 1.48/0.61    ( ! [X7] : (~v1_relat_1(X7) | k5_relat_1(k5_relat_1(X7,sK2),sK3) = k5_relat_1(X7,k5_relat_1(sK2,sK3))) )),
% 1.48/0.61    inference(resolution,[],[f147,f139])).
% 1.48/0.61  fof(f147,plain,(
% 1.48/0.61    ( ! [X2,X3] : (~v1_relat_1(X2) | ~v1_relat_1(X3) | k5_relat_1(k5_relat_1(X3,sK2),X2) = k5_relat_1(X3,k5_relat_1(sK2,X2))) )),
% 1.48/0.61    inference(resolution,[],[f133,f99])).
% 1.48/0.61  fof(f99,plain,(
% 1.48/0.61    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0) | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))) )),
% 1.48/0.61    inference(cnf_transformation,[],[f51])).
% 1.48/0.61  fof(f51,plain,(
% 1.48/0.61    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.48/0.61    inference(ennf_transformation,[],[f6])).
% 1.48/0.61  fof(f6,axiom,(
% 1.48/0.61    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)))))),
% 1.48/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).
% 1.48/0.61  fof(f133,plain,(
% 1.48/0.61    v1_relat_1(sK2)),
% 1.48/0.61    inference(resolution,[],[f66,f101])).
% 1.48/0.61  fof(f698,plain,(
% 1.48/0.61    k5_relat_1(k6_partfun1(sK1),k2_funct_1(sK2)) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) | ~spl5_3),
% 1.48/0.61    inference(forward_demodulation,[],[f697,f173])).
% 1.48/0.61  fof(f697,plain,(
% 1.48/0.61    k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k5_relat_1(k5_relat_1(k2_funct_1(sK2),sK2),k2_funct_1(sK2)) | ~spl5_3),
% 1.48/0.61    inference(forward_demodulation,[],[f690,f168])).
% 1.48/0.61  fof(f168,plain,(
% 1.48/0.61    k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 1.48/0.61    inference(subsumption_resolution,[],[f167,f64])).
% 1.48/0.61  fof(f167,plain,(
% 1.48/0.61    k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~v1_funct_1(sK2)),
% 1.48/0.61    inference(subsumption_resolution,[],[f166,f65])).
% 1.48/0.61  fof(f166,plain,(
% 1.48/0.61    k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 1.48/0.61    inference(subsumption_resolution,[],[f165,f66])).
% 1.48/0.61  fof(f165,plain,(
% 1.48/0.61    k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 1.48/0.61    inference(subsumption_resolution,[],[f164,f72])).
% 1.48/0.61  fof(f164,plain,(
% 1.48/0.61    ~v2_funct_1(sK2) | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 1.48/0.61    inference(subsumption_resolution,[],[f158,f74])).
% 1.48/0.61  fof(f158,plain,(
% 1.48/0.61    k1_xboole_0 = sK1 | ~v2_funct_1(sK2) | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 1.48/0.61    inference(trivial_inequality_removal,[],[f155])).
% 1.48/0.61  fof(f155,plain,(
% 1.48/0.61    sK1 != sK1 | k1_xboole_0 = sK1 | ~v2_funct_1(sK2) | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 1.48/0.61    inference(superposition,[],[f76,f70])).
% 1.48/0.61  fof(f76,plain,(
% 1.48/0.61    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.48/0.61    inference(cnf_transformation,[],[f31])).
% 1.48/0.61  fof(f690,plain,(
% 1.48/0.61    k5_relat_1(k5_relat_1(k2_funct_1(sK2),sK2),k2_funct_1(sK2)) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,k2_funct_1(sK2))) | ~spl5_3),
% 1.48/0.61    inference(resolution,[],[f514,f411])).
% 1.48/0.61  fof(f514,plain,(
% 1.48/0.61    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(k5_relat_1(X0,sK2),X0) = k5_relat_1(X0,k5_relat_1(sK2,X0))) )),
% 1.48/0.61    inference(factoring,[],[f147])).
% 1.48/0.61  fof(f425,plain,(
% 1.48/0.61    k2_funct_1(sK2) = k5_relat_1(k6_partfun1(sK1),k2_funct_1(sK2)) | ~spl5_3),
% 1.48/0.61    inference(forward_demodulation,[],[f421,f212])).
% 1.48/0.61  fof(f212,plain,(
% 1.48/0.61    sK1 = k1_relat_1(k2_funct_1(sK2))),
% 1.48/0.61    inference(forward_demodulation,[],[f211,f205])).
% 1.48/0.61  fof(f205,plain,(
% 1.48/0.61    sK1 = k2_relat_1(sK2)),
% 1.48/0.61    inference(forward_demodulation,[],[f134,f70])).
% 1.48/0.61  fof(f134,plain,(
% 1.48/0.61    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 1.48/0.61    inference(resolution,[],[f66,f100])).
% 1.48/0.61  fof(f100,plain,(
% 1.48/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.48/0.61    inference(cnf_transformation,[],[f52])).
% 1.48/0.61  fof(f52,plain,(
% 1.48/0.61    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.48/0.61    inference(ennf_transformation,[],[f16])).
% 1.48/0.61  fof(f16,axiom,(
% 1.48/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.48/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.48/0.61  fof(f211,plain,(
% 1.48/0.61    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))),
% 1.48/0.61    inference(subsumption_resolution,[],[f127,f133])).
% 1.48/0.61  fof(f127,plain,(
% 1.48/0.61    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 1.48/0.61    inference(subsumption_resolution,[],[f121,f64])).
% 1.48/0.61  fof(f121,plain,(
% 1.48/0.61    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 1.48/0.61    inference(resolution,[],[f72,f82])).
% 1.48/0.61  fof(f82,plain,(
% 1.48/0.61    ( ! [X0] : (~v2_funct_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.48/0.61    inference(cnf_transformation,[],[f37])).
% 1.48/0.61  fof(f37,plain,(
% 1.48/0.61    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.48/0.61    inference(flattening,[],[f36])).
% 1.48/0.61  fof(f36,plain,(
% 1.48/0.61    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.48/0.61    inference(ennf_transformation,[],[f12])).
% 1.48/0.61  fof(f12,axiom,(
% 1.48/0.61    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 1.48/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 1.48/0.61  fof(f421,plain,(
% 1.48/0.61    k2_funct_1(sK2) = k5_relat_1(k6_partfun1(k1_relat_1(k2_funct_1(sK2))),k2_funct_1(sK2)) | ~spl5_3),
% 1.48/0.61    inference(resolution,[],[f411,f113])).
% 1.48/0.61  fof(f420,plain,(
% 1.48/0.61    spl5_3),
% 1.48/0.61    inference(avatar_contradiction_clause,[],[f419])).
% 1.48/0.61  fof(f419,plain,(
% 1.48/0.61    $false | spl5_3),
% 1.48/0.61    inference(subsumption_resolution,[],[f418,f133])).
% 1.48/0.61  fof(f418,plain,(
% 1.48/0.61    ~v1_relat_1(sK2) | spl5_3),
% 1.48/0.61    inference(subsumption_resolution,[],[f417,f64])).
% 1.48/0.61  fof(f417,plain,(
% 1.48/0.61    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl5_3),
% 1.48/0.61    inference(resolution,[],[f412,f84])).
% 1.48/0.61  fof(f84,plain,(
% 1.48/0.61    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.48/0.61    inference(cnf_transformation,[],[f39])).
% 1.48/0.61  fof(f39,plain,(
% 1.48/0.61    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.48/0.61    inference(flattening,[],[f38])).
% 1.48/0.61  fof(f38,plain,(
% 1.48/0.61    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.48/0.61    inference(ennf_transformation,[],[f10])).
% 1.48/0.61  fof(f10,axiom,(
% 1.48/0.61    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 1.48/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 1.48/0.61  fof(f412,plain,(
% 1.48/0.61    ~v1_relat_1(k2_funct_1(sK2)) | spl5_3),
% 1.48/0.61    inference(avatar_component_clause,[],[f410])).
% 1.48/0.61  fof(f361,plain,(
% 1.48/0.61    spl5_2),
% 1.48/0.61    inference(avatar_contradiction_clause,[],[f360])).
% 1.48/0.61  fof(f360,plain,(
% 1.48/0.61    $false | spl5_2),
% 1.48/0.61    inference(subsumption_resolution,[],[f359,f111])).
% 1.48/0.61  fof(f111,plain,(
% 1.48/0.61    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 1.48/0.61    inference(definition_unfolding,[],[f91,f95])).
% 1.48/0.61  fof(f91,plain,(
% 1.48/0.61    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 1.48/0.61    inference(cnf_transformation,[],[f11])).
% 1.48/0.61  fof(f11,axiom,(
% 1.48/0.61    ! [X0] : v2_funct_1(k6_relat_1(X0))),
% 1.48/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_funct_1)).
% 1.48/0.61  fof(f359,plain,(
% 1.48/0.61    ~v2_funct_1(k6_partfun1(sK0)) | spl5_2),
% 1.48/0.61    inference(forward_demodulation,[],[f358,f291])).
% 1.48/0.61  fof(f291,plain,(
% 1.48/0.61    k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)),
% 1.48/0.61    inference(backward_demodulation,[],[f245,f288])).
% 1.48/0.61  fof(f358,plain,(
% 1.48/0.61    ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) | spl5_2),
% 1.48/0.61    inference(subsumption_resolution,[],[f357,f67])).
% 1.48/0.61  fof(f357,plain,(
% 1.48/0.61    ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) | ~v1_funct_1(sK3) | spl5_2),
% 1.48/0.61    inference(subsumption_resolution,[],[f356,f73])).
% 1.48/0.61  fof(f73,plain,(
% 1.48/0.61    k1_xboole_0 != sK0),
% 1.48/0.61    inference(cnf_transformation,[],[f60])).
% 1.48/0.61  fof(f356,plain,(
% 1.48/0.61    ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) | k1_xboole_0 = sK0 | ~v1_funct_1(sK3) | spl5_2),
% 1.48/0.61    inference(subsumption_resolution,[],[f355,f69])).
% 1.48/0.61  fof(f355,plain,(
% 1.48/0.61    ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | k1_xboole_0 = sK0 | ~v1_funct_1(sK3) | spl5_2),
% 1.48/0.61    inference(subsumption_resolution,[],[f354,f222])).
% 1.48/0.61  fof(f222,plain,(
% 1.48/0.61    ~v2_funct_1(sK3) | spl5_2),
% 1.48/0.61    inference(avatar_component_clause,[],[f220])).
% 1.48/0.61  fof(f354,plain,(
% 1.48/0.61    v2_funct_1(sK3) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | k1_xboole_0 = sK0 | ~v1_funct_1(sK3)),
% 1.48/0.61    inference(resolution,[],[f163,f68])).
% 1.48/0.61  fof(f68,plain,(
% 1.48/0.61    v1_funct_2(sK3,sK1,sK0)),
% 1.48/0.61    inference(cnf_transformation,[],[f60])).
% 1.48/0.61  fof(f163,plain,(
% 1.48/0.61    ( ! [X2,X3] : (~v1_funct_2(X3,sK1,X2) | v2_funct_1(X3) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X2,sK2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2))) | k1_xboole_0 = X2 | ~v1_funct_1(X3)) )),
% 1.48/0.61    inference(subsumption_resolution,[],[f162,f64])).
% 1.48/0.61  fof(f162,plain,(
% 1.48/0.61    ( ! [X2,X3] : (k1_xboole_0 = X2 | v2_funct_1(X3) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X2,sK2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2))) | ~v1_funct_2(X3,sK1,X2) | ~v1_funct_1(X3) | ~v1_funct_1(sK2)) )),
% 1.48/0.61    inference(subsumption_resolution,[],[f161,f65])).
% 1.48/0.61  fof(f161,plain,(
% 1.48/0.61    ( ! [X2,X3] : (k1_xboole_0 = X2 | v2_funct_1(X3) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X2,sK2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2))) | ~v1_funct_2(X3,sK1,X2) | ~v1_funct_1(X3) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) )),
% 1.48/0.61    inference(subsumption_resolution,[],[f159,f66])).
% 1.48/0.61  fof(f159,plain,(
% 1.48/0.61    ( ! [X2,X3] : (k1_xboole_0 = X2 | v2_funct_1(X3) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X2,sK2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2))) | ~v1_funct_2(X3,sK1,X2) | ~v1_funct_1(X3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) )),
% 1.48/0.61    inference(trivial_inequality_removal,[],[f154])).
% 1.48/0.61  fof(f154,plain,(
% 1.48/0.61    ( ! [X2,X3] : (sK1 != sK1 | k1_xboole_0 = X2 | v2_funct_1(X3) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X2,sK2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2))) | ~v1_funct_2(X3,sK1,X2) | ~v1_funct_1(X3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) )),
% 1.48/0.61    inference(superposition,[],[f88,f70])).
% 1.48/0.61  fof(f88,plain,(
% 1.48/0.61    ( ! [X4,X2,X0,X3,X1] : (k2_relset_1(X0,X1,X3) != X1 | k1_xboole_0 = X2 | v2_funct_1(X4) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.48/0.61    inference(cnf_transformation,[],[f41])).
% 1.48/0.61  fof(f41,plain,(
% 1.48/0.61    ! [X0,X1,X2,X3] : (! [X4] : ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.48/0.61    inference(flattening,[],[f40])).
% 1.48/0.61  fof(f40,plain,(
% 1.48/0.61    ! [X0,X1,X2,X3] : (! [X4] : ((((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | (k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.48/0.61    inference(ennf_transformation,[],[f23])).
% 1.48/0.61  fof(f23,axiom,(
% 1.48/0.61    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) => ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 1.48/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_funct_2)).
% 1.48/0.61  fof(f223,plain,(
% 1.48/0.61    spl5_1 | ~spl5_2),
% 1.48/0.61    inference(avatar_split_clause,[],[f200,f220,f216])).
% 1.48/0.61  fof(f200,plain,(
% 1.48/0.61    ~v2_funct_1(sK3) | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))),
% 1.48/0.61    inference(subsumption_resolution,[],[f199,f67])).
% 1.48/0.61  fof(f199,plain,(
% 1.48/0.61    ~v2_funct_1(sK3) | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~v1_funct_1(sK3)),
% 1.48/0.61    inference(subsumption_resolution,[],[f198,f68])).
% 1.48/0.61  fof(f198,plain,(
% 1.48/0.61    ~v2_funct_1(sK3) | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 1.48/0.61    inference(subsumption_resolution,[],[f197,f69])).
% 1.48/0.61  fof(f197,plain,(
% 1.48/0.61    ~v2_funct_1(sK3) | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 1.48/0.61    inference(subsumption_resolution,[],[f188,f73])).
% 1.48/0.61  fof(f188,plain,(
% 1.48/0.61    k1_xboole_0 = sK0 | ~v2_funct_1(sK3) | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 1.48/0.61    inference(trivial_inequality_removal,[],[f185])).
% 1.48/0.61  fof(f185,plain,(
% 1.48/0.61    sK0 != sK0 | k1_xboole_0 = sK0 | ~v2_funct_1(sK3) | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 1.48/0.61    inference(superposition,[],[f76,f182])).
% 1.48/0.61  fof(f182,plain,(
% 1.48/0.61    sK0 = k2_relset_1(sK1,sK0,sK3)),
% 1.48/0.61    inference(subsumption_resolution,[],[f181,f67])).
% 1.48/0.61  fof(f181,plain,(
% 1.48/0.61    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_1(sK3)),
% 1.48/0.61    inference(subsumption_resolution,[],[f180,f68])).
% 1.48/0.61  fof(f180,plain,(
% 1.48/0.61    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 1.48/0.61    inference(subsumption_resolution,[],[f179,f69])).
% 1.48/0.61  fof(f179,plain,(
% 1.48/0.61    sK0 = k2_relset_1(sK1,sK0,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 1.48/0.61    inference(subsumption_resolution,[],[f178,f64])).
% 1.48/0.61  fof(f178,plain,(
% 1.48/0.61    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 1.48/0.61    inference(subsumption_resolution,[],[f177,f65])).
% 1.48/0.61  fof(f177,plain,(
% 1.48/0.61    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 1.48/0.61    inference(subsumption_resolution,[],[f175,f66])).
% 1.48/0.61  fof(f175,plain,(
% 1.48/0.61    sK0 = k2_relset_1(sK1,sK0,sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 1.48/0.61    inference(resolution,[],[f71,f94])).
% 1.48/0.61  fof(f94,plain,(
% 1.48/0.61    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | k2_relset_1(X0,X1,X2) = X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.48/0.61    inference(cnf_transformation,[],[f46])).
% 1.48/0.61  fof(f46,plain,(
% 1.48/0.61    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.48/0.61    inference(flattening,[],[f45])).
% 1.48/0.61  fof(f45,plain,(
% 1.48/0.61    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.48/0.61    inference(ennf_transformation,[],[f22])).
% 1.48/0.61  fof(f22,axiom,(
% 1.48/0.61    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 1.48/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_2)).
% 1.48/0.61  % SZS output end Proof for theBenchmark
% 1.48/0.61  % (20576)------------------------------
% 1.48/0.61  % (20576)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.61  % (20576)Termination reason: Refutation
% 1.48/0.61  
% 1.48/0.61  % (20576)Memory used [KB]: 11257
% 1.48/0.61  % (20576)Time elapsed: 0.178 s
% 1.48/0.61  % (20576)------------------------------
% 1.48/0.61  % (20576)------------------------------
% 1.48/0.61  % (20551)Success in time 0.243 s
%------------------------------------------------------------------------------
