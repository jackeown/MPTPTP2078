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
% DateTime   : Thu Dec  3 13:02:53 EST 2020

% Result     : Theorem 2.22s
% Output     : Refutation 2.22s
% Verified   : 
% Statistics : Number of formulae       :  259 (1425 expanded)
%              Number of leaves         :   32 ( 450 expanded)
%              Depth                    :   29
%              Number of atoms          : 1061 (13275 expanded)
%              Number of equality atoms :  254 (4405 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f912,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f214,f219,f327,f331,f454,f456,f656,f660,f848,f907])).

fof(f907,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9 ),
    inference(avatar_contradiction_clause,[],[f906])).

fof(f906,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f894,f226])).

fof(f226,plain,
    ( sK3 != k4_relat_1(sK2)
    | ~ spl4_2 ),
    inference(superposition,[],[f81,f213])).

fof(f213,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f211])).

fof(f211,plain,
    ( spl4_2
  <=> k2_funct_1(sK2) = k4_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f81,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f30,f66,f65])).

fof(f65,plain,
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

fof(f66,plain,
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

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

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
    inference(ennf_transformation,[],[f28])).

fof(f28,negated_conjecture,(
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
    inference(negated_conjecture,[],[f27])).

fof(f27,conjecture,(
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

fof(f894,plain,
    ( sK3 = k4_relat_1(sK2)
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9 ),
    inference(backward_demodulation,[],[f664,f891])).

fof(f891,plain,
    ( sK2 = k4_relat_1(sK3)
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f890,f838])).

fof(f838,plain,
    ( v1_relat_1(k4_relat_1(sK3))
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f837])).

fof(f837,plain,
    ( spl4_9
  <=> v1_relat_1(k4_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f890,plain,
    ( sK2 = k4_relat_1(sK3)
    | ~ v1_relat_1(k4_relat_1(sK3))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f889,f717])).

fof(f717,plain,
    ( v1_funct_1(k4_relat_1(sK3))
    | ~ spl4_7
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f716,f650])).

fof(f650,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f649])).

fof(f649,plain,
    ( spl4_7
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f716,plain,
    ( v1_funct_1(k4_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ spl4_7
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f715,f73])).

fof(f73,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f67])).

fof(f715,plain,
    ( v1_funct_1(k4_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_7
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f709,f655])).

fof(f655,plain,
    ( v2_funct_1(sK3)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f653])).

fof(f653,plain,
    ( spl4_8
  <=> v2_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f709,plain,
    ( v1_funct_1(k4_relat_1(sK3))
    | ~ v2_funct_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_7
    | ~ spl4_8 ),
    inference(superposition,[],[f93,f691])).

fof(f691,plain,
    ( k4_relat_1(sK3) = k2_funct_1(sK3)
    | ~ spl4_7
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f690,f650])).

fof(f690,plain,
    ( k4_relat_1(sK3) = k2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f676,f73])).

fof(f676,plain,
    ( k4_relat_1(sK3) = k2_funct_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_8 ),
    inference(resolution,[],[f655,f89])).

fof(f89,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

fof(f93,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_funct_1)).

fof(f889,plain,
    ( sK2 = k4_relat_1(sK3)
    | ~ v1_funct_1(k4_relat_1(sK3))
    | ~ v1_relat_1(k4_relat_1(sK3))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f886,f671])).

fof(f671,plain,
    ( k6_partfun1(sK0) = k5_relat_1(k4_relat_1(sK3),k4_relat_1(sK2))
    | ~ spl4_1
    | ~ spl4_6
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f670,f134])).

fof(f134,plain,(
    ! [X0] : k6_partfun1(X0) = k4_relat_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f121,f109,f109])).

fof(f109,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f121,plain,(
    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_relat_1)).

fof(f670,plain,
    ( k4_relat_1(k6_partfun1(sK0)) = k5_relat_1(k4_relat_1(sK3),k4_relat_1(sK2))
    | ~ spl4_1
    | ~ spl4_6
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f666,f453])).

fof(f453,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f451])).

fof(f451,plain,
    ( spl4_6
  <=> k6_partfun1(sK0) = k5_relat_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f666,plain,
    ( k4_relat_1(k5_relat_1(sK2,sK3)) = k5_relat_1(k4_relat_1(sK3),k4_relat_1(sK2))
    | ~ spl4_1
    | ~ spl4_7 ),
    inference(resolution,[],[f650,f221])).

fof(f221,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k4_relat_1(k5_relat_1(sK2,X0)) = k5_relat_1(k4_relat_1(X0),k4_relat_1(sK2)) )
    | ~ spl4_1 ),
    inference(resolution,[],[f208,f122])).

fof(f122,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).

fof(f208,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f207])).

fof(f207,plain,
    ( spl4_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f886,plain,
    ( k6_partfun1(sK0) != k5_relat_1(k4_relat_1(sK3),k4_relat_1(sK2))
    | sK2 = k4_relat_1(sK3)
    | ~ v1_funct_1(k4_relat_1(sK3))
    | ~ v1_relat_1(k4_relat_1(sK3))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_7
    | ~ spl4_8 ),
    inference(trivial_inequality_removal,[],[f883])).

fof(f883,plain,
    ( sK1 != sK1
    | k6_partfun1(sK0) != k5_relat_1(k4_relat_1(sK3),k4_relat_1(sK2))
    | sK2 = k4_relat_1(sK3)
    | ~ v1_funct_1(k4_relat_1(sK3))
    | ~ v1_relat_1(k4_relat_1(sK3))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_7
    | ~ spl4_8 ),
    inference(superposition,[],[f865,f706])).

fof(f706,plain,
    ( sK1 = k2_relat_1(k4_relat_1(sK3))
    | ~ spl4_7
    | ~ spl4_8 ),
    inference(backward_demodulation,[],[f689,f691])).

fof(f689,plain,
    ( sK1 = k2_relat_1(k2_funct_1(sK3))
    | ~ spl4_7
    | ~ spl4_8 ),
    inference(forward_demodulation,[],[f688,f260])).

fof(f260,plain,(
    sK1 = k1_relat_1(sK3) ),
    inference(forward_demodulation,[],[f167,f161])).

fof(f161,plain,(
    sK1 = k1_relset_1(sK1,sK0,sK3) ),
    inference(global_subsumption,[],[f75,f160])).

fof(f160,plain,
    ( sK1 = k1_relset_1(sK1,sK0,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(subsumption_resolution,[],[f159,f79])).

fof(f79,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f67])).

fof(f159,plain,
    ( sK1 = k1_relset_1(sK1,sK0,sK3)
    | k1_xboole_0 = sK0
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(resolution,[],[f74,f97])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) = X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
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
    inference(nnf_transformation,[],[f48])).

fof(f48,plain,(
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
    inference(flattening,[],[f47])).

fof(f47,plain,(
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
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
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

fof(f74,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f67])).

fof(f75,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f67])).

fof(f167,plain,(
    k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) ),
    inference(resolution,[],[f75,f125])).

fof(f125,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f688,plain,
    ( k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3))
    | ~ spl4_7
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f687,f650])).

fof(f687,plain,
    ( k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f675,f73])).

fof(f675,plain,
    ( k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_8 ),
    inference(resolution,[],[f655,f88])).

fof(f88,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f865,plain,
    ( ! [X2] :
        ( sK1 != k2_relat_1(X2)
        | k6_partfun1(sK0) != k5_relat_1(X2,k4_relat_1(sK2))
        | sK2 = X2
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) )
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f864,f326])).

fof(f326,plain,
    ( sK2 = k2_funct_1(k4_relat_1(sK2))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f324])).

fof(f324,plain,
    ( spl4_4
  <=> sK2 = k2_funct_1(k4_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f864,plain,
    ( ! [X2] :
        ( k6_partfun1(sK0) != k5_relat_1(X2,k4_relat_1(sK2))
        | sK1 != k2_relat_1(X2)
        | k2_funct_1(k4_relat_1(sK2)) = X2
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) )
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(forward_demodulation,[],[f863,f282])).

fof(f282,plain,
    ( sK0 = k2_relat_1(k4_relat_1(sK2))
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f281,f216])).

fof(f216,plain,(
    sK0 = k1_relat_1(sK2) ),
    inference(forward_demodulation,[],[f162,f158])).

fof(f158,plain,(
    sK0 = k1_relset_1(sK0,sK1,sK2) ),
    inference(global_subsumption,[],[f72,f157])).

fof(f157,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f156,f80])).

fof(f80,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f67])).

fof(f156,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(resolution,[],[f71,f97])).

fof(f71,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f67])).

fof(f72,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f67])).

fof(f162,plain,(
    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) ),
    inference(resolution,[],[f72,f125])).

fof(f281,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k4_relat_1(sK2))
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f280,f213])).

fof(f280,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f152,f208])).

fof(f152,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f145,f70])).

fof(f70,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f67])).

fof(f145,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f78,f88])).

fof(f78,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f67])).

fof(f863,plain,
    ( ! [X2] :
        ( sK1 != k2_relat_1(X2)
        | k6_partfun1(k2_relat_1(k4_relat_1(sK2))) != k5_relat_1(X2,k4_relat_1(sK2))
        | k2_funct_1(k4_relat_1(sK2)) = X2
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) )
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(forward_demodulation,[],[f862,f289])).

fof(f289,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f270,f288])).

fof(f288,plain,
    ( sK1 = k1_relat_1(k4_relat_1(sK2))
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f264,f277])).

fof(f277,plain,
    ( sK1 = k1_relset_1(sK1,sK0,k4_relat_1(sK2))
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f200,f213])).

fof(f200,plain,(
    sK1 = k1_relset_1(sK1,sK0,k2_funct_1(sK2)) ),
    inference(global_subsumption,[],[f187,f199])).

fof(f199,plain,
    ( sK1 = k1_relset_1(sK1,sK0,k2_funct_1(sK2))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(subsumption_resolution,[],[f198,f79])).

fof(f198,plain,
    ( sK1 = k1_relset_1(sK1,sK0,k2_funct_1(sK2))
    | k1_xboole_0 = sK0
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(resolution,[],[f183,f97])).

fof(f183,plain,(
    v1_funct_2(k2_funct_1(sK2),sK1,sK0) ),
    inference(subsumption_resolution,[],[f182,f70])).

fof(f182,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f181,f71])).

fof(f181,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f180,f72])).

fof(f180,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f179,f78])).

fof(f179,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(trivial_inequality_removal,[],[f172])).

fof(f172,plain,
    ( sK1 != sK1
    | v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(superposition,[],[f115,f76])).

fof(f76,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f67])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | v1_funct_2(k2_funct_1(X2),X1,X0)
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

fof(f187,plain,(
    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(subsumption_resolution,[],[f186,f70])).

fof(f186,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f185,f71])).

fof(f185,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f184,f72])).

fof(f184,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f178,f78])).

fof(f178,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(trivial_inequality_removal,[],[f173])).

fof(f173,plain,
    ( sK1 != sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(superposition,[],[f116,f76])).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f264,plain,
    ( k1_relat_1(k4_relat_1(sK2)) = k1_relset_1(sK1,sK0,k4_relat_1(sK2))
    | ~ spl4_2 ),
    inference(resolution,[],[f261,f125])).

fof(f261,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f187,f213])).

fof(f270,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k4_relat_1(sK2))
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f269,f213])).

fof(f269,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f151,f208])).

fof(f151,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f144,f70])).

fof(f144,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f78,f87])).

fof(f87,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f862,plain,
    ( ! [X2] :
        ( k2_relat_1(sK2) != k2_relat_1(X2)
        | k6_partfun1(k2_relat_1(k4_relat_1(sK2))) != k5_relat_1(X2,k4_relat_1(sK2))
        | k2_funct_1(k4_relat_1(sK2)) = X2
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) )
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f276,f321])).

fof(f321,plain,
    ( v1_relat_1(k4_relat_1(sK2))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f320])).

fof(f320,plain,
    ( spl4_3
  <=> v1_relat_1(k4_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f276,plain,
    ( ! [X2] :
        ( k2_relat_1(sK2) != k2_relat_1(X2)
        | k6_partfun1(k2_relat_1(k4_relat_1(sK2))) != k5_relat_1(X2,k4_relat_1(sK2))
        | k2_funct_1(k4_relat_1(sK2)) = X2
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(k4_relat_1(sK2)) )
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f275,f237])).

fof(f237,plain,
    ( v1_funct_1(k4_relat_1(sK2))
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f236,f208])).

fof(f236,plain,
    ( v1_funct_1(k4_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f235,f70])).

fof(f235,plain,
    ( v1_funct_1(k4_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f229,f78])).

fof(f229,plain,
    ( v1_funct_1(k4_relat_1(sK2))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_2 ),
    inference(superposition,[],[f93,f213])).

fof(f275,plain,
    ( ! [X2] :
        ( k2_relat_1(sK2) != k2_relat_1(X2)
        | k6_partfun1(k2_relat_1(k4_relat_1(sK2))) != k5_relat_1(X2,k4_relat_1(sK2))
        | k2_funct_1(k4_relat_1(sK2)) = X2
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2)
        | ~ v1_funct_1(k4_relat_1(sK2))
        | ~ v1_relat_1(k4_relat_1(sK2)) )
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f273,f240])).

fof(f240,plain,
    ( v2_funct_1(k4_relat_1(sK2))
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f239,f208])).

fof(f239,plain,
    ( v2_funct_1(k4_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f238,f70])).

fof(f238,plain,
    ( v2_funct_1(k4_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f230,f78])).

fof(f230,plain,
    ( v2_funct_1(k4_relat_1(sK2))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_2 ),
    inference(superposition,[],[f94,f213])).

fof(f94,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f273,plain,
    ( ! [X2] :
        ( k2_relat_1(sK2) != k2_relat_1(X2)
        | k6_partfun1(k2_relat_1(k4_relat_1(sK2))) != k5_relat_1(X2,k4_relat_1(sK2))
        | k2_funct_1(k4_relat_1(sK2)) = X2
        | ~ v2_funct_1(k4_relat_1(sK2))
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2)
        | ~ v1_funct_1(k4_relat_1(sK2))
        | ~ v1_relat_1(k4_relat_1(sK2)) )
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(superposition,[],[f126,f270])).

fof(f126,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) != k2_relat_1(X1)
      | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
      | k2_funct_1(X0) = X1
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f82,f109])).

fof(f82,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
      | k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

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
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_1)).

fof(f664,plain,
    ( sK3 = k4_relat_1(k4_relat_1(sK3))
    | ~ spl4_7 ),
    inference(resolution,[],[f650,f123])).

fof(f123,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k4_relat_1(k4_relat_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k4_relat_1(k4_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).

fof(f848,plain,
    ( ~ spl4_7
    | spl4_9 ),
    inference(avatar_contradiction_clause,[],[f847])).

fof(f847,plain,
    ( $false
    | ~ spl4_7
    | spl4_9 ),
    inference(subsumption_resolution,[],[f845,f650])).

fof(f845,plain,
    ( ~ v1_relat_1(sK3)
    | spl4_9 ),
    inference(resolution,[],[f839,f124])).

fof(f124,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(f839,plain,
    ( ~ v1_relat_1(k4_relat_1(sK3))
    | spl4_9 ),
    inference(avatar_component_clause,[],[f837])).

fof(f660,plain,(
    spl4_7 ),
    inference(avatar_contradiction_clause,[],[f659])).

fof(f659,plain,
    ( $false
    | spl4_7 ),
    inference(subsumption_resolution,[],[f658,f118])).

fof(f118,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f658,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | spl4_7 ),
    inference(resolution,[],[f657,f75])).

fof(f657,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl4_7 ),
    inference(resolution,[],[f651,f117])).

fof(f117,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f651,plain,
    ( ~ v1_relat_1(sK3)
    | spl4_7 ),
    inference(avatar_component_clause,[],[f649])).

fof(f656,plain,
    ( ~ spl4_7
    | spl4_8
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f647,f451,f211,f207,f653,f649])).

fof(f647,plain,
    ( v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f646,f129])).

fof(f129,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f106,f109])).

fof(f106,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f646,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_6 ),
    inference(forward_demodulation,[],[f645,f453])).

fof(f645,plain,
    ( v2_funct_1(sK3)
    | ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | ~ v1_relat_1(sK3)
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f643,f73])).

fof(f643,plain,
    ( v2_funct_1(sK3)
    | ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(trivial_inequality_removal,[],[f642])).

fof(f642,plain,
    ( sK1 != sK1
    | v2_funct_1(sK3)
    | ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(superposition,[],[f301,f260])).

fof(f301,plain,
    ( ! [X1] :
        ( sK1 != k1_relat_1(X1)
        | v2_funct_1(X1)
        | ~ v2_funct_1(k5_relat_1(sK2,X1))
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1) )
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f300,f208])).

fof(f300,plain,
    ( ! [X1] :
        ( sK1 != k1_relat_1(X1)
        | v2_funct_1(X1)
        | ~ v2_funct_1(k5_relat_1(sK2,X1))
        | ~ v1_relat_1(sK2)
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1) )
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f298,f70])).

fof(f298,plain,
    ( ! [X1] :
        ( sK1 != k1_relat_1(X1)
        | v2_funct_1(X1)
        | ~ v2_funct_1(k5_relat_1(sK2,X1))
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2)
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1) )
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(superposition,[],[f104,f289])).

fof(f104,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) != k2_relat_1(X1)
      | v2_funct_1(X0)
      | ~ v2_funct_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
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

fof(f456,plain,(
    spl4_5 ),
    inference(avatar_contradiction_clause,[],[f455])).

fof(f455,plain,
    ( $false
    | spl4_5 ),
    inference(subsumption_resolution,[],[f443,f449])).

fof(f449,plain,
    ( ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl4_5 ),
    inference(avatar_component_clause,[],[f447])).

fof(f447,plain,
    ( spl4_5
  <=> m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f443,plain,(
    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f442,f70])).

fof(f442,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f441,f72])).

fof(f441,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f440,f73])).

fof(f440,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f435,f75])).

fof(f435,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(superposition,[],[f111,f340])).

fof(f340,plain,(
    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f335,f73])).

fof(f335,plain,
    ( ~ v1_funct_1(sK3)
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(resolution,[],[f165,f75])).

fof(f165,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X0)
      | k1_partfun1(sK0,sK1,X1,X2,sK2,X0) = k5_relat_1(sK2,X0) ) ),
    inference(subsumption_resolution,[],[f163,f70])).

fof(f163,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X0)
      | k1_partfun1(sK0,sK1,X1,X2,sK2,X0) = k5_relat_1(sK2,X0)
      | ~ v1_funct_1(sK2) ) ),
    inference(resolution,[],[f72,f112])).

fof(f112,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f111,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f454,plain,
    ( ~ spl4_5
    | spl4_6
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f445,f211,f207,f451,f447])).

fof(f445,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f444,f372])).

fof(f372,plain,
    ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f371,f70])).

fof(f371,plain,
    ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f370,f72])).

fof(f370,plain,
    ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f369,f237])).

fof(f369,plain,
    ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(k4_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f364,f261])).

fof(f364,plain,
    ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k4_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(superposition,[],[f111,f337])).

fof(f337,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,k4_relat_1(sK2))
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f336,f262])).

fof(f262,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,k4_relat_1(sK2))
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f192,f213])).

fof(f192,plain,(
    k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f191,f70])).

fof(f191,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f190,f71])).

fof(f190,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f189,f72])).

fof(f189,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f188,f78])).

fof(f188,plain,
    ( ~ v2_funct_1(sK2)
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f177,f80])).

fof(f177,plain,
    ( k1_xboole_0 = sK1
    | ~ v2_funct_1(sK2)
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(trivial_inequality_removal,[],[f174])).

fof(f174,plain,
    ( sK1 != sK1
    | k1_xboole_0 = sK1
    | ~ v2_funct_1(sK2)
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(superposition,[],[f95,f76])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
            & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).

fof(f336,plain,
    ( k5_relat_1(sK2,k4_relat_1(sK2)) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,k4_relat_1(sK2))
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f332,f237])).

fof(f332,plain,
    ( ~ v1_funct_1(k4_relat_1(sK2))
    | k5_relat_1(sK2,k4_relat_1(sK2)) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,k4_relat_1(sK2))
    | ~ spl4_2 ),
    inference(resolution,[],[f165,f261])).

fof(f444,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f433,f107])).

fof(f107,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f433,plain,(
    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0)) ),
    inference(backward_demodulation,[],[f77,f340])).

fof(f77,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f67])).

fof(f331,plain,
    ( ~ spl4_1
    | spl4_3 ),
    inference(avatar_contradiction_clause,[],[f330])).

fof(f330,plain,
    ( $false
    | ~ spl4_1
    | spl4_3 ),
    inference(subsumption_resolution,[],[f328,f208])).

fof(f328,plain,
    ( ~ v1_relat_1(sK2)
    | spl4_3 ),
    inference(resolution,[],[f322,f124])).

fof(f322,plain,
    ( ~ v1_relat_1(k4_relat_1(sK2))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f320])).

fof(f327,plain,
    ( ~ spl4_3
    | spl4_4
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f318,f211,f207,f324,f320])).

fof(f318,plain,
    ( sK2 = k2_funct_1(k4_relat_1(sK2))
    | ~ v1_relat_1(k4_relat_1(sK2))
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f254,f220])).

fof(f220,plain,
    ( sK2 = k4_relat_1(k4_relat_1(sK2))
    | ~ spl4_1 ),
    inference(resolution,[],[f208,f123])).

fof(f254,plain,
    ( k4_relat_1(k4_relat_1(sK2)) = k2_funct_1(k4_relat_1(sK2))
    | ~ v1_relat_1(k4_relat_1(sK2))
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f247,f237])).

fof(f247,plain,
    ( k4_relat_1(k4_relat_1(sK2)) = k2_funct_1(k4_relat_1(sK2))
    | ~ v1_funct_1(k4_relat_1(sK2))
    | ~ v1_relat_1(k4_relat_1(sK2))
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(resolution,[],[f240,f89])).

fof(f219,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f218])).

fof(f218,plain,
    ( $false
    | spl4_1 ),
    inference(subsumption_resolution,[],[f217,f118])).

fof(f217,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | spl4_1 ),
    inference(resolution,[],[f215,f72])).

fof(f215,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl4_1 ),
    inference(resolution,[],[f209,f117])).

fof(f209,plain,
    ( ~ v1_relat_1(sK2)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f207])).

fof(f214,plain,
    ( ~ spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f153,f211,f207])).

fof(f153,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f146,f70])).

fof(f146,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f78,f89])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:17:35 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.53  % (31112)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (31120)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.55  % (31128)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.56  % (31134)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.56  % (31118)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.57  % (31126)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.57  % (31123)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.57  % (31115)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.58  % (31131)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.78/0.60  % (31117)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.78/0.60  % (31133)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.78/0.60  % (31124)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.78/0.60  % (31121)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.78/0.60  % (31110)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.78/0.60  % (31132)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.78/0.60  % (31113)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.78/0.61  % (31108)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.78/0.61  % (31116)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.78/0.61  % (31109)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.78/0.61  % (31129)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.88/0.61  % (31107)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.88/0.61  % (31114)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.88/0.61  % (31135)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.88/0.62  % (31127)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.88/0.62  % (31111)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.88/0.62  % (31122)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.88/0.62  % (31106)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.88/0.63  % (31130)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.88/0.63  % (31119)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.88/0.64  % (31122)Refutation not found, incomplete strategy% (31122)------------------------------
% 1.88/0.64  % (31122)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.88/0.64  % (31122)Termination reason: Refutation not found, incomplete strategy
% 1.88/0.64  
% 1.88/0.64  % (31122)Memory used [KB]: 10746
% 1.88/0.64  % (31122)Time elapsed: 0.212 s
% 1.88/0.64  % (31122)------------------------------
% 1.88/0.64  % (31122)------------------------------
% 1.88/0.64  % (31125)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 2.22/0.67  % (31130)Refutation found. Thanks to Tanya!
% 2.22/0.67  % SZS status Theorem for theBenchmark
% 2.22/0.68  % SZS output start Proof for theBenchmark
% 2.22/0.68  fof(f912,plain,(
% 2.22/0.68    $false),
% 2.22/0.68    inference(avatar_sat_refutation,[],[f214,f219,f327,f331,f454,f456,f656,f660,f848,f907])).
% 2.22/0.68  fof(f907,plain,(
% 2.22/0.68    ~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_6 | ~spl4_7 | ~spl4_8 | ~spl4_9),
% 2.22/0.68    inference(avatar_contradiction_clause,[],[f906])).
% 2.22/0.68  fof(f906,plain,(
% 2.22/0.68    $false | (~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_6 | ~spl4_7 | ~spl4_8 | ~spl4_9)),
% 2.22/0.68    inference(subsumption_resolution,[],[f894,f226])).
% 2.22/0.68  fof(f226,plain,(
% 2.22/0.68    sK3 != k4_relat_1(sK2) | ~spl4_2),
% 2.22/0.68    inference(superposition,[],[f81,f213])).
% 2.22/0.68  fof(f213,plain,(
% 2.22/0.68    k2_funct_1(sK2) = k4_relat_1(sK2) | ~spl4_2),
% 2.22/0.68    inference(avatar_component_clause,[],[f211])).
% 2.22/0.68  fof(f211,plain,(
% 2.22/0.68    spl4_2 <=> k2_funct_1(sK2) = k4_relat_1(sK2)),
% 2.22/0.68    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 2.22/0.68  fof(f81,plain,(
% 2.22/0.68    k2_funct_1(sK2) != sK3),
% 2.22/0.68    inference(cnf_transformation,[],[f67])).
% 2.22/0.68  fof(f67,plain,(
% 2.22/0.68    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 2.22/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f30,f66,f65])).
% 2.22/0.68  fof(f65,plain,(
% 2.22/0.68    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 2.22/0.68    introduced(choice_axiom,[])).
% 2.22/0.68  fof(f66,plain,(
% 2.22/0.68    ? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) => (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3))),
% 2.22/0.68    introduced(choice_axiom,[])).
% 2.22/0.68  fof(f30,plain,(
% 2.22/0.68    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.22/0.68    inference(flattening,[],[f29])).
% 2.22/0.68  fof(f29,plain,(
% 2.22/0.68    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.22/0.68    inference(ennf_transformation,[],[f28])).
% 2.22/0.68  fof(f28,negated_conjecture,(
% 2.22/0.68    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 2.22/0.68    inference(negated_conjecture,[],[f27])).
% 2.22/0.68  fof(f27,conjecture,(
% 2.22/0.68    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 2.22/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).
% 2.22/0.68  fof(f894,plain,(
% 2.22/0.68    sK3 = k4_relat_1(sK2) | (~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_6 | ~spl4_7 | ~spl4_8 | ~spl4_9)),
% 2.22/0.68    inference(backward_demodulation,[],[f664,f891])).
% 2.22/0.68  fof(f891,plain,(
% 2.22/0.68    sK2 = k4_relat_1(sK3) | (~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_6 | ~spl4_7 | ~spl4_8 | ~spl4_9)),
% 2.22/0.68    inference(subsumption_resolution,[],[f890,f838])).
% 2.22/0.68  fof(f838,plain,(
% 2.22/0.68    v1_relat_1(k4_relat_1(sK3)) | ~spl4_9),
% 2.22/0.68    inference(avatar_component_clause,[],[f837])).
% 2.22/0.68  fof(f837,plain,(
% 2.22/0.68    spl4_9 <=> v1_relat_1(k4_relat_1(sK3))),
% 2.22/0.68    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 2.22/0.68  fof(f890,plain,(
% 2.22/0.68    sK2 = k4_relat_1(sK3) | ~v1_relat_1(k4_relat_1(sK3)) | (~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_6 | ~spl4_7 | ~spl4_8)),
% 2.22/0.68    inference(subsumption_resolution,[],[f889,f717])).
% 2.22/0.68  fof(f717,plain,(
% 2.22/0.68    v1_funct_1(k4_relat_1(sK3)) | (~spl4_7 | ~spl4_8)),
% 2.22/0.68    inference(subsumption_resolution,[],[f716,f650])).
% 2.22/0.68  fof(f650,plain,(
% 2.22/0.68    v1_relat_1(sK3) | ~spl4_7),
% 2.22/0.68    inference(avatar_component_clause,[],[f649])).
% 2.22/0.68  fof(f649,plain,(
% 2.22/0.68    spl4_7 <=> v1_relat_1(sK3)),
% 2.22/0.68    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 2.22/0.68  fof(f716,plain,(
% 2.22/0.68    v1_funct_1(k4_relat_1(sK3)) | ~v1_relat_1(sK3) | (~spl4_7 | ~spl4_8)),
% 2.22/0.68    inference(subsumption_resolution,[],[f715,f73])).
% 2.22/0.68  fof(f73,plain,(
% 2.22/0.68    v1_funct_1(sK3)),
% 2.22/0.68    inference(cnf_transformation,[],[f67])).
% 2.22/0.68  fof(f715,plain,(
% 2.22/0.68    v1_funct_1(k4_relat_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl4_7 | ~spl4_8)),
% 2.22/0.68    inference(subsumption_resolution,[],[f709,f655])).
% 2.22/0.68  fof(f655,plain,(
% 2.22/0.68    v2_funct_1(sK3) | ~spl4_8),
% 2.22/0.68    inference(avatar_component_clause,[],[f653])).
% 2.22/0.68  fof(f653,plain,(
% 2.22/0.68    spl4_8 <=> v2_funct_1(sK3)),
% 2.22/0.68    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 2.22/0.68  fof(f709,plain,(
% 2.22/0.68    v1_funct_1(k4_relat_1(sK3)) | ~v2_funct_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl4_7 | ~spl4_8)),
% 2.22/0.68    inference(superposition,[],[f93,f691])).
% 2.22/0.68  fof(f691,plain,(
% 2.22/0.68    k4_relat_1(sK3) = k2_funct_1(sK3) | (~spl4_7 | ~spl4_8)),
% 2.22/0.68    inference(subsumption_resolution,[],[f690,f650])).
% 2.22/0.68  fof(f690,plain,(
% 2.22/0.68    k4_relat_1(sK3) = k2_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl4_8),
% 2.22/0.68    inference(subsumption_resolution,[],[f676,f73])).
% 2.22/0.68  fof(f676,plain,(
% 2.22/0.68    k4_relat_1(sK3) = k2_funct_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl4_8),
% 2.22/0.68    inference(resolution,[],[f655,f89])).
% 2.22/0.68  fof(f89,plain,(
% 2.22/0.68    ( ! [X0] : (~v2_funct_1(X0) | k4_relat_1(X0) = k2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.22/0.68    inference(cnf_transformation,[],[f40])).
% 2.22/0.68  fof(f40,plain,(
% 2.22/0.68    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.22/0.68    inference(flattening,[],[f39])).
% 2.22/0.68  fof(f39,plain,(
% 2.22/0.68    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.22/0.68    inference(ennf_transformation,[],[f9])).
% 2.22/0.68  fof(f9,axiom,(
% 2.22/0.68    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 2.22/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).
% 2.22/0.68  fof(f93,plain,(
% 2.22/0.68    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.22/0.68    inference(cnf_transformation,[],[f44])).
% 2.22/0.68  fof(f44,plain,(
% 2.22/0.68    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.22/0.68    inference(flattening,[],[f43])).
% 2.22/0.68  fof(f43,plain,(
% 2.22/0.68    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.22/0.68    inference(ennf_transformation,[],[f12])).
% 2.22/0.68  fof(f12,axiom,(
% 2.22/0.68    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 2.22/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_funct_1)).
% 2.22/0.68  fof(f889,plain,(
% 2.22/0.68    sK2 = k4_relat_1(sK3) | ~v1_funct_1(k4_relat_1(sK3)) | ~v1_relat_1(k4_relat_1(sK3)) | (~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_6 | ~spl4_7 | ~spl4_8)),
% 2.22/0.68    inference(subsumption_resolution,[],[f886,f671])).
% 2.22/0.68  fof(f671,plain,(
% 2.22/0.68    k6_partfun1(sK0) = k5_relat_1(k4_relat_1(sK3),k4_relat_1(sK2)) | (~spl4_1 | ~spl4_6 | ~spl4_7)),
% 2.22/0.68    inference(forward_demodulation,[],[f670,f134])).
% 2.22/0.68  fof(f134,plain,(
% 2.22/0.68    ( ! [X0] : (k6_partfun1(X0) = k4_relat_1(k6_partfun1(X0))) )),
% 2.22/0.68    inference(definition_unfolding,[],[f121,f109,f109])).
% 2.22/0.68  fof(f109,plain,(
% 2.22/0.68    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 2.22/0.68    inference(cnf_transformation,[],[f24])).
% 2.22/0.68  fof(f24,axiom,(
% 2.22/0.68    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 2.22/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 2.22/0.68  fof(f121,plain,(
% 2.22/0.68    ( ! [X0] : (k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))) )),
% 2.22/0.68    inference(cnf_transformation,[],[f7])).
% 2.22/0.68  fof(f7,axiom,(
% 2.22/0.68    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))),
% 2.22/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_relat_1)).
% 2.22/0.68  fof(f670,plain,(
% 2.22/0.68    k4_relat_1(k6_partfun1(sK0)) = k5_relat_1(k4_relat_1(sK3),k4_relat_1(sK2)) | (~spl4_1 | ~spl4_6 | ~spl4_7)),
% 2.22/0.68    inference(forward_demodulation,[],[f666,f453])).
% 2.22/0.68  fof(f453,plain,(
% 2.22/0.68    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~spl4_6),
% 2.22/0.68    inference(avatar_component_clause,[],[f451])).
% 2.22/0.68  fof(f451,plain,(
% 2.22/0.68    spl4_6 <=> k6_partfun1(sK0) = k5_relat_1(sK2,sK3)),
% 2.22/0.68    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 2.22/0.68  fof(f666,plain,(
% 2.22/0.68    k4_relat_1(k5_relat_1(sK2,sK3)) = k5_relat_1(k4_relat_1(sK3),k4_relat_1(sK2)) | (~spl4_1 | ~spl4_7)),
% 2.22/0.68    inference(resolution,[],[f650,f221])).
% 2.22/0.68  fof(f221,plain,(
% 2.22/0.68    ( ! [X0] : (~v1_relat_1(X0) | k4_relat_1(k5_relat_1(sK2,X0)) = k5_relat_1(k4_relat_1(X0),k4_relat_1(sK2))) ) | ~spl4_1),
% 2.22/0.68    inference(resolution,[],[f208,f122])).
% 2.22/0.68  fof(f122,plain,(
% 2.22/0.68    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X0) | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))) )),
% 2.22/0.68    inference(cnf_transformation,[],[f61])).
% 2.22/0.68  fof(f61,plain,(
% 2.22/0.68    ! [X0] : (! [X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.22/0.68    inference(ennf_transformation,[],[f5])).
% 2.22/0.68  fof(f5,axiom,(
% 2.22/0.68    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))))),
% 2.22/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).
% 2.22/0.68  fof(f208,plain,(
% 2.22/0.68    v1_relat_1(sK2) | ~spl4_1),
% 2.22/0.68    inference(avatar_component_clause,[],[f207])).
% 2.22/0.68  fof(f207,plain,(
% 2.22/0.68    spl4_1 <=> v1_relat_1(sK2)),
% 2.22/0.68    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 2.22/0.68  fof(f886,plain,(
% 2.22/0.68    k6_partfun1(sK0) != k5_relat_1(k4_relat_1(sK3),k4_relat_1(sK2)) | sK2 = k4_relat_1(sK3) | ~v1_funct_1(k4_relat_1(sK3)) | ~v1_relat_1(k4_relat_1(sK3)) | (~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_7 | ~spl4_8)),
% 2.22/0.68    inference(trivial_inequality_removal,[],[f883])).
% 2.22/0.68  fof(f883,plain,(
% 2.22/0.68    sK1 != sK1 | k6_partfun1(sK0) != k5_relat_1(k4_relat_1(sK3),k4_relat_1(sK2)) | sK2 = k4_relat_1(sK3) | ~v1_funct_1(k4_relat_1(sK3)) | ~v1_relat_1(k4_relat_1(sK3)) | (~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_7 | ~spl4_8)),
% 2.22/0.68    inference(superposition,[],[f865,f706])).
% 2.22/0.68  fof(f706,plain,(
% 2.22/0.68    sK1 = k2_relat_1(k4_relat_1(sK3)) | (~spl4_7 | ~spl4_8)),
% 2.22/0.68    inference(backward_demodulation,[],[f689,f691])).
% 2.22/0.68  fof(f689,plain,(
% 2.22/0.68    sK1 = k2_relat_1(k2_funct_1(sK3)) | (~spl4_7 | ~spl4_8)),
% 2.22/0.68    inference(forward_demodulation,[],[f688,f260])).
% 2.22/0.68  fof(f260,plain,(
% 2.22/0.68    sK1 = k1_relat_1(sK3)),
% 2.22/0.68    inference(forward_demodulation,[],[f167,f161])).
% 2.22/0.68  fof(f161,plain,(
% 2.22/0.68    sK1 = k1_relset_1(sK1,sK0,sK3)),
% 2.22/0.68    inference(global_subsumption,[],[f75,f160])).
% 2.22/0.68  fof(f160,plain,(
% 2.22/0.68    sK1 = k1_relset_1(sK1,sK0,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.22/0.68    inference(subsumption_resolution,[],[f159,f79])).
% 2.22/0.68  fof(f79,plain,(
% 2.22/0.68    k1_xboole_0 != sK0),
% 2.22/0.68    inference(cnf_transformation,[],[f67])).
% 2.22/0.68  fof(f159,plain,(
% 2.22/0.68    sK1 = k1_relset_1(sK1,sK0,sK3) | k1_xboole_0 = sK0 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.22/0.68    inference(resolution,[],[f74,f97])).
% 2.22/0.68  fof(f97,plain,(
% 2.22/0.68    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) = X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.22/0.68    inference(cnf_transformation,[],[f68])).
% 2.22/0.68  fof(f68,plain,(
% 2.22/0.68    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.22/0.68    inference(nnf_transformation,[],[f48])).
% 2.22/0.68  fof(f48,plain,(
% 2.22/0.68    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.22/0.68    inference(flattening,[],[f47])).
% 2.22/0.68  fof(f47,plain,(
% 2.22/0.68    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.22/0.68    inference(ennf_transformation,[],[f20])).
% 2.22/0.68  fof(f20,axiom,(
% 2.22/0.68    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.22/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 2.22/0.68  fof(f74,plain,(
% 2.22/0.68    v1_funct_2(sK3,sK1,sK0)),
% 2.22/0.68    inference(cnf_transformation,[],[f67])).
% 2.22/0.68  fof(f75,plain,(
% 2.22/0.68    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.22/0.68    inference(cnf_transformation,[],[f67])).
% 2.22/0.68  fof(f167,plain,(
% 2.22/0.68    k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3)),
% 2.22/0.68    inference(resolution,[],[f75,f125])).
% 2.22/0.68  fof(f125,plain,(
% 2.22/0.68    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 2.22/0.68    inference(cnf_transformation,[],[f64])).
% 2.22/0.68  fof(f64,plain,(
% 2.22/0.68    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.22/0.68    inference(ennf_transformation,[],[f18])).
% 2.22/0.68  fof(f18,axiom,(
% 2.22/0.68    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 2.22/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 2.22/0.68  fof(f688,plain,(
% 2.22/0.68    k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3)) | (~spl4_7 | ~spl4_8)),
% 2.22/0.68    inference(subsumption_resolution,[],[f687,f650])).
% 2.22/0.68  fof(f687,plain,(
% 2.22/0.68    k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3)) | ~v1_relat_1(sK3) | ~spl4_8),
% 2.22/0.68    inference(subsumption_resolution,[],[f675,f73])).
% 2.22/0.68  fof(f675,plain,(
% 2.22/0.68    k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl4_8),
% 2.22/0.68    inference(resolution,[],[f655,f88])).
% 2.22/0.68  fof(f88,plain,(
% 2.22/0.68    ( ! [X0] : (~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.22/0.68    inference(cnf_transformation,[],[f38])).
% 2.22/0.68  fof(f38,plain,(
% 2.22/0.68    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.22/0.68    inference(flattening,[],[f37])).
% 2.22/0.68  fof(f37,plain,(
% 2.22/0.68    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.22/0.68    inference(ennf_transformation,[],[f14])).
% 2.22/0.68  fof(f14,axiom,(
% 2.22/0.68    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 2.22/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 2.22/0.68  fof(f865,plain,(
% 2.22/0.68    ( ! [X2] : (sK1 != k2_relat_1(X2) | k6_partfun1(sK0) != k5_relat_1(X2,k4_relat_1(sK2)) | sK2 = X2 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) ) | (~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4)),
% 2.22/0.68    inference(forward_demodulation,[],[f864,f326])).
% 2.22/0.68  fof(f326,plain,(
% 2.22/0.68    sK2 = k2_funct_1(k4_relat_1(sK2)) | ~spl4_4),
% 2.22/0.68    inference(avatar_component_clause,[],[f324])).
% 2.22/0.68  fof(f324,plain,(
% 2.22/0.68    spl4_4 <=> sK2 = k2_funct_1(k4_relat_1(sK2))),
% 2.22/0.68    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 2.22/0.68  fof(f864,plain,(
% 2.22/0.68    ( ! [X2] : (k6_partfun1(sK0) != k5_relat_1(X2,k4_relat_1(sK2)) | sK1 != k2_relat_1(X2) | k2_funct_1(k4_relat_1(sK2)) = X2 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) ) | (~spl4_1 | ~spl4_2 | ~spl4_3)),
% 2.22/0.68    inference(forward_demodulation,[],[f863,f282])).
% 2.22/0.68  fof(f282,plain,(
% 2.22/0.68    sK0 = k2_relat_1(k4_relat_1(sK2)) | (~spl4_1 | ~spl4_2)),
% 2.22/0.68    inference(forward_demodulation,[],[f281,f216])).
% 2.22/0.68  fof(f216,plain,(
% 2.22/0.68    sK0 = k1_relat_1(sK2)),
% 2.22/0.68    inference(forward_demodulation,[],[f162,f158])).
% 2.22/0.68  fof(f158,plain,(
% 2.22/0.68    sK0 = k1_relset_1(sK0,sK1,sK2)),
% 2.22/0.68    inference(global_subsumption,[],[f72,f157])).
% 2.22/0.68  fof(f157,plain,(
% 2.22/0.68    sK0 = k1_relset_1(sK0,sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.22/0.68    inference(subsumption_resolution,[],[f156,f80])).
% 2.22/0.68  fof(f80,plain,(
% 2.22/0.68    k1_xboole_0 != sK1),
% 2.22/0.68    inference(cnf_transformation,[],[f67])).
% 2.22/0.68  fof(f156,plain,(
% 2.22/0.68    sK0 = k1_relset_1(sK0,sK1,sK2) | k1_xboole_0 = sK1 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.22/0.68    inference(resolution,[],[f71,f97])).
% 2.22/0.68  fof(f71,plain,(
% 2.22/0.68    v1_funct_2(sK2,sK0,sK1)),
% 2.22/0.68    inference(cnf_transformation,[],[f67])).
% 2.22/0.68  fof(f72,plain,(
% 2.22/0.68    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.22/0.68    inference(cnf_transformation,[],[f67])).
% 2.22/0.68  fof(f162,plain,(
% 2.22/0.68    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)),
% 2.22/0.68    inference(resolution,[],[f72,f125])).
% 2.22/0.68  fof(f281,plain,(
% 2.22/0.68    k1_relat_1(sK2) = k2_relat_1(k4_relat_1(sK2)) | (~spl4_1 | ~spl4_2)),
% 2.22/0.68    inference(forward_demodulation,[],[f280,f213])).
% 2.22/0.68  fof(f280,plain,(
% 2.22/0.68    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~spl4_1),
% 2.22/0.68    inference(subsumption_resolution,[],[f152,f208])).
% 2.22/0.68  fof(f152,plain,(
% 2.22/0.68    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 2.22/0.68    inference(subsumption_resolution,[],[f145,f70])).
% 2.22/0.68  fof(f70,plain,(
% 2.22/0.68    v1_funct_1(sK2)),
% 2.22/0.68    inference(cnf_transformation,[],[f67])).
% 2.22/0.68  fof(f145,plain,(
% 2.22/0.68    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 2.22/0.68    inference(resolution,[],[f78,f88])).
% 2.22/0.68  fof(f78,plain,(
% 2.22/0.68    v2_funct_1(sK2)),
% 2.22/0.68    inference(cnf_transformation,[],[f67])).
% 2.22/0.68  fof(f863,plain,(
% 2.22/0.68    ( ! [X2] : (sK1 != k2_relat_1(X2) | k6_partfun1(k2_relat_1(k4_relat_1(sK2))) != k5_relat_1(X2,k4_relat_1(sK2)) | k2_funct_1(k4_relat_1(sK2)) = X2 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) ) | (~spl4_1 | ~spl4_2 | ~spl4_3)),
% 2.22/0.68    inference(forward_demodulation,[],[f862,f289])).
% 2.22/0.68  fof(f289,plain,(
% 2.22/0.68    sK1 = k2_relat_1(sK2) | (~spl4_1 | ~spl4_2)),
% 2.22/0.68    inference(backward_demodulation,[],[f270,f288])).
% 2.22/0.68  fof(f288,plain,(
% 2.22/0.68    sK1 = k1_relat_1(k4_relat_1(sK2)) | ~spl4_2),
% 2.22/0.68    inference(forward_demodulation,[],[f264,f277])).
% 2.22/0.68  fof(f277,plain,(
% 2.22/0.68    sK1 = k1_relset_1(sK1,sK0,k4_relat_1(sK2)) | ~spl4_2),
% 2.22/0.68    inference(forward_demodulation,[],[f200,f213])).
% 2.22/0.68  fof(f200,plain,(
% 2.22/0.68    sK1 = k1_relset_1(sK1,sK0,k2_funct_1(sK2))),
% 2.22/0.68    inference(global_subsumption,[],[f187,f199])).
% 2.22/0.68  fof(f199,plain,(
% 2.22/0.68    sK1 = k1_relset_1(sK1,sK0,k2_funct_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.22/0.68    inference(subsumption_resolution,[],[f198,f79])).
% 2.22/0.68  fof(f198,plain,(
% 2.22/0.68    sK1 = k1_relset_1(sK1,sK0,k2_funct_1(sK2)) | k1_xboole_0 = sK0 | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.22/0.68    inference(resolution,[],[f183,f97])).
% 2.22/0.68  fof(f183,plain,(
% 2.22/0.68    v1_funct_2(k2_funct_1(sK2),sK1,sK0)),
% 2.22/0.68    inference(subsumption_resolution,[],[f182,f70])).
% 2.22/0.68  fof(f182,plain,(
% 2.22/0.68    v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(sK2)),
% 2.22/0.68    inference(subsumption_resolution,[],[f181,f71])).
% 2.22/0.68  fof(f181,plain,(
% 2.22/0.68    v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 2.22/0.68    inference(subsumption_resolution,[],[f180,f72])).
% 2.22/0.68  fof(f180,plain,(
% 2.22/0.68    v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 2.22/0.68    inference(subsumption_resolution,[],[f179,f78])).
% 2.22/0.68  fof(f179,plain,(
% 2.22/0.68    v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 2.22/0.68    inference(trivial_inequality_removal,[],[f172])).
% 2.22/0.68  fof(f172,plain,(
% 2.22/0.68    sK1 != sK1 | v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 2.22/0.68    inference(superposition,[],[f115,f76])).
% 2.22/0.68  fof(f76,plain,(
% 2.22/0.68    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 2.22/0.68    inference(cnf_transformation,[],[f67])).
% 2.22/0.68  fof(f115,plain,(
% 2.22/0.68    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | v1_funct_2(k2_funct_1(X2),X1,X0) | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.22/0.68    inference(cnf_transformation,[],[f59])).
% 2.22/0.68  fof(f59,plain,(
% 2.22/0.68    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.22/0.68    inference(flattening,[],[f58])).
% 2.22/0.68  fof(f58,plain,(
% 2.22/0.68    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.22/0.68    inference(ennf_transformation,[],[f25])).
% 2.22/0.68  fof(f25,axiom,(
% 2.22/0.68    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.22/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).
% 2.22/0.68  fof(f187,plain,(
% 2.22/0.68    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.22/0.68    inference(subsumption_resolution,[],[f186,f70])).
% 2.22/0.68  fof(f186,plain,(
% 2.22/0.68    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK2)),
% 2.22/0.68    inference(subsumption_resolution,[],[f185,f71])).
% 2.22/0.68  fof(f185,plain,(
% 2.22/0.68    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 2.22/0.68    inference(subsumption_resolution,[],[f184,f72])).
% 2.22/0.68  fof(f184,plain,(
% 2.22/0.68    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 2.22/0.68    inference(subsumption_resolution,[],[f178,f78])).
% 2.22/0.68  fof(f178,plain,(
% 2.22/0.68    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 2.22/0.68    inference(trivial_inequality_removal,[],[f173])).
% 2.22/0.68  fof(f173,plain,(
% 2.22/0.68    sK1 != sK1 | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 2.22/0.68    inference(superposition,[],[f116,f76])).
% 2.22/0.68  fof(f116,plain,(
% 2.22/0.68    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.22/0.68    inference(cnf_transformation,[],[f59])).
% 2.22/0.68  fof(f264,plain,(
% 2.22/0.68    k1_relat_1(k4_relat_1(sK2)) = k1_relset_1(sK1,sK0,k4_relat_1(sK2)) | ~spl4_2),
% 2.22/0.68    inference(resolution,[],[f261,f125])).
% 2.22/0.68  fof(f261,plain,(
% 2.22/0.68    m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_2),
% 2.22/0.68    inference(forward_demodulation,[],[f187,f213])).
% 2.22/0.68  fof(f270,plain,(
% 2.22/0.68    k2_relat_1(sK2) = k1_relat_1(k4_relat_1(sK2)) | (~spl4_1 | ~spl4_2)),
% 2.22/0.68    inference(forward_demodulation,[],[f269,f213])).
% 2.22/0.68  fof(f269,plain,(
% 2.22/0.68    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~spl4_1),
% 2.22/0.68    inference(subsumption_resolution,[],[f151,f208])).
% 2.22/0.68  fof(f151,plain,(
% 2.22/0.68    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 2.22/0.68    inference(subsumption_resolution,[],[f144,f70])).
% 2.22/0.68  fof(f144,plain,(
% 2.22/0.68    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 2.22/0.68    inference(resolution,[],[f78,f87])).
% 2.22/0.68  fof(f87,plain,(
% 2.22/0.68    ( ! [X0] : (~v2_funct_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.22/0.68    inference(cnf_transformation,[],[f38])).
% 2.22/0.68  fof(f862,plain,(
% 2.22/0.68    ( ! [X2] : (k2_relat_1(sK2) != k2_relat_1(X2) | k6_partfun1(k2_relat_1(k4_relat_1(sK2))) != k5_relat_1(X2,k4_relat_1(sK2)) | k2_funct_1(k4_relat_1(sK2)) = X2 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) ) | (~spl4_1 | ~spl4_2 | ~spl4_3)),
% 2.22/0.68    inference(subsumption_resolution,[],[f276,f321])).
% 2.22/0.68  fof(f321,plain,(
% 2.22/0.68    v1_relat_1(k4_relat_1(sK2)) | ~spl4_3),
% 2.22/0.68    inference(avatar_component_clause,[],[f320])).
% 2.22/0.68  fof(f320,plain,(
% 2.22/0.68    spl4_3 <=> v1_relat_1(k4_relat_1(sK2))),
% 2.22/0.68    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 2.22/0.68  fof(f276,plain,(
% 2.22/0.68    ( ! [X2] : (k2_relat_1(sK2) != k2_relat_1(X2) | k6_partfun1(k2_relat_1(k4_relat_1(sK2))) != k5_relat_1(X2,k4_relat_1(sK2)) | k2_funct_1(k4_relat_1(sK2)) = X2 | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_relat_1(k4_relat_1(sK2))) ) | (~spl4_1 | ~spl4_2)),
% 2.22/0.68    inference(subsumption_resolution,[],[f275,f237])).
% 2.22/0.68  fof(f237,plain,(
% 2.22/0.68    v1_funct_1(k4_relat_1(sK2)) | (~spl4_1 | ~spl4_2)),
% 2.22/0.68    inference(subsumption_resolution,[],[f236,f208])).
% 2.22/0.68  fof(f236,plain,(
% 2.22/0.68    v1_funct_1(k4_relat_1(sK2)) | ~v1_relat_1(sK2) | ~spl4_2),
% 2.22/0.68    inference(subsumption_resolution,[],[f235,f70])).
% 2.22/0.68  fof(f235,plain,(
% 2.22/0.68    v1_funct_1(k4_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl4_2),
% 2.22/0.68    inference(subsumption_resolution,[],[f229,f78])).
% 2.22/0.68  fof(f229,plain,(
% 2.22/0.68    v1_funct_1(k4_relat_1(sK2)) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl4_2),
% 2.22/0.68    inference(superposition,[],[f93,f213])).
% 2.22/0.68  fof(f275,plain,(
% 2.22/0.68    ( ! [X2] : (k2_relat_1(sK2) != k2_relat_1(X2) | k6_partfun1(k2_relat_1(k4_relat_1(sK2))) != k5_relat_1(X2,k4_relat_1(sK2)) | k2_funct_1(k4_relat_1(sK2)) = X2 | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(k4_relat_1(sK2)) | ~v1_relat_1(k4_relat_1(sK2))) ) | (~spl4_1 | ~spl4_2)),
% 2.22/0.68    inference(subsumption_resolution,[],[f273,f240])).
% 2.22/0.68  fof(f240,plain,(
% 2.22/0.68    v2_funct_1(k4_relat_1(sK2)) | (~spl4_1 | ~spl4_2)),
% 2.22/0.68    inference(subsumption_resolution,[],[f239,f208])).
% 2.22/0.68  fof(f239,plain,(
% 2.22/0.68    v2_funct_1(k4_relat_1(sK2)) | ~v1_relat_1(sK2) | ~spl4_2),
% 2.22/0.68    inference(subsumption_resolution,[],[f238,f70])).
% 2.22/0.68  fof(f238,plain,(
% 2.22/0.68    v2_funct_1(k4_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl4_2),
% 2.22/0.68    inference(subsumption_resolution,[],[f230,f78])).
% 2.22/0.68  fof(f230,plain,(
% 2.22/0.68    v2_funct_1(k4_relat_1(sK2)) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl4_2),
% 2.22/0.68    inference(superposition,[],[f94,f213])).
% 2.22/0.68  fof(f94,plain,(
% 2.22/0.68    ( ! [X0] : (v2_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.22/0.68    inference(cnf_transformation,[],[f44])).
% 2.22/0.68  fof(f273,plain,(
% 2.22/0.68    ( ! [X2] : (k2_relat_1(sK2) != k2_relat_1(X2) | k6_partfun1(k2_relat_1(k4_relat_1(sK2))) != k5_relat_1(X2,k4_relat_1(sK2)) | k2_funct_1(k4_relat_1(sK2)) = X2 | ~v2_funct_1(k4_relat_1(sK2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(k4_relat_1(sK2)) | ~v1_relat_1(k4_relat_1(sK2))) ) | (~spl4_1 | ~spl4_2)),
% 2.22/0.68    inference(superposition,[],[f126,f270])).
% 2.22/0.68  fof(f126,plain,(
% 2.22/0.68    ( ! [X0,X1] : (k1_relat_1(X0) != k2_relat_1(X1) | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0)) | k2_funct_1(X0) = X1 | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.22/0.68    inference(definition_unfolding,[],[f82,f109])).
% 2.22/0.68  fof(f82,plain,(
% 2.22/0.68    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.22/0.68    inference(cnf_transformation,[],[f32])).
% 2.22/0.68  fof(f32,plain,(
% 2.22/0.68    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.22/0.68    inference(flattening,[],[f31])).
% 2.22/0.68  fof(f31,plain,(
% 2.22/0.68    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.22/0.68    inference(ennf_transformation,[],[f17])).
% 2.22/0.68  fof(f17,axiom,(
% 2.22/0.68    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0)) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 2.22/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_1)).
% 2.22/0.69  fof(f664,plain,(
% 2.22/0.69    sK3 = k4_relat_1(k4_relat_1(sK3)) | ~spl4_7),
% 2.22/0.69    inference(resolution,[],[f650,f123])).
% 2.22/0.69  fof(f123,plain,(
% 2.22/0.69    ( ! [X0] : (~v1_relat_1(X0) | k4_relat_1(k4_relat_1(X0)) = X0) )),
% 2.22/0.69    inference(cnf_transformation,[],[f62])).
% 2.22/0.69  fof(f62,plain,(
% 2.22/0.69    ! [X0] : (k4_relat_1(k4_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 2.22/0.69    inference(ennf_transformation,[],[f4])).
% 2.22/0.69  fof(f4,axiom,(
% 2.22/0.69    ! [X0] : (v1_relat_1(X0) => k4_relat_1(k4_relat_1(X0)) = X0)),
% 2.22/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).
% 2.22/0.69  fof(f848,plain,(
% 2.22/0.69    ~spl4_7 | spl4_9),
% 2.22/0.69    inference(avatar_contradiction_clause,[],[f847])).
% 2.22/0.69  fof(f847,plain,(
% 2.22/0.69    $false | (~spl4_7 | spl4_9)),
% 2.22/0.69    inference(subsumption_resolution,[],[f845,f650])).
% 2.22/0.69  fof(f845,plain,(
% 2.22/0.69    ~v1_relat_1(sK3) | spl4_9),
% 2.22/0.69    inference(resolution,[],[f839,f124])).
% 2.22/0.69  fof(f124,plain,(
% 2.22/0.69    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 2.22/0.69    inference(cnf_transformation,[],[f63])).
% 2.22/0.69  fof(f63,plain,(
% 2.22/0.69    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.22/0.69    inference(ennf_transformation,[],[f2])).
% 2.22/0.69  fof(f2,axiom,(
% 2.22/0.69    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 2.22/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).
% 2.22/0.69  fof(f839,plain,(
% 2.22/0.69    ~v1_relat_1(k4_relat_1(sK3)) | spl4_9),
% 2.22/0.69    inference(avatar_component_clause,[],[f837])).
% 2.22/0.69  fof(f660,plain,(
% 2.22/0.69    spl4_7),
% 2.22/0.69    inference(avatar_contradiction_clause,[],[f659])).
% 2.22/0.69  fof(f659,plain,(
% 2.22/0.69    $false | spl4_7),
% 2.22/0.69    inference(subsumption_resolution,[],[f658,f118])).
% 2.22/0.69  fof(f118,plain,(
% 2.22/0.69    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.22/0.69    inference(cnf_transformation,[],[f3])).
% 2.22/0.69  fof(f3,axiom,(
% 2.22/0.69    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.22/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 2.22/0.69  fof(f658,plain,(
% 2.22/0.69    ~v1_relat_1(k2_zfmisc_1(sK1,sK0)) | spl4_7),
% 2.22/0.69    inference(resolution,[],[f657,f75])).
% 2.22/0.69  fof(f657,plain,(
% 2.22/0.69    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl4_7),
% 2.22/0.69    inference(resolution,[],[f651,f117])).
% 2.22/0.69  fof(f117,plain,(
% 2.22/0.69    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.22/0.69    inference(cnf_transformation,[],[f60])).
% 2.22/0.69  fof(f60,plain,(
% 2.22/0.69    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.22/0.69    inference(ennf_transformation,[],[f1])).
% 2.22/0.69  fof(f1,axiom,(
% 2.22/0.69    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.22/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 2.22/0.69  fof(f651,plain,(
% 2.22/0.69    ~v1_relat_1(sK3) | spl4_7),
% 2.22/0.69    inference(avatar_component_clause,[],[f649])).
% 2.22/0.69  fof(f656,plain,(
% 2.22/0.69    ~spl4_7 | spl4_8 | ~spl4_1 | ~spl4_2 | ~spl4_6),
% 2.22/0.69    inference(avatar_split_clause,[],[f647,f451,f211,f207,f653,f649])).
% 2.22/0.69  fof(f647,plain,(
% 2.22/0.69    v2_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl4_1 | ~spl4_2 | ~spl4_6)),
% 2.22/0.69    inference(subsumption_resolution,[],[f646,f129])).
% 2.22/0.69  fof(f129,plain,(
% 2.22/0.69    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 2.22/0.69    inference(definition_unfolding,[],[f106,f109])).
% 2.22/0.69  fof(f106,plain,(
% 2.22/0.69    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 2.22/0.69    inference(cnf_transformation,[],[f11])).
% 2.22/0.69  fof(f11,axiom,(
% 2.22/0.69    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 2.22/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).
% 2.22/0.69  fof(f646,plain,(
% 2.22/0.69    ~v2_funct_1(k6_partfun1(sK0)) | v2_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl4_1 | ~spl4_2 | ~spl4_6)),
% 2.22/0.69    inference(forward_demodulation,[],[f645,f453])).
% 2.22/0.69  fof(f645,plain,(
% 2.22/0.69    v2_funct_1(sK3) | ~v2_funct_1(k5_relat_1(sK2,sK3)) | ~v1_relat_1(sK3) | (~spl4_1 | ~spl4_2)),
% 2.22/0.69    inference(subsumption_resolution,[],[f643,f73])).
% 2.22/0.69  fof(f643,plain,(
% 2.22/0.69    v2_funct_1(sK3) | ~v2_funct_1(k5_relat_1(sK2,sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl4_1 | ~spl4_2)),
% 2.22/0.69    inference(trivial_inequality_removal,[],[f642])).
% 2.22/0.69  fof(f642,plain,(
% 2.22/0.69    sK1 != sK1 | v2_funct_1(sK3) | ~v2_funct_1(k5_relat_1(sK2,sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl4_1 | ~spl4_2)),
% 2.22/0.69    inference(superposition,[],[f301,f260])).
% 2.22/0.69  fof(f301,plain,(
% 2.22/0.69    ( ! [X1] : (sK1 != k1_relat_1(X1) | v2_funct_1(X1) | ~v2_funct_1(k5_relat_1(sK2,X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) ) | (~spl4_1 | ~spl4_2)),
% 2.22/0.69    inference(subsumption_resolution,[],[f300,f208])).
% 2.22/0.69  fof(f300,plain,(
% 2.22/0.69    ( ! [X1] : (sK1 != k1_relat_1(X1) | v2_funct_1(X1) | ~v2_funct_1(k5_relat_1(sK2,X1)) | ~v1_relat_1(sK2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) ) | (~spl4_1 | ~spl4_2)),
% 2.22/0.69    inference(subsumption_resolution,[],[f298,f70])).
% 2.22/0.69  fof(f298,plain,(
% 2.22/0.69    ( ! [X1] : (sK1 != k1_relat_1(X1) | v2_funct_1(X1) | ~v2_funct_1(k5_relat_1(sK2,X1)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) ) | (~spl4_1 | ~spl4_2)),
% 2.22/0.69    inference(superposition,[],[f104,f289])).
% 2.22/0.69  fof(f104,plain,(
% 2.22/0.69    ( ! [X0,X1] : (k1_relat_1(X0) != k2_relat_1(X1) | v2_funct_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.22/0.69    inference(cnf_transformation,[],[f50])).
% 2.22/0.69  fof(f50,plain,(
% 2.22/0.69    ! [X0] : (! [X1] : ((v2_funct_1(X0) & v2_funct_1(X1)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.22/0.69    inference(flattening,[],[f49])).
% 2.22/0.69  fof(f49,plain,(
% 2.22/0.69    ! [X0] : (! [X1] : (((v2_funct_1(X0) & v2_funct_1(X1)) | (k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.22/0.69    inference(ennf_transformation,[],[f13])).
% 2.22/0.69  fof(f13,axiom,(
% 2.22/0.69    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(k5_relat_1(X1,X0))) => (v2_funct_1(X0) & v2_funct_1(X1)))))),
% 2.22/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_1)).
% 2.22/0.69  fof(f456,plain,(
% 2.22/0.69    spl4_5),
% 2.22/0.69    inference(avatar_contradiction_clause,[],[f455])).
% 2.22/0.69  fof(f455,plain,(
% 2.22/0.69    $false | spl4_5),
% 2.22/0.69    inference(subsumption_resolution,[],[f443,f449])).
% 2.22/0.69  fof(f449,plain,(
% 2.22/0.69    ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl4_5),
% 2.22/0.69    inference(avatar_component_clause,[],[f447])).
% 2.22/0.69  fof(f447,plain,(
% 2.22/0.69    spl4_5 <=> m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.22/0.69    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 2.22/0.69  fof(f443,plain,(
% 2.22/0.69    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.22/0.69    inference(subsumption_resolution,[],[f442,f70])).
% 2.22/0.69  fof(f442,plain,(
% 2.22/0.69    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK2)),
% 2.22/0.69    inference(subsumption_resolution,[],[f441,f72])).
% 2.22/0.69  fof(f441,plain,(
% 2.22/0.69    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2)),
% 2.22/0.69    inference(subsumption_resolution,[],[f440,f73])).
% 2.22/0.69  fof(f440,plain,(
% 2.22/0.69    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2)),
% 2.22/0.69    inference(subsumption_resolution,[],[f435,f75])).
% 2.22/0.69  fof(f435,plain,(
% 2.22/0.69    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2)),
% 2.22/0.69    inference(superposition,[],[f111,f340])).
% 2.22/0.69  fof(f340,plain,(
% 2.22/0.69    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)),
% 2.22/0.69    inference(subsumption_resolution,[],[f335,f73])).
% 2.22/0.69  fof(f335,plain,(
% 2.22/0.69    ~v1_funct_1(sK3) | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)),
% 2.22/0.69    inference(resolution,[],[f165,f75])).
% 2.22/0.69  fof(f165,plain,(
% 2.22/0.69    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X0) | k1_partfun1(sK0,sK1,X1,X2,sK2,X0) = k5_relat_1(sK2,X0)) )),
% 2.22/0.69    inference(subsumption_resolution,[],[f163,f70])).
% 2.22/0.69  fof(f163,plain,(
% 2.22/0.69    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X0) | k1_partfun1(sK0,sK1,X1,X2,sK2,X0) = k5_relat_1(sK2,X0) | ~v1_funct_1(sK2)) )),
% 2.22/0.69    inference(resolution,[],[f72,f112])).
% 2.22/0.69  fof(f112,plain,(
% 2.22/0.69    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~v1_funct_1(X4)) )),
% 2.22/0.69    inference(cnf_transformation,[],[f56])).
% 2.22/0.69  fof(f56,plain,(
% 2.22/0.69    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.22/0.69    inference(flattening,[],[f55])).
% 2.22/0.69  fof(f55,plain,(
% 2.22/0.69    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.22/0.69    inference(ennf_transformation,[],[f23])).
% 2.22/0.69  fof(f23,axiom,(
% 2.22/0.69    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 2.22/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 2.22/0.69  fof(f111,plain,(
% 2.22/0.69    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.22/0.69    inference(cnf_transformation,[],[f54])).
% 2.22/0.69  fof(f54,plain,(
% 2.22/0.69    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.22/0.69    inference(flattening,[],[f53])).
% 2.22/0.69  fof(f53,plain,(
% 2.22/0.69    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.22/0.69    inference(ennf_transformation,[],[f21])).
% 2.22/0.69  fof(f21,axiom,(
% 2.22/0.69    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 2.22/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 2.22/0.69  fof(f454,plain,(
% 2.22/0.69    ~spl4_5 | spl4_6 | ~spl4_1 | ~spl4_2),
% 2.22/0.69    inference(avatar_split_clause,[],[f445,f211,f207,f451,f447])).
% 2.22/0.69  fof(f445,plain,(
% 2.22/0.69    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | (~spl4_1 | ~spl4_2)),
% 2.22/0.69    inference(subsumption_resolution,[],[f444,f372])).
% 2.22/0.69  fof(f372,plain,(
% 2.22/0.69    m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | (~spl4_1 | ~spl4_2)),
% 2.22/0.69    inference(subsumption_resolution,[],[f371,f70])).
% 2.22/0.69  fof(f371,plain,(
% 2.22/0.69    m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK2) | (~spl4_1 | ~spl4_2)),
% 2.22/0.69    inference(subsumption_resolution,[],[f370,f72])).
% 2.22/0.69  fof(f370,plain,(
% 2.22/0.69    m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl4_1 | ~spl4_2)),
% 2.22/0.69    inference(subsumption_resolution,[],[f369,f237])).
% 2.22/0.69  fof(f369,plain,(
% 2.22/0.69    m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(k4_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl4_1 | ~spl4_2)),
% 2.22/0.69    inference(subsumption_resolution,[],[f364,f261])).
% 2.22/0.69  fof(f364,plain,(
% 2.22/0.69    m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(k4_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl4_1 | ~spl4_2)),
% 2.22/0.69    inference(superposition,[],[f111,f337])).
% 2.22/0.69  fof(f337,plain,(
% 2.22/0.69    k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,k4_relat_1(sK2)) | (~spl4_1 | ~spl4_2)),
% 2.22/0.69    inference(forward_demodulation,[],[f336,f262])).
% 2.22/0.69  fof(f262,plain,(
% 2.22/0.69    k6_partfun1(sK0) = k5_relat_1(sK2,k4_relat_1(sK2)) | ~spl4_2),
% 2.22/0.69    inference(forward_demodulation,[],[f192,f213])).
% 2.22/0.69  fof(f192,plain,(
% 2.22/0.69    k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 2.22/0.69    inference(subsumption_resolution,[],[f191,f70])).
% 2.22/0.69  fof(f191,plain,(
% 2.22/0.69    k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~v1_funct_1(sK2)),
% 2.22/0.69    inference(subsumption_resolution,[],[f190,f71])).
% 2.22/0.69  fof(f190,plain,(
% 2.22/0.69    k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 2.22/0.69    inference(subsumption_resolution,[],[f189,f72])).
% 2.22/0.69  fof(f189,plain,(
% 2.22/0.69    k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 2.22/0.69    inference(subsumption_resolution,[],[f188,f78])).
% 2.22/0.69  fof(f188,plain,(
% 2.22/0.69    ~v2_funct_1(sK2) | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 2.22/0.69    inference(subsumption_resolution,[],[f177,f80])).
% 2.22/0.69  fof(f177,plain,(
% 2.22/0.69    k1_xboole_0 = sK1 | ~v2_funct_1(sK2) | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 2.22/0.69    inference(trivial_inequality_removal,[],[f174])).
% 2.22/0.69  fof(f174,plain,(
% 2.22/0.69    sK1 != sK1 | k1_xboole_0 = sK1 | ~v2_funct_1(sK2) | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 2.22/0.69    inference(superposition,[],[f95,f76])).
% 2.22/0.69  fof(f95,plain,(
% 2.22/0.69    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.22/0.69    inference(cnf_transformation,[],[f46])).
% 2.22/0.69  fof(f46,plain,(
% 2.22/0.69    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.22/0.69    inference(flattening,[],[f45])).
% 2.22/0.69  fof(f45,plain,(
% 2.22/0.69    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.22/0.69    inference(ennf_transformation,[],[f26])).
% 2.22/0.69  fof(f26,axiom,(
% 2.22/0.69    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1)))),
% 2.22/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).
% 2.22/0.69  fof(f336,plain,(
% 2.22/0.69    k5_relat_1(sK2,k4_relat_1(sK2)) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,k4_relat_1(sK2)) | (~spl4_1 | ~spl4_2)),
% 2.22/0.69    inference(subsumption_resolution,[],[f332,f237])).
% 2.22/0.69  fof(f332,plain,(
% 2.22/0.69    ~v1_funct_1(k4_relat_1(sK2)) | k5_relat_1(sK2,k4_relat_1(sK2)) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,k4_relat_1(sK2)) | ~spl4_2),
% 2.22/0.69    inference(resolution,[],[f165,f261])).
% 2.22/0.69  fof(f444,plain,(
% 2.22/0.69    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.22/0.69    inference(resolution,[],[f433,f107])).
% 2.22/0.69  fof(f107,plain,(
% 2.22/0.69    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.22/0.69    inference(cnf_transformation,[],[f69])).
% 2.22/0.69  fof(f69,plain,(
% 2.22/0.69    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.22/0.69    inference(nnf_transformation,[],[f52])).
% 2.22/0.69  fof(f52,plain,(
% 2.22/0.69    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.22/0.69    inference(flattening,[],[f51])).
% 2.22/0.69  fof(f51,plain,(
% 2.22/0.69    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.22/0.69    inference(ennf_transformation,[],[f19])).
% 2.22/0.69  fof(f19,axiom,(
% 2.22/0.69    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 2.22/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 2.22/0.69  fof(f433,plain,(
% 2.22/0.69    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0))),
% 2.22/0.69    inference(backward_demodulation,[],[f77,f340])).
% 2.22/0.69  fof(f77,plain,(
% 2.22/0.69    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 2.22/0.69    inference(cnf_transformation,[],[f67])).
% 2.22/0.69  fof(f331,plain,(
% 2.22/0.69    ~spl4_1 | spl4_3),
% 2.22/0.69    inference(avatar_contradiction_clause,[],[f330])).
% 2.22/0.69  fof(f330,plain,(
% 2.22/0.69    $false | (~spl4_1 | spl4_3)),
% 2.22/0.69    inference(subsumption_resolution,[],[f328,f208])).
% 2.22/0.69  fof(f328,plain,(
% 2.22/0.69    ~v1_relat_1(sK2) | spl4_3),
% 2.22/0.69    inference(resolution,[],[f322,f124])).
% 2.22/0.69  fof(f322,plain,(
% 2.22/0.69    ~v1_relat_1(k4_relat_1(sK2)) | spl4_3),
% 2.22/0.69    inference(avatar_component_clause,[],[f320])).
% 2.22/0.69  fof(f327,plain,(
% 2.22/0.69    ~spl4_3 | spl4_4 | ~spl4_1 | ~spl4_2),
% 2.22/0.69    inference(avatar_split_clause,[],[f318,f211,f207,f324,f320])).
% 2.22/0.69  fof(f318,plain,(
% 2.22/0.69    sK2 = k2_funct_1(k4_relat_1(sK2)) | ~v1_relat_1(k4_relat_1(sK2)) | (~spl4_1 | ~spl4_2)),
% 2.22/0.69    inference(forward_demodulation,[],[f254,f220])).
% 2.22/0.69  fof(f220,plain,(
% 2.22/0.69    sK2 = k4_relat_1(k4_relat_1(sK2)) | ~spl4_1),
% 2.22/0.69    inference(resolution,[],[f208,f123])).
% 2.22/0.70  fof(f254,plain,(
% 2.22/0.70    k4_relat_1(k4_relat_1(sK2)) = k2_funct_1(k4_relat_1(sK2)) | ~v1_relat_1(k4_relat_1(sK2)) | (~spl4_1 | ~spl4_2)),
% 2.22/0.70    inference(subsumption_resolution,[],[f247,f237])).
% 2.22/0.70  fof(f247,plain,(
% 2.22/0.70    k4_relat_1(k4_relat_1(sK2)) = k2_funct_1(k4_relat_1(sK2)) | ~v1_funct_1(k4_relat_1(sK2)) | ~v1_relat_1(k4_relat_1(sK2)) | (~spl4_1 | ~spl4_2)),
% 2.22/0.70    inference(resolution,[],[f240,f89])).
% 2.22/0.70  fof(f219,plain,(
% 2.22/0.70    spl4_1),
% 2.22/0.70    inference(avatar_contradiction_clause,[],[f218])).
% 2.22/0.70  fof(f218,plain,(
% 2.22/0.70    $false | spl4_1),
% 2.22/0.70    inference(subsumption_resolution,[],[f217,f118])).
% 2.22/0.70  fof(f217,plain,(
% 2.22/0.70    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | spl4_1),
% 2.22/0.70    inference(resolution,[],[f215,f72])).
% 2.22/0.70  fof(f215,plain,(
% 2.22/0.70    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl4_1),
% 2.22/0.70    inference(resolution,[],[f209,f117])).
% 2.22/0.70  fof(f209,plain,(
% 2.22/0.70    ~v1_relat_1(sK2) | spl4_1),
% 2.22/0.70    inference(avatar_component_clause,[],[f207])).
% 2.22/0.70  fof(f214,plain,(
% 2.22/0.70    ~spl4_1 | spl4_2),
% 2.22/0.70    inference(avatar_split_clause,[],[f153,f211,f207])).
% 2.22/0.70  fof(f153,plain,(
% 2.22/0.70    k2_funct_1(sK2) = k4_relat_1(sK2) | ~v1_relat_1(sK2)),
% 2.22/0.70    inference(subsumption_resolution,[],[f146,f70])).
% 2.22/0.70  fof(f146,plain,(
% 2.22/0.70    k2_funct_1(sK2) = k4_relat_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 2.22/0.70    inference(resolution,[],[f78,f89])).
% 2.22/0.70  % SZS output end Proof for theBenchmark
% 2.22/0.70  % (31130)------------------------------
% 2.22/0.70  % (31130)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.22/0.70  % (31130)Termination reason: Refutation
% 2.22/0.70  
% 2.22/0.70  % (31130)Memory used [KB]: 11129
% 2.22/0.70  % (31130)Time elapsed: 0.250 s
% 2.22/0.70  % (31130)------------------------------
% 2.22/0.70  % (31130)------------------------------
% 2.22/0.70  % (31105)Success in time 0.334 s
%------------------------------------------------------------------------------
