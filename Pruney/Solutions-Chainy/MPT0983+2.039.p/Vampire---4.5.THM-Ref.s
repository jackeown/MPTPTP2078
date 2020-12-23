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
% DateTime   : Thu Dec  3 13:01:38 EST 2020

% Result     : Theorem 1.86s
% Output     : Refutation 1.86s
% Verified   : 
% Statistics : Number of formulae       :  171 ( 609 expanded)
%              Number of leaves         :   32 ( 193 expanded)
%              Depth                    :   22
%              Number of atoms          :  558 (4054 expanded)
%              Number of equality atoms :   88 ( 165 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f945,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f109,f179,f186,f740,f780,f804,f823,f852,f856,f864,f940])).

fof(f940,plain,
    ( spl4_1
    | ~ spl4_4
    | ~ spl4_8 ),
    inference(avatar_contradiction_clause,[],[f939])).

fof(f939,plain,
    ( $false
    | spl4_1
    | ~ spl4_4
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f917,f198])).

fof(f198,plain,
    ( v2_funct_1(k1_xboole_0)
    | ~ spl4_8 ),
    inference(superposition,[],[f90,f191])).

fof(f191,plain,
    ( k1_xboole_0 = k6_partfun1(k1_xboole_0)
    | ~ spl4_8 ),
    inference(resolution,[],[f189,f112])).

fof(f112,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f79,f59])).

fof(f59,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

fof(f189,plain,
    ( v1_xboole_0(k6_partfun1(k1_xboole_0))
    | ~ spl4_8 ),
    inference(resolution,[],[f175,f110])).

fof(f110,plain,(
    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[],[f63,f96])).

fof(f96,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f63,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f175,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
        | v1_xboole_0(X1) )
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f174])).

fof(f174,plain,
    ( spl4_8
  <=> ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
        | v1_xboole_0(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f90,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f60,f61])).

fof(f61,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f60,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_funct_1)).

fof(f917,plain,
    ( ~ v2_funct_1(k1_xboole_0)
    | spl4_1
    | ~ spl4_4 ),
    inference(backward_demodulation,[],[f104,f879])).

fof(f879,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_4 ),
    inference(resolution,[],[f159,f112])).

fof(f159,plain,
    ( v1_xboole_0(sK2)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f157])).

fof(f157,plain,
    ( spl4_4
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f104,plain,
    ( ~ v2_funct_1(sK2)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl4_1
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f864,plain,
    ( spl4_43
    | ~ spl4_44
    | spl4_1 ),
    inference(avatar_split_clause,[],[f721,f102,f727,f723])).

fof(f723,plain,
    ( spl4_43
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).

fof(f727,plain,
    ( spl4_44
  <=> v2_funct_1(k5_relat_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).

fof(f721,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | k1_xboole_0 = sK0
    | spl4_1 ),
    inference(subsumption_resolution,[],[f720,f51])).

fof(f51,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,
    ( ( ~ v2_funct_2(sK3,sK0)
      | ~ v2_funct_1(sK2) )
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_2(sK3,sK1,sK0)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f42,f41])).

fof(f41,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ( ~ v2_funct_2(X3,X0)
              | ~ v2_funct_1(X2) )
            & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ( ~ v2_funct_2(X3,sK0)
            | ~ v2_funct_1(sK2) )
          & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
          & v1_funct_2(X3,sK1,sK0)
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ? [X3] :
        ( ( ~ v2_funct_2(X3,sK0)
          | ~ v2_funct_1(sK2) )
        & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        & v1_funct_2(X3,sK1,sK0)
        & v1_funct_1(X3) )
   => ( ( ~ v2_funct_2(sK3,sK0)
        | ~ v2_funct_1(sK2) )
      & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      & v1_funct_2(sK3,sK1,sK0)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( ~ v2_funct_2(X3,X0)
            | ~ v2_funct_1(X2) )
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( ~ v2_funct_2(X3,X0)
            | ~ v2_funct_1(X2) )
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2] :
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
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
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

fof(f720,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | k1_xboole_0 = sK0
    | ~ v1_funct_1(sK2)
    | spl4_1 ),
    inference(subsumption_resolution,[],[f719,f52])).

fof(f52,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f719,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | k1_xboole_0 = sK0
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl4_1 ),
    inference(subsumption_resolution,[],[f718,f53])).

fof(f53,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f43])).

fof(f718,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | k1_xboole_0 = sK0
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl4_1 ),
    inference(subsumption_resolution,[],[f717,f54])).

fof(f54,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f717,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | k1_xboole_0 = sK0
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl4_1 ),
    inference(subsumption_resolution,[],[f716,f55])).

fof(f55,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f716,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | k1_xboole_0 = sK0
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl4_1 ),
    inference(subsumption_resolution,[],[f715,f56])).

fof(f56,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f43])).

fof(f715,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | k1_xboole_0 = sK0
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl4_1 ),
    inference(subsumption_resolution,[],[f706,f104])).

fof(f706,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | k1_xboole_0 = sK0
    | v2_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(superposition,[],[f83,f545])).

fof(f545,plain,(
    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f539,f51])).

fof(f539,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f264,f53])).

fof(f264,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | k1_partfun1(X3,X4,sK1,sK0,X5,sK3) = k5_relat_1(X5,sK3)
      | ~ v1_funct_1(X5) ) ),
    inference(subsumption_resolution,[],[f259,f54])).

fof(f259,plain,(
    ! [X4,X5,X3] :
      ( k1_partfun1(X3,X4,sK1,sK0,X5,sK3) = k5_relat_1(X5,sK3)
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_1(X5) ) ),
    inference(resolution,[],[f87,f56])).

fof(f87,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
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

fof(f83,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
      | k1_xboole_0 = X2
      | v2_funct_1(X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X4,X1,X2)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( v2_funct_1(X3)
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( v2_funct_1(X3)
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
         => ( v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
           => ( v2_funct_1(X3)
              | ( k1_xboole_0 != X1
                & k1_xboole_0 = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_funct_2)).

fof(f856,plain,
    ( ~ spl4_3
    | spl4_4 ),
    inference(avatar_split_clause,[],[f824,f157,f153])).

fof(f153,plain,
    ( spl4_3
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f824,plain,
    ( v1_xboole_0(sK2)
    | ~ v1_xboole_0(sK0) ),
    inference(resolution,[],[f53,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X2)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

fof(f852,plain,
    ( spl4_2
    | ~ spl4_46 ),
    inference(avatar_contradiction_clause,[],[f851])).

fof(f851,plain,
    ( $false
    | spl4_2
    | ~ spl4_46 ),
    inference(subsumption_resolution,[],[f850,f115])).

fof(f115,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f80,f56])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f850,plain,
    ( ~ v1_relat_1(sK3)
    | spl4_2
    | ~ spl4_46 ),
    inference(subsumption_resolution,[],[f843,f108])).

fof(f108,plain,
    ( ~ v2_funct_2(sK3,sK0)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl4_2
  <=> v2_funct_2(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f843,plain,
    ( v2_funct_2(sK3,sK0)
    | ~ v1_relat_1(sK3)
    | ~ spl4_46 ),
    inference(superposition,[],[f190,f779])).

fof(f779,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ spl4_46 ),
    inference(avatar_component_clause,[],[f777])).

fof(f777,plain,
    ( spl4_46
  <=> sK0 = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).

fof(f190,plain,(
    ! [X1] :
      ( v2_funct_2(X1,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f93,f123])).

fof(f123,plain,(
    ! [X2] :
      ( v5_relat_1(X2,k2_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f68,f94])).

fof(f94,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f93,plain,(
    ! [X1] :
      ( v2_funct_2(X1,k2_relat_1(X1))
      | ~ v5_relat_1(X1,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( v2_funct_2(X1,X0)
      | k2_relat_1(X1) != X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

fof(f823,plain,(
    spl4_45 ),
    inference(avatar_contradiction_clause,[],[f822])).

fof(f822,plain,
    ( $false
    | spl4_45 ),
    inference(subsumption_resolution,[],[f821,f115])).

fof(f821,plain,
    ( ~ v1_relat_1(sK3)
    | spl4_45 ),
    inference(subsumption_resolution,[],[f820,f142])).

fof(f142,plain,(
    v5_relat_1(sK3,sK0) ),
    inference(resolution,[],[f82,f56])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f820,plain,
    ( ~ v5_relat_1(sK3,sK0)
    | ~ v1_relat_1(sK3)
    | spl4_45 ),
    inference(resolution,[],[f775,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f775,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK0)
    | spl4_45 ),
    inference(avatar_component_clause,[],[f773])).

fof(f773,plain,
    ( spl4_45
  <=> r1_tarski(k2_relat_1(sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).

fof(f804,plain,
    ( spl4_3
    | ~ spl4_43 ),
    inference(avatar_contradiction_clause,[],[f803])).

fof(f803,plain,
    ( $false
    | spl4_3
    | ~ spl4_43 ),
    inference(subsumption_resolution,[],[f787,f59])).

fof(f787,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl4_3
    | ~ spl4_43 ),
    inference(backward_demodulation,[],[f155,f725])).

fof(f725,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_43 ),
    inference(avatar_component_clause,[],[f723])).

fof(f155,plain,
    ( ~ v1_xboole_0(sK0)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f153])).

fof(f780,plain,
    ( ~ spl4_45
    | spl4_46 ),
    inference(avatar_split_clause,[],[f771,f777,f773])).

fof(f771,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ r1_tarski(k2_relat_1(sK3),sK0) ),
    inference(forward_demodulation,[],[f770,f91])).

fof(f91,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f65,f61])).

fof(f65,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f770,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK0)
    | k2_relat_1(sK3) = k2_relat_1(k6_partfun1(sK0)) ),
    inference(forward_demodulation,[],[f769,f91])).

fof(f769,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),k2_relat_1(k6_partfun1(sK0)))
    | k2_relat_1(sK3) = k2_relat_1(k6_partfun1(sK0)) ),
    inference(subsumption_resolution,[],[f768,f115])).

fof(f768,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),k2_relat_1(k6_partfun1(sK0)))
    | k2_relat_1(sK3) = k2_relat_1(k6_partfun1(sK0))
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f757,f114])).

fof(f114,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f80,f53])).

fof(f757,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),k2_relat_1(k6_partfun1(sK0)))
    | ~ v1_relat_1(sK2)
    | k2_relat_1(sK3) = k2_relat_1(k6_partfun1(sK0))
    | ~ v1_relat_1(sK3) ),
    inference(superposition,[],[f211,f732])).

fof(f732,plain,(
    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) ),
    inference(global_subsumption,[],[f710,f731])).

fof(f731,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f703,f247])).

fof(f247,plain,(
    ! [X2,X3] :
      ( ~ r2_relset_1(X2,X2,X3,k6_partfun1(X2))
      | k6_partfun1(X2) = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ) ),
    inference(resolution,[],[f85,f63])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f703,plain,(
    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0)) ),
    inference(backward_demodulation,[],[f57,f545])).

fof(f57,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f43])).

fof(f710,plain,(
    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f709,f51])).

fof(f709,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f708,f53])).

fof(f708,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f707,f54])).

fof(f707,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f704,f56])).

fof(f704,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(superposition,[],[f89,f545])).

fof(f89,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f211,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(k2_relat_1(X2),k2_relat_1(k5_relat_1(X3,X2)))
      | ~ v1_relat_1(X3)
      | k2_relat_1(X2) = k2_relat_1(k5_relat_1(X3,X2))
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f66,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

fof(f740,plain,(
    spl4_44 ),
    inference(avatar_contradiction_clause,[],[f739])).

fof(f739,plain,
    ( $false
    | spl4_44 ),
    inference(subsumption_resolution,[],[f733,f90])).

fof(f733,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | spl4_44 ),
    inference(backward_demodulation,[],[f729,f732])).

fof(f729,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | spl4_44 ),
    inference(avatar_component_clause,[],[f727])).

fof(f186,plain,
    ( spl4_7
    | spl4_8 ),
    inference(avatar_split_clause,[],[f184,f174,f171])).

fof(f171,plain,
    ( spl4_7
  <=> ! [X0] : ~ v1_xboole_0(X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f184,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0))
      | v1_xboole_0(X3)
      | ~ v1_xboole_0(X2) ) ),
    inference(superposition,[],[f70,f97])).

fof(f97,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | v1_xboole_0(X2)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

fof(f179,plain,(
    ~ spl4_7 ),
    inference(avatar_contradiction_clause,[],[f178])).

fof(f178,plain,
    ( $false
    | ~ spl4_7 ),
    inference(resolution,[],[f172,f59])).

fof(f172,plain,
    ( ! [X0] : ~ v1_xboole_0(X0)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f171])).

fof(f109,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f58,f106,f102])).

fof(f58,plain,
    ( ~ v2_funct_2(sK3,sK0)
    | ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f43])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:35:16 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.50  % (12972)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.50  % (12998)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.50  % (12988)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.51  % (12973)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.51  % (12979)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.51  % (12978)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.52  % (12996)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.52  % (12982)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.53  % (12979)Refutation not found, incomplete strategy% (12979)------------------------------
% 0.21/0.53  % (12979)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (12969)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.53  % (12980)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.53  % (12979)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (12979)Memory used [KB]: 10874
% 0.21/0.53  % (12979)Time elapsed: 0.117 s
% 0.21/0.53  % (12979)------------------------------
% 0.21/0.53  % (12979)------------------------------
% 0.21/0.53  % (12991)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.53  % (12971)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.53  % (12983)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.53  % (12970)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.53  % (12995)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (12986)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.54  % (12974)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.54  % (12977)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.54  % (12992)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.54  % (12975)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (12984)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.54  % (12997)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.55  % (12976)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.55  % (12987)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.55  % (12989)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.55  % (12993)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.55  % (12981)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.55  % (12994)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.55  % (12985)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.55  % (12997)Refutation not found, incomplete strategy% (12997)------------------------------
% 0.21/0.55  % (12997)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (12990)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.56  % (12985)Refutation not found, incomplete strategy% (12985)------------------------------
% 0.21/0.56  % (12985)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (12985)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  % (12997)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (12997)Memory used [KB]: 10874
% 0.21/0.57  % (12997)Time elapsed: 0.142 s
% 0.21/0.57  % (12997)------------------------------
% 0.21/0.57  % (12997)------------------------------
% 0.21/0.57  
% 0.21/0.57  % (12985)Memory used [KB]: 10746
% 0.21/0.57  % (12985)Time elapsed: 0.151 s
% 0.21/0.57  % (12985)------------------------------
% 0.21/0.57  % (12985)------------------------------
% 1.86/0.61  % (12975)Refutation found. Thanks to Tanya!
% 1.86/0.61  % SZS status Theorem for theBenchmark
% 1.86/0.61  % SZS output start Proof for theBenchmark
% 1.86/0.61  fof(f945,plain,(
% 1.86/0.61    $false),
% 1.86/0.61    inference(avatar_sat_refutation,[],[f109,f179,f186,f740,f780,f804,f823,f852,f856,f864,f940])).
% 1.86/0.61  fof(f940,plain,(
% 1.86/0.61    spl4_1 | ~spl4_4 | ~spl4_8),
% 1.86/0.61    inference(avatar_contradiction_clause,[],[f939])).
% 1.86/0.61  fof(f939,plain,(
% 1.86/0.61    $false | (spl4_1 | ~spl4_4 | ~spl4_8)),
% 1.86/0.61    inference(subsumption_resolution,[],[f917,f198])).
% 1.86/0.61  fof(f198,plain,(
% 1.86/0.61    v2_funct_1(k1_xboole_0) | ~spl4_8),
% 1.86/0.61    inference(superposition,[],[f90,f191])).
% 1.86/0.61  fof(f191,plain,(
% 1.86/0.61    k1_xboole_0 = k6_partfun1(k1_xboole_0) | ~spl4_8),
% 1.86/0.61    inference(resolution,[],[f189,f112])).
% 1.86/0.61  fof(f112,plain,(
% 1.86/0.61    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 1.86/0.61    inference(resolution,[],[f79,f59])).
% 1.86/0.61  fof(f59,plain,(
% 1.86/0.61    v1_xboole_0(k1_xboole_0)),
% 1.86/0.61    inference(cnf_transformation,[],[f1])).
% 1.86/0.61  fof(f1,axiom,(
% 1.86/0.61    v1_xboole_0(k1_xboole_0)),
% 1.86/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.86/0.61  fof(f79,plain,(
% 1.86/0.61    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 1.86/0.61    inference(cnf_transformation,[],[f30])).
% 1.86/0.61  fof(f30,plain,(
% 1.86/0.61    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 1.86/0.61    inference(ennf_transformation,[],[f3])).
% 1.86/0.61  fof(f3,axiom,(
% 1.86/0.61    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 1.86/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).
% 1.86/0.61  fof(f189,plain,(
% 1.86/0.61    v1_xboole_0(k6_partfun1(k1_xboole_0)) | ~spl4_8),
% 1.86/0.61    inference(resolution,[],[f175,f110])).
% 1.86/0.61  fof(f110,plain,(
% 1.86/0.61    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))),
% 1.86/0.61    inference(superposition,[],[f63,f96])).
% 1.86/0.61  fof(f96,plain,(
% 1.86/0.61    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.86/0.61    inference(equality_resolution,[],[f78])).
% 1.86/0.61  fof(f78,plain,(
% 1.86/0.61    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 1.86/0.61    inference(cnf_transformation,[],[f49])).
% 1.86/0.61  fof(f49,plain,(
% 1.86/0.61    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.86/0.61    inference(flattening,[],[f48])).
% 1.86/0.61  fof(f48,plain,(
% 1.86/0.61    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.86/0.61    inference(nnf_transformation,[],[f4])).
% 1.86/0.61  fof(f4,axiom,(
% 1.86/0.61    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.86/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.86/0.61  fof(f63,plain,(
% 1.86/0.61    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.86/0.61    inference(cnf_transformation,[],[f16])).
% 1.86/0.61  fof(f16,axiom,(
% 1.86/0.61    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 1.86/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 1.86/0.61  fof(f175,plain,(
% 1.86/0.61    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | v1_xboole_0(X1)) ) | ~spl4_8),
% 1.86/0.61    inference(avatar_component_clause,[],[f174])).
% 1.86/0.61  fof(f174,plain,(
% 1.86/0.61    spl4_8 <=> ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | v1_xboole_0(X1))),
% 1.86/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 1.86/0.61  fof(f90,plain,(
% 1.86/0.61    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 1.86/0.61    inference(definition_unfolding,[],[f60,f61])).
% 1.86/0.61  fof(f61,plain,(
% 1.86/0.61    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.86/0.61    inference(cnf_transformation,[],[f18])).
% 1.86/0.61  fof(f18,axiom,(
% 1.86/0.61    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.86/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.86/0.61  fof(f60,plain,(
% 1.86/0.61    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 1.86/0.61    inference(cnf_transformation,[],[f8])).
% 1.86/0.61  fof(f8,axiom,(
% 1.86/0.61    ! [X0] : v2_funct_1(k6_relat_1(X0))),
% 1.86/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_funct_1)).
% 1.86/0.61  fof(f917,plain,(
% 1.86/0.61    ~v2_funct_1(k1_xboole_0) | (spl4_1 | ~spl4_4)),
% 1.86/0.61    inference(backward_demodulation,[],[f104,f879])).
% 1.86/0.61  fof(f879,plain,(
% 1.86/0.61    k1_xboole_0 = sK2 | ~spl4_4),
% 1.86/0.61    inference(resolution,[],[f159,f112])).
% 1.86/0.61  fof(f159,plain,(
% 1.86/0.61    v1_xboole_0(sK2) | ~spl4_4),
% 1.86/0.61    inference(avatar_component_clause,[],[f157])).
% 1.86/0.61  fof(f157,plain,(
% 1.86/0.61    spl4_4 <=> v1_xboole_0(sK2)),
% 1.86/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.86/0.61  fof(f104,plain,(
% 1.86/0.61    ~v2_funct_1(sK2) | spl4_1),
% 1.86/0.61    inference(avatar_component_clause,[],[f102])).
% 1.86/0.61  fof(f102,plain,(
% 1.86/0.61    spl4_1 <=> v2_funct_1(sK2)),
% 1.86/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.86/0.61  fof(f864,plain,(
% 1.86/0.61    spl4_43 | ~spl4_44 | spl4_1),
% 1.86/0.61    inference(avatar_split_clause,[],[f721,f102,f727,f723])).
% 1.86/0.61  fof(f723,plain,(
% 1.86/0.61    spl4_43 <=> k1_xboole_0 = sK0),
% 1.86/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).
% 1.86/0.61  fof(f727,plain,(
% 1.86/0.61    spl4_44 <=> v2_funct_1(k5_relat_1(sK2,sK3))),
% 1.86/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).
% 1.86/0.61  fof(f721,plain,(
% 1.86/0.61    ~v2_funct_1(k5_relat_1(sK2,sK3)) | k1_xboole_0 = sK0 | spl4_1),
% 1.86/0.61    inference(subsumption_resolution,[],[f720,f51])).
% 1.86/0.61  fof(f51,plain,(
% 1.86/0.61    v1_funct_1(sK2)),
% 1.86/0.61    inference(cnf_transformation,[],[f43])).
% 1.86/0.61  fof(f43,plain,(
% 1.86/0.61    ((~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 1.86/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f42,f41])).
% 1.86/0.61  fof(f41,plain,(
% 1.86/0.61    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : ((~v2_funct_2(X3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 1.86/0.61    introduced(choice_axiom,[])).
% 1.86/0.61  fof(f42,plain,(
% 1.86/0.61    ? [X3] : ((~v2_funct_2(X3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) => ((~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3))),
% 1.86/0.61    introduced(choice_axiom,[])).
% 1.86/0.61  fof(f23,plain,(
% 1.86/0.61    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.86/0.61    inference(flattening,[],[f22])).
% 1.86/0.61  fof(f22,plain,(
% 1.86/0.61    ? [X0,X1,X2] : (? [X3] : (((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.86/0.61    inference(ennf_transformation,[],[f21])).
% 1.86/0.61  fof(f21,negated_conjecture,(
% 1.86/0.61    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 1.86/0.61    inference(negated_conjecture,[],[f20])).
% 1.86/0.61  fof(f20,conjecture,(
% 1.86/0.61    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 1.86/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_funct_2)).
% 1.86/0.61  fof(f720,plain,(
% 1.86/0.61    ~v2_funct_1(k5_relat_1(sK2,sK3)) | k1_xboole_0 = sK0 | ~v1_funct_1(sK2) | spl4_1),
% 1.86/0.61    inference(subsumption_resolution,[],[f719,f52])).
% 1.86/0.61  fof(f52,plain,(
% 1.86/0.61    v1_funct_2(sK2,sK0,sK1)),
% 1.86/0.61    inference(cnf_transformation,[],[f43])).
% 1.86/0.61  fof(f719,plain,(
% 1.86/0.61    ~v2_funct_1(k5_relat_1(sK2,sK3)) | k1_xboole_0 = sK0 | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | spl4_1),
% 1.86/0.61    inference(subsumption_resolution,[],[f718,f53])).
% 1.86/0.61  fof(f53,plain,(
% 1.86/0.61    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.86/0.61    inference(cnf_transformation,[],[f43])).
% 1.86/0.61  fof(f718,plain,(
% 1.86/0.61    ~v2_funct_1(k5_relat_1(sK2,sK3)) | k1_xboole_0 = sK0 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | spl4_1),
% 1.86/0.61    inference(subsumption_resolution,[],[f717,f54])).
% 1.86/0.61  fof(f54,plain,(
% 1.86/0.61    v1_funct_1(sK3)),
% 1.86/0.61    inference(cnf_transformation,[],[f43])).
% 1.86/0.61  fof(f717,plain,(
% 1.86/0.61    ~v2_funct_1(k5_relat_1(sK2,sK3)) | k1_xboole_0 = sK0 | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | spl4_1),
% 1.86/0.61    inference(subsumption_resolution,[],[f716,f55])).
% 1.86/0.61  fof(f55,plain,(
% 1.86/0.61    v1_funct_2(sK3,sK1,sK0)),
% 1.86/0.61    inference(cnf_transformation,[],[f43])).
% 1.86/0.61  fof(f716,plain,(
% 1.86/0.61    ~v2_funct_1(k5_relat_1(sK2,sK3)) | k1_xboole_0 = sK0 | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | spl4_1),
% 1.86/0.61    inference(subsumption_resolution,[],[f715,f56])).
% 1.86/0.61  fof(f56,plain,(
% 1.86/0.61    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.86/0.61    inference(cnf_transformation,[],[f43])).
% 1.86/0.61  fof(f715,plain,(
% 1.86/0.61    ~v2_funct_1(k5_relat_1(sK2,sK3)) | k1_xboole_0 = sK0 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | spl4_1),
% 1.86/0.61    inference(subsumption_resolution,[],[f706,f104])).
% 1.86/0.61  fof(f706,plain,(
% 1.86/0.61    ~v2_funct_1(k5_relat_1(sK2,sK3)) | k1_xboole_0 = sK0 | v2_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 1.86/0.61    inference(superposition,[],[f83,f545])).
% 1.86/0.61  fof(f545,plain,(
% 1.86/0.61    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)),
% 1.86/0.61    inference(subsumption_resolution,[],[f539,f51])).
% 1.86/0.61  fof(f539,plain,(
% 1.86/0.61    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) | ~v1_funct_1(sK2)),
% 1.86/0.61    inference(resolution,[],[f264,f53])).
% 1.86/0.61  fof(f264,plain,(
% 1.86/0.61    ( ! [X4,X5,X3] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | k1_partfun1(X3,X4,sK1,sK0,X5,sK3) = k5_relat_1(X5,sK3) | ~v1_funct_1(X5)) )),
% 1.86/0.61    inference(subsumption_resolution,[],[f259,f54])).
% 1.86/0.61  fof(f259,plain,(
% 1.86/0.61    ( ! [X4,X5,X3] : (k1_partfun1(X3,X4,sK1,sK0,X5,sK3) = k5_relat_1(X5,sK3) | ~v1_funct_1(sK3) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_1(X5)) )),
% 1.86/0.61    inference(resolution,[],[f87,f56])).
% 1.86/0.61  fof(f87,plain,(
% 1.86/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.86/0.61    inference(cnf_transformation,[],[f38])).
% 1.86/0.61  fof(f38,plain,(
% 1.86/0.61    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.86/0.61    inference(flattening,[],[f37])).
% 1.86/0.61  fof(f37,plain,(
% 1.86/0.61    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.86/0.61    inference(ennf_transformation,[],[f17])).
% 1.86/0.61  fof(f17,axiom,(
% 1.86/0.61    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.86/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 1.86/0.61  fof(f83,plain,(
% 1.86/0.61    ( ! [X4,X2,X0,X3,X1] : (~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | k1_xboole_0 = X2 | v2_funct_1(X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.86/0.61    inference(cnf_transformation,[],[f34])).
% 1.86/0.61  fof(f34,plain,(
% 1.86/0.61    ! [X0,X1,X2,X3] : (! [X4] : (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.86/0.61    inference(flattening,[],[f33])).
% 1.86/0.61  fof(f33,plain,(
% 1.86/0.61    ! [X0,X1,X2,X3] : (! [X4] : (((v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.86/0.61    inference(ennf_transformation,[],[f19])).
% 1.86/0.61  fof(f19,axiom,(
% 1.86/0.61    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) => (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 1.86/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_funct_2)).
% 1.86/0.61  fof(f856,plain,(
% 1.86/0.61    ~spl4_3 | spl4_4),
% 1.86/0.61    inference(avatar_split_clause,[],[f824,f157,f153])).
% 1.86/0.61  fof(f153,plain,(
% 1.86/0.61    spl4_3 <=> v1_xboole_0(sK0)),
% 1.86/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.86/0.61  fof(f824,plain,(
% 1.86/0.61    v1_xboole_0(sK2) | ~v1_xboole_0(sK0)),
% 1.86/0.61    inference(resolution,[],[f53,f69])).
% 1.86/0.61  fof(f69,plain,(
% 1.86/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X2) | ~v1_xboole_0(X0)) )),
% 1.86/0.61    inference(cnf_transformation,[],[f26])).
% 1.86/0.61  fof(f26,plain,(
% 1.86/0.61    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 1.86/0.61    inference(ennf_transformation,[],[f11])).
% 1.86/0.61  fof(f11,axiom,(
% 1.86/0.61    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_xboole_0(X2)))),
% 1.86/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).
% 1.86/0.61  fof(f852,plain,(
% 1.86/0.61    spl4_2 | ~spl4_46),
% 1.86/0.61    inference(avatar_contradiction_clause,[],[f851])).
% 1.86/0.61  fof(f851,plain,(
% 1.86/0.61    $false | (spl4_2 | ~spl4_46)),
% 1.86/0.61    inference(subsumption_resolution,[],[f850,f115])).
% 1.86/0.61  fof(f115,plain,(
% 1.86/0.61    v1_relat_1(sK3)),
% 1.86/0.61    inference(resolution,[],[f80,f56])).
% 1.86/0.61  fof(f80,plain,(
% 1.86/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.86/0.61    inference(cnf_transformation,[],[f31])).
% 1.86/0.61  fof(f31,plain,(
% 1.86/0.61    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.86/0.61    inference(ennf_transformation,[],[f9])).
% 1.86/0.61  fof(f9,axiom,(
% 1.86/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.86/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.86/0.61  fof(f850,plain,(
% 1.86/0.61    ~v1_relat_1(sK3) | (spl4_2 | ~spl4_46)),
% 1.86/0.61    inference(subsumption_resolution,[],[f843,f108])).
% 1.86/0.61  fof(f108,plain,(
% 1.86/0.61    ~v2_funct_2(sK3,sK0) | spl4_2),
% 1.86/0.61    inference(avatar_component_clause,[],[f106])).
% 1.86/0.61  fof(f106,plain,(
% 1.86/0.61    spl4_2 <=> v2_funct_2(sK3,sK0)),
% 1.86/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.86/0.61  fof(f843,plain,(
% 1.86/0.61    v2_funct_2(sK3,sK0) | ~v1_relat_1(sK3) | ~spl4_46),
% 1.86/0.61    inference(superposition,[],[f190,f779])).
% 1.86/0.61  fof(f779,plain,(
% 1.86/0.61    sK0 = k2_relat_1(sK3) | ~spl4_46),
% 1.86/0.61    inference(avatar_component_clause,[],[f777])).
% 1.86/0.61  fof(f777,plain,(
% 1.86/0.61    spl4_46 <=> sK0 = k2_relat_1(sK3)),
% 1.86/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).
% 1.86/0.61  fof(f190,plain,(
% 1.86/0.61    ( ! [X1] : (v2_funct_2(X1,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.86/0.61    inference(subsumption_resolution,[],[f93,f123])).
% 1.86/0.61  fof(f123,plain,(
% 1.86/0.61    ( ! [X2] : (v5_relat_1(X2,k2_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 1.86/0.61    inference(resolution,[],[f68,f94])).
% 1.86/0.61  fof(f94,plain,(
% 1.86/0.61    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.86/0.61    inference(equality_resolution,[],[f74])).
% 1.86/0.61  fof(f74,plain,(
% 1.86/0.61    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.86/0.61    inference(cnf_transformation,[],[f47])).
% 1.86/0.61  fof(f47,plain,(
% 1.86/0.61    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.86/0.61    inference(flattening,[],[f46])).
% 1.86/0.61  fof(f46,plain,(
% 1.86/0.61    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.86/0.61    inference(nnf_transformation,[],[f2])).
% 1.86/0.61  fof(f2,axiom,(
% 1.86/0.61    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.86/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.86/0.61  fof(f68,plain,(
% 1.86/0.61    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.86/0.61    inference(cnf_transformation,[],[f44])).
% 1.86/0.61  fof(f44,plain,(
% 1.86/0.61    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.86/0.61    inference(nnf_transformation,[],[f25])).
% 1.86/0.61  fof(f25,plain,(
% 1.86/0.61    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.86/0.61    inference(ennf_transformation,[],[f5])).
% 1.86/0.61  fof(f5,axiom,(
% 1.86/0.61    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.86/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 1.86/0.61  fof(f93,plain,(
% 1.86/0.61    ( ! [X1] : (v2_funct_2(X1,k2_relat_1(X1)) | ~v5_relat_1(X1,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.86/0.61    inference(equality_resolution,[],[f72])).
% 1.86/0.61  fof(f72,plain,(
% 1.86/0.61    ( ! [X0,X1] : (v2_funct_2(X1,X0) | k2_relat_1(X1) != X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.86/0.61    inference(cnf_transformation,[],[f45])).
% 1.86/0.61  fof(f45,plain,(
% 1.86/0.61    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.86/0.61    inference(nnf_transformation,[],[f29])).
% 1.86/0.61  fof(f29,plain,(
% 1.86/0.61    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.86/0.61    inference(flattening,[],[f28])).
% 1.86/0.61  fof(f28,plain,(
% 1.86/0.61    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.86/0.61    inference(ennf_transformation,[],[f14])).
% 1.86/0.61  fof(f14,axiom,(
% 1.86/0.61    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 1.86/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).
% 1.86/0.61  fof(f823,plain,(
% 1.86/0.61    spl4_45),
% 1.86/0.61    inference(avatar_contradiction_clause,[],[f822])).
% 1.86/0.61  fof(f822,plain,(
% 1.86/0.61    $false | spl4_45),
% 1.86/0.61    inference(subsumption_resolution,[],[f821,f115])).
% 1.86/0.61  fof(f821,plain,(
% 1.86/0.61    ~v1_relat_1(sK3) | spl4_45),
% 1.86/0.61    inference(subsumption_resolution,[],[f820,f142])).
% 1.86/0.61  fof(f142,plain,(
% 1.86/0.61    v5_relat_1(sK3,sK0)),
% 1.86/0.61    inference(resolution,[],[f82,f56])).
% 1.86/0.61  fof(f82,plain,(
% 1.86/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.86/0.61    inference(cnf_transformation,[],[f32])).
% 1.86/0.61  fof(f32,plain,(
% 1.86/0.61    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.86/0.61    inference(ennf_transformation,[],[f10])).
% 1.86/0.61  fof(f10,axiom,(
% 1.86/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.86/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.86/0.61  fof(f820,plain,(
% 1.86/0.61    ~v5_relat_1(sK3,sK0) | ~v1_relat_1(sK3) | spl4_45),
% 1.86/0.61    inference(resolution,[],[f775,f67])).
% 1.86/0.61  fof(f67,plain,(
% 1.86/0.61    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.86/0.61    inference(cnf_transformation,[],[f44])).
% 1.86/0.61  fof(f775,plain,(
% 1.86/0.61    ~r1_tarski(k2_relat_1(sK3),sK0) | spl4_45),
% 1.86/0.61    inference(avatar_component_clause,[],[f773])).
% 1.86/0.61  fof(f773,plain,(
% 1.86/0.61    spl4_45 <=> r1_tarski(k2_relat_1(sK3),sK0)),
% 1.86/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).
% 1.86/0.61  fof(f804,plain,(
% 1.86/0.61    spl4_3 | ~spl4_43),
% 1.86/0.61    inference(avatar_contradiction_clause,[],[f803])).
% 1.86/0.61  fof(f803,plain,(
% 1.86/0.61    $false | (spl4_3 | ~spl4_43)),
% 1.86/0.61    inference(subsumption_resolution,[],[f787,f59])).
% 1.86/0.61  fof(f787,plain,(
% 1.86/0.61    ~v1_xboole_0(k1_xboole_0) | (spl4_3 | ~spl4_43)),
% 1.86/0.61    inference(backward_demodulation,[],[f155,f725])).
% 1.86/0.61  fof(f725,plain,(
% 1.86/0.61    k1_xboole_0 = sK0 | ~spl4_43),
% 1.86/0.61    inference(avatar_component_clause,[],[f723])).
% 1.86/0.61  fof(f155,plain,(
% 1.86/0.61    ~v1_xboole_0(sK0) | spl4_3),
% 1.86/0.61    inference(avatar_component_clause,[],[f153])).
% 1.86/0.61  fof(f780,plain,(
% 1.86/0.61    ~spl4_45 | spl4_46),
% 1.86/0.61    inference(avatar_split_clause,[],[f771,f777,f773])).
% 1.86/0.61  fof(f771,plain,(
% 1.86/0.61    sK0 = k2_relat_1(sK3) | ~r1_tarski(k2_relat_1(sK3),sK0)),
% 1.86/0.61    inference(forward_demodulation,[],[f770,f91])).
% 1.86/0.61  fof(f91,plain,(
% 1.86/0.61    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 1.86/0.61    inference(definition_unfolding,[],[f65,f61])).
% 1.86/0.61  fof(f65,plain,(
% 1.86/0.61    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 1.86/0.61    inference(cnf_transformation,[],[f7])).
% 1.86/0.61  fof(f7,axiom,(
% 1.86/0.61    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.86/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 1.86/0.61  fof(f770,plain,(
% 1.86/0.61    ~r1_tarski(k2_relat_1(sK3),sK0) | k2_relat_1(sK3) = k2_relat_1(k6_partfun1(sK0))),
% 1.86/0.61    inference(forward_demodulation,[],[f769,f91])).
% 1.86/0.61  fof(f769,plain,(
% 1.86/0.61    ~r1_tarski(k2_relat_1(sK3),k2_relat_1(k6_partfun1(sK0))) | k2_relat_1(sK3) = k2_relat_1(k6_partfun1(sK0))),
% 1.86/0.61    inference(subsumption_resolution,[],[f768,f115])).
% 1.86/0.61  fof(f768,plain,(
% 1.86/0.61    ~r1_tarski(k2_relat_1(sK3),k2_relat_1(k6_partfun1(sK0))) | k2_relat_1(sK3) = k2_relat_1(k6_partfun1(sK0)) | ~v1_relat_1(sK3)),
% 1.86/0.61    inference(subsumption_resolution,[],[f757,f114])).
% 1.86/0.61  fof(f114,plain,(
% 1.86/0.61    v1_relat_1(sK2)),
% 1.86/0.61    inference(resolution,[],[f80,f53])).
% 1.86/0.61  fof(f757,plain,(
% 1.86/0.61    ~r1_tarski(k2_relat_1(sK3),k2_relat_1(k6_partfun1(sK0))) | ~v1_relat_1(sK2) | k2_relat_1(sK3) = k2_relat_1(k6_partfun1(sK0)) | ~v1_relat_1(sK3)),
% 1.86/0.61    inference(superposition,[],[f211,f732])).
% 1.86/0.62  fof(f732,plain,(
% 1.86/0.62    k6_partfun1(sK0) = k5_relat_1(sK2,sK3)),
% 1.86/0.62    inference(global_subsumption,[],[f710,f731])).
% 1.86/0.62  fof(f731,plain,(
% 1.86/0.62    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.86/0.62    inference(resolution,[],[f703,f247])).
% 1.86/0.62  fof(f247,plain,(
% 1.86/0.62    ( ! [X2,X3] : (~r2_relset_1(X2,X2,X3,k6_partfun1(X2)) | k6_partfun1(X2) = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))) )),
% 1.86/0.62    inference(resolution,[],[f85,f63])).
% 1.86/0.62  fof(f85,plain,(
% 1.86/0.62    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.86/0.62    inference(cnf_transformation,[],[f50])).
% 1.86/0.62  fof(f50,plain,(
% 1.86/0.62    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.86/0.62    inference(nnf_transformation,[],[f36])).
% 1.86/0.62  fof(f36,plain,(
% 1.86/0.62    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.86/0.62    inference(flattening,[],[f35])).
% 1.86/0.62  fof(f35,plain,(
% 1.86/0.62    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.86/0.62    inference(ennf_transformation,[],[f13])).
% 1.86/0.62  fof(f13,axiom,(
% 1.86/0.62    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.86/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.86/0.62  fof(f703,plain,(
% 1.86/0.62    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0))),
% 1.86/0.62    inference(backward_demodulation,[],[f57,f545])).
% 1.86/0.62  fof(f57,plain,(
% 1.86/0.62    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 1.86/0.62    inference(cnf_transformation,[],[f43])).
% 1.86/0.62  fof(f710,plain,(
% 1.86/0.62    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.86/0.62    inference(subsumption_resolution,[],[f709,f51])).
% 1.86/0.62  fof(f709,plain,(
% 1.86/0.62    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK2)),
% 1.86/0.62    inference(subsumption_resolution,[],[f708,f53])).
% 1.86/0.62  fof(f708,plain,(
% 1.86/0.62    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2)),
% 1.86/0.62    inference(subsumption_resolution,[],[f707,f54])).
% 1.86/0.62  fof(f707,plain,(
% 1.86/0.62    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2)),
% 1.86/0.62    inference(subsumption_resolution,[],[f704,f56])).
% 1.86/0.62  fof(f704,plain,(
% 1.86/0.62    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2)),
% 1.86/0.62    inference(superposition,[],[f89,f545])).
% 1.86/0.62  fof(f89,plain,(
% 1.86/0.62    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.86/0.62    inference(cnf_transformation,[],[f40])).
% 1.86/0.62  fof(f40,plain,(
% 1.86/0.62    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.86/0.62    inference(flattening,[],[f39])).
% 1.86/0.62  fof(f39,plain,(
% 1.86/0.62    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.86/0.62    inference(ennf_transformation,[],[f15])).
% 1.86/0.62  fof(f15,axiom,(
% 1.86/0.62    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 1.86/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 1.86/0.62  fof(f211,plain,(
% 1.86/0.62    ( ! [X2,X3] : (~r1_tarski(k2_relat_1(X2),k2_relat_1(k5_relat_1(X3,X2))) | ~v1_relat_1(X3) | k2_relat_1(X2) = k2_relat_1(k5_relat_1(X3,X2)) | ~v1_relat_1(X2)) )),
% 1.86/0.62    inference(resolution,[],[f66,f75])).
% 1.86/0.62  fof(f75,plain,(
% 1.86/0.62    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.86/0.62    inference(cnf_transformation,[],[f47])).
% 1.86/0.62  fof(f66,plain,(
% 1.86/0.62    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.86/0.62    inference(cnf_transformation,[],[f24])).
% 1.86/0.62  fof(f24,plain,(
% 1.86/0.62    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.86/0.62    inference(ennf_transformation,[],[f6])).
% 1.86/0.62  fof(f6,axiom,(
% 1.86/0.62    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 1.86/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).
% 1.86/0.62  fof(f740,plain,(
% 1.86/0.62    spl4_44),
% 1.86/0.62    inference(avatar_contradiction_clause,[],[f739])).
% 1.86/0.62  fof(f739,plain,(
% 1.86/0.62    $false | spl4_44),
% 1.86/0.62    inference(subsumption_resolution,[],[f733,f90])).
% 1.86/0.62  fof(f733,plain,(
% 1.86/0.62    ~v2_funct_1(k6_partfun1(sK0)) | spl4_44),
% 1.86/0.62    inference(backward_demodulation,[],[f729,f732])).
% 1.86/0.62  fof(f729,plain,(
% 1.86/0.62    ~v2_funct_1(k5_relat_1(sK2,sK3)) | spl4_44),
% 1.86/0.62    inference(avatar_component_clause,[],[f727])).
% 1.86/0.62  fof(f186,plain,(
% 1.86/0.62    spl4_7 | spl4_8),
% 1.86/0.62    inference(avatar_split_clause,[],[f184,f174,f171])).
% 1.86/0.62  fof(f171,plain,(
% 1.86/0.62    spl4_7 <=> ! [X0] : ~v1_xboole_0(X0)),
% 1.86/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 1.86/0.62  fof(f184,plain,(
% 1.86/0.62    ( ! [X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0)) | v1_xboole_0(X3) | ~v1_xboole_0(X2)) )),
% 1.86/0.62    inference(superposition,[],[f70,f97])).
% 1.86/0.62  fof(f97,plain,(
% 1.86/0.62    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.86/0.62    inference(equality_resolution,[],[f77])).
% 1.86/0.62  fof(f77,plain,(
% 1.86/0.62    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 1.86/0.62    inference(cnf_transformation,[],[f49])).
% 1.86/0.62  fof(f70,plain,(
% 1.86/0.62    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | v1_xboole_0(X2) | ~v1_xboole_0(X0)) )),
% 1.86/0.62    inference(cnf_transformation,[],[f27])).
% 1.86/0.62  fof(f27,plain,(
% 1.86/0.62    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 1.86/0.62    inference(ennf_transformation,[],[f12])).
% 1.86/0.62  fof(f12,axiom,(
% 1.86/0.62    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 1.86/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).
% 1.86/0.62  fof(f179,plain,(
% 1.86/0.62    ~spl4_7),
% 1.86/0.62    inference(avatar_contradiction_clause,[],[f178])).
% 1.86/0.62  fof(f178,plain,(
% 1.86/0.62    $false | ~spl4_7),
% 1.86/0.62    inference(resolution,[],[f172,f59])).
% 1.86/0.62  fof(f172,plain,(
% 1.86/0.62    ( ! [X0] : (~v1_xboole_0(X0)) ) | ~spl4_7),
% 1.86/0.62    inference(avatar_component_clause,[],[f171])).
% 1.86/0.62  fof(f109,plain,(
% 1.86/0.62    ~spl4_1 | ~spl4_2),
% 1.86/0.62    inference(avatar_split_clause,[],[f58,f106,f102])).
% 1.86/0.62  fof(f58,plain,(
% 1.86/0.62    ~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)),
% 1.86/0.62    inference(cnf_transformation,[],[f43])).
% 1.86/0.62  % SZS output end Proof for theBenchmark
% 1.86/0.62  % (12975)------------------------------
% 1.86/0.62  % (12975)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.86/0.62  % (12975)Termination reason: Refutation
% 1.86/0.62  
% 1.86/0.62  % (12975)Memory used [KB]: 11385
% 1.86/0.62  % (12975)Time elapsed: 0.176 s
% 1.86/0.62  % (12975)------------------------------
% 1.86/0.62  % (12975)------------------------------
% 1.86/0.62  % (12968)Success in time 0.262 s
%------------------------------------------------------------------------------
