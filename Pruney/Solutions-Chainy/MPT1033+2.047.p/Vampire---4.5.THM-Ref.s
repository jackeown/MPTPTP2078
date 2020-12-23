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
% DateTime   : Thu Dec  3 13:06:49 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 347 expanded)
%              Number of leaves         :   13 ( 114 expanded)
%              Depth                    :   17
%              Number of atoms          :  433 (2819 expanded)
%              Number of equality atoms :   61 ( 576 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f270,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f44,f63,f80,f89,f126,f141,f267])).

fof(f267,plain,(
    ~ spl5_4 ),
    inference(avatar_contradiction_clause,[],[f266])).

fof(f266,plain,
    ( $false
    | ~ spl5_4 ),
    inference(trivial_inequality_removal,[],[f265])).

fof(f265,plain,
    ( k1_funct_1(sK2,sK4(sK0,sK2,sK2)) != k1_funct_1(sK2,sK4(sK0,sK2,sK2))
    | ~ spl5_4 ),
    inference(forward_demodulation,[],[f264,f62])).

fof(f62,plain,
    ( sK2 = sK3
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl5_4
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f264,plain,
    ( k1_funct_1(sK3,sK4(sK0,sK3,sK2)) != k1_funct_1(sK2,sK4(sK0,sK3,sK2))
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f225,f153])).

fof(f153,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK2)
    | ~ spl5_4 ),
    inference(superposition,[],[f27,f62])).

fof(f27,plain,(
    ~ r2_relset_1(sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK3)
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_partfun1(sK2,sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f7,f15,f14])).

fof(f14,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ~ r2_relset_1(X0,X1,X2,X3)
            & ( k1_xboole_0 = X0
              | k1_xboole_0 != X1 )
            & r1_partfun1(X2,X3)
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ~ r2_relset_1(sK0,sK1,sK2,X3)
          & ( k1_xboole_0 = sK0
            | k1_xboole_0 != sK1 )
          & r1_partfun1(sK2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
          & v1_funct_2(X3,sK0,sK1)
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ? [X3] :
        ( ~ r2_relset_1(sK0,sK1,sK2,X3)
        & ( k1_xboole_0 = sK0
          | k1_xboole_0 != sK1 )
        & r1_partfun1(sK2,X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        & v1_funct_2(X3,sK0,sK1)
        & v1_funct_1(X3) )
   => ( ~ r2_relset_1(sK0,sK1,sK2,sK3)
      & ( k1_xboole_0 = sK0
        | k1_xboole_0 != sK1 )
      & r1_partfun1(sK2,sK3)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & r1_partfun1(X2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & r1_partfun1(X2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X3,X0,X1)
              & v1_funct_1(X3) )
           => ( r1_partfun1(X2,X3)
             => ( r2_relset_1(X0,X1,X2,X3)
                | ( k1_xboole_0 != X0
                  & k1_xboole_0 = X1 ) ) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( r1_partfun1(X2,X3)
           => ( r2_relset_1(X0,X1,X2,X3)
              | ( k1_xboole_0 != X0
                & k1_xboole_0 = X1 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_2)).

fof(f225,plain,
    ( r2_relset_1(sK0,sK1,sK2,sK2)
    | k1_funct_1(sK3,sK4(sK0,sK3,sK2)) != k1_funct_1(sK2,sK4(sK0,sK3,sK2))
    | ~ spl5_4 ),
    inference(forward_demodulation,[],[f224,f62])).

fof(f224,plain,
    ( r2_relset_1(sK0,sK1,sK3,sK2)
    | k1_funct_1(sK3,sK4(sK0,sK3,sK2)) != k1_funct_1(sK2,sK4(sK0,sK3,sK2)) ),
    inference(subsumption_resolution,[],[f223,f22])).

fof(f22,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f16])).

fof(f223,plain,
    ( r2_relset_1(sK0,sK1,sK3,sK2)
    | k1_funct_1(sK3,sK4(sK0,sK3,sK2)) != k1_funct_1(sK2,sK4(sK0,sK3,sK2))
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f213,f23])).

fof(f23,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f213,plain,
    ( r2_relset_1(sK0,sK1,sK3,sK2)
    | k1_funct_1(sK3,sK4(sK0,sK3,sK2)) != k1_funct_1(sK2,sK4(sK0,sK3,sK2))
    | ~ v1_funct_2(sK3,sK0,sK1)
    | ~ v1_funct_1(sK3) ),
    inference(resolution,[],[f73,f24])).

fof(f24,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f16])).

fof(f73,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | r2_relset_1(sK0,sK1,X0,sK2)
      | k1_funct_1(X0,sK4(sK0,X0,sK2)) != k1_funct_1(sK2,sK4(sK0,X0,sK2))
      | ~ v1_funct_2(X0,sK0,sK1)
      | ~ v1_funct_1(X0) ) ),
    inference(subsumption_resolution,[],[f72,f19])).

fof(f19,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f72,plain,(
    ! [X0] :
      ( k1_funct_1(X0,sK4(sK0,X0,sK2)) != k1_funct_1(sK2,sK4(sK0,X0,sK2))
      | r2_relset_1(sK0,sK1,X0,sK2)
      | ~ v1_funct_1(sK2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_2(X0,sK0,sK1)
      | ~ v1_funct_1(X0) ) ),
    inference(subsumption_resolution,[],[f70,f20])).

fof(f20,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f70,plain,(
    ! [X0] :
      ( k1_funct_1(X0,sK4(sK0,X0,sK2)) != k1_funct_1(sK2,sK4(sK0,X0,sK2))
      | r2_relset_1(sK0,sK1,X0,sK2)
      | ~ v1_funct_2(sK2,sK0,sK1)
      | ~ v1_funct_1(sK2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_2(X0,sK0,sK1)
      | ~ v1_funct_1(X0) ) ),
    inference(resolution,[],[f29,f21])).

fof(f21,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f16])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_funct_1(X2,sK4(X0,X2,X3)) != k1_funct_1(X3,sK4(X0,X2,X3))
      | r2_relset_1(X0,X1,X2,X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r2_relset_1(X0,X1,X2,X3)
          | ( k1_funct_1(X2,sK4(X0,X2,X3)) != k1_funct_1(X3,sK4(X0,X2,X3))
            & m1_subset_1(sK4(X0,X2,X3),X0) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f9,f17])).

fof(f17,plain,(
    ! [X3,X2,X0] :
      ( ? [X4] :
          ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
          & m1_subset_1(X4,X0) )
     => ( k1_funct_1(X2,sK4(X0,X2,X3)) != k1_funct_1(X3,sK4(X0,X2,X3))
        & m1_subset_1(sK4(X0,X2,X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r2_relset_1(X0,X1,X2,X3)
          | ? [X4] :
              ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
              & m1_subset_1(X4,X0) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r2_relset_1(X0,X1,X2,X3)
          | ? [X4] :
              ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
              & m1_subset_1(X4,X0) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( ! [X4] :
                ( m1_subset_1(X4,X0)
               => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) )
           => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_funct_2)).

fof(f141,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | spl5_5 ),
    inference(avatar_contradiction_clause,[],[f140])).

fof(f140,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_2
    | spl5_5 ),
    inference(subsumption_resolution,[],[f139,f19])).

fof(f139,plain,
    ( ~ v1_funct_1(sK2)
    | ~ spl5_1
    | ~ spl5_2
    | spl5_5 ),
    inference(subsumption_resolution,[],[f138,f107])).

fof(f107,plain,
    ( v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f102,f43])).

fof(f43,plain,
    ( k1_xboole_0 = sK0
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f41])).

fof(f41,plain,
    ( spl5_2
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f102,plain,
    ( v1_funct_2(sK2,sK0,k1_xboole_0)
    | ~ spl5_1 ),
    inference(superposition,[],[f20,f38])).

fof(f38,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f37])).

fof(f37,plain,
    ( spl5_1
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f138,plain,
    ( ~ v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(sK2)
    | ~ spl5_1
    | ~ spl5_2
    | spl5_5 ),
    inference(subsumption_resolution,[],[f134,f97])).

fof(f97,plain,
    ( ~ v1_partfun1(sK2,k1_xboole_0)
    | ~ spl5_2
    | spl5_5 ),
    inference(forward_demodulation,[],[f84,f43])).

fof(f84,plain,
    ( ~ v1_partfun1(sK2,sK0)
    | spl5_5 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl5_5
  <=> v1_partfun1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f134,plain,
    ( v1_partfun1(sK2,k1_xboole_0)
    | ~ v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(sK2)
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(resolution,[],[f104,f35])).

fof(f35,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | v1_partfun1(X2,k1_xboole_0)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(duplicate_literal_removal,[],[f33])).

fof(f33,plain,(
    ! [X2,X1] :
      ( v1_partfun1(X2,k1_xboole_0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v1_partfun1(X2,X0)
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_funct_2)).

fof(f104,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f99,f43])).

fof(f99,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl5_1 ),
    inference(superposition,[],[f21,f38])).

fof(f126,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | spl5_6 ),
    inference(avatar_contradiction_clause,[],[f125])).

fof(f125,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_2
    | spl5_6 ),
    inference(subsumption_resolution,[],[f124,f22])).

fof(f124,plain,
    ( ~ v1_funct_1(sK3)
    | ~ spl5_1
    | ~ spl5_2
    | spl5_6 ),
    inference(subsumption_resolution,[],[f123,f106])).

fof(f106,plain,
    ( v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f101,f43])).

fof(f101,plain,
    ( v1_funct_2(sK3,sK0,k1_xboole_0)
    | ~ spl5_1 ),
    inference(superposition,[],[f23,f38])).

fof(f123,plain,
    ( ~ v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(sK3)
    | ~ spl5_1
    | ~ spl5_2
    | spl5_6 ),
    inference(subsumption_resolution,[],[f119,f96])).

fof(f96,plain,
    ( ~ v1_partfun1(sK3,k1_xboole_0)
    | ~ spl5_2
    | spl5_6 ),
    inference(forward_demodulation,[],[f88,f43])).

fof(f88,plain,
    ( ~ v1_partfun1(sK3,sK0)
    | spl5_6 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl5_6
  <=> v1_partfun1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f119,plain,
    ( v1_partfun1(sK3,k1_xboole_0)
    | ~ v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(sK3)
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(resolution,[],[f103,f35])).

fof(f103,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f98,f43])).

fof(f98,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl5_1 ),
    inference(superposition,[],[f24,f38])).

fof(f89,plain,
    ( ~ spl5_5
    | ~ spl5_6
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f77,f57,f86,f82])).

fof(f57,plain,
    ( spl5_3
  <=> ! [X1,X0] :
        ( ~ v1_partfun1(sK3,X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_partfun1(sK2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f77,plain,
    ( ~ v1_partfun1(sK3,sK0)
    | ~ v1_partfun1(sK2,sK0)
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f76,f21])).

fof(f76,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_partfun1(sK3,sK0)
    | ~ v1_partfun1(sK2,sK0)
    | ~ spl5_3 ),
    inference(resolution,[],[f58,f24])).

fof(f58,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_partfun1(sK3,X0)
        | ~ v1_partfun1(sK2,X0) )
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f57])).

fof(f80,plain,
    ( spl5_1
    | ~ spl5_3 ),
    inference(avatar_contradiction_clause,[],[f79])).

fof(f79,plain,
    ( $false
    | spl5_1
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f78,f49])).

fof(f49,plain,
    ( v1_partfun1(sK2,sK0)
    | spl5_1 ),
    inference(subsumption_resolution,[],[f48,f19])).

fof(f48,plain,
    ( v1_partfun1(sK2,sK0)
    | ~ v1_funct_1(sK2)
    | spl5_1 ),
    inference(subsumption_resolution,[],[f47,f20])).

fof(f47,plain,
    ( v1_partfun1(sK2,sK0)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl5_1 ),
    inference(subsumption_resolution,[],[f45,f39])).

fof(f39,plain,
    ( k1_xboole_0 != sK1
    | spl5_1 ),
    inference(avatar_component_clause,[],[f37])).

fof(f45,plain,
    ( k1_xboole_0 = sK1
    | v1_partfun1(sK2,sK0)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f34,f21])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(duplicate_literal_removal,[],[f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f78,plain,
    ( ~ v1_partfun1(sK2,sK0)
    | spl5_1
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f77,f52])).

fof(f52,plain,
    ( v1_partfun1(sK3,sK0)
    | spl5_1 ),
    inference(subsumption_resolution,[],[f51,f22])).

fof(f51,plain,
    ( v1_partfun1(sK3,sK0)
    | ~ v1_funct_1(sK3)
    | spl5_1 ),
    inference(subsumption_resolution,[],[f50,f23])).

fof(f50,plain,
    ( v1_partfun1(sK3,sK0)
    | ~ v1_funct_2(sK3,sK0,sK1)
    | ~ v1_funct_1(sK3)
    | spl5_1 ),
    inference(subsumption_resolution,[],[f46,f39])).

fof(f46,plain,
    ( k1_xboole_0 = sK1
    | v1_partfun1(sK3,sK0)
    | ~ v1_funct_2(sK3,sK0,sK1)
    | ~ v1_funct_1(sK3) ),
    inference(resolution,[],[f34,f24])).

fof(f63,plain,
    ( spl5_3
    | spl5_4 ),
    inference(avatar_split_clause,[],[f55,f60,f57])).

fof(f55,plain,(
    ! [X0,X1] :
      ( sK2 = sK3
      | ~ v1_partfun1(sK3,X0)
      | ~ v1_partfun1(sK2,X0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(subsumption_resolution,[],[f54,f19])).

fof(f54,plain,(
    ! [X0,X1] :
      ( sK2 = sK3
      | ~ v1_partfun1(sK3,X0)
      | ~ v1_partfun1(sK2,X0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(sK2) ) ),
    inference(subsumption_resolution,[],[f53,f22])).

fof(f53,plain,(
    ! [X0,X1] :
      ( sK2 = sK3
      | ~ v1_partfun1(sK3,X0)
      | ~ v1_partfun1(sK2,X0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(sK2) ) ),
    inference(resolution,[],[f32,f25])).

fof(f25,plain,(
    r1_partfun1(sK2,sK3) ),
    inference(cnf_transformation,[],[f16])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_partfun1(X2,X3)
      | X2 = X3
      | ~ v1_partfun1(X3,X0)
      | ~ v1_partfun1(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( X2 = X3
          | ~ r1_partfun1(X2,X3)
          | ~ v1_partfun1(X3,X0)
          | ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( X2 = X3
          | ~ r1_partfun1(X2,X3)
          | ~ v1_partfun1(X3,X0)
          | ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_1(X3) )
         => ( ( r1_partfun1(X2,X3)
              & v1_partfun1(X3,X0)
              & v1_partfun1(X2,X0) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_partfun1)).

fof(f44,plain,
    ( ~ spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f26,f41,f37])).

fof(f26,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n015.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:58:08 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.49  % (10317)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.49  % (10325)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.50  % (10317)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f270,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(avatar_sat_refutation,[],[f44,f63,f80,f89,f126,f141,f267])).
% 0.22/0.50  fof(f267,plain,(
% 0.22/0.50    ~spl5_4),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f266])).
% 0.22/0.50  fof(f266,plain,(
% 0.22/0.50    $false | ~spl5_4),
% 0.22/0.50    inference(trivial_inequality_removal,[],[f265])).
% 0.22/0.50  fof(f265,plain,(
% 0.22/0.50    k1_funct_1(sK2,sK4(sK0,sK2,sK2)) != k1_funct_1(sK2,sK4(sK0,sK2,sK2)) | ~spl5_4),
% 0.22/0.50    inference(forward_demodulation,[],[f264,f62])).
% 0.22/0.50  fof(f62,plain,(
% 0.22/0.50    sK2 = sK3 | ~spl5_4),
% 0.22/0.50    inference(avatar_component_clause,[],[f60])).
% 0.22/0.50  fof(f60,plain,(
% 0.22/0.50    spl5_4 <=> sK2 = sK3),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.22/0.50  fof(f264,plain,(
% 0.22/0.50    k1_funct_1(sK3,sK4(sK0,sK3,sK2)) != k1_funct_1(sK2,sK4(sK0,sK3,sK2)) | ~spl5_4),
% 0.22/0.50    inference(subsumption_resolution,[],[f225,f153])).
% 0.22/0.50  fof(f153,plain,(
% 0.22/0.50    ~r2_relset_1(sK0,sK1,sK2,sK2) | ~spl5_4),
% 0.22/0.50    inference(superposition,[],[f27,f62])).
% 0.22/0.50  fof(f27,plain,(
% 0.22/0.50    ~r2_relset_1(sK0,sK1,sK2,sK3)),
% 0.22/0.50    inference(cnf_transformation,[],[f16])).
% 0.22/0.50  fof(f16,plain,(
% 0.22/0.50    (~r2_relset_1(sK0,sK1,sK2,sK3) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_partfun1(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f7,f15,f14])).
% 0.22/0.50  fof(f14,plain,(
% 0.22/0.50    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_partfun1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (~r2_relset_1(sK0,sK1,sK2,X3) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_partfun1(sK2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(X3,sK0,sK1) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f15,plain,(
% 0.22/0.50    ? [X3] : (~r2_relset_1(sK0,sK1,sK2,X3) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_partfun1(sK2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(X3,sK0,sK1) & v1_funct_1(X3)) => (~r2_relset_1(sK0,sK1,sK2,sK3) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_partfun1(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f7,plain,(
% 0.22/0.50    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_partfun1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.22/0.50    inference(flattening,[],[f6])).
% 0.22/0.50  fof(f6,plain,(
% 0.22/0.50    ? [X0,X1,X2] : (? [X3] : (((~r2_relset_1(X0,X1,X2,X3) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_partfun1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.22/0.50    inference(ennf_transformation,[],[f5])).
% 0.22/0.50  fof(f5,negated_conjecture,(
% 0.22/0.50    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_partfun1(X2,X3) => (r2_relset_1(X0,X1,X2,X3) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)))))),
% 0.22/0.50    inference(negated_conjecture,[],[f4])).
% 0.22/0.50  fof(f4,conjecture,(
% 0.22/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_partfun1(X2,X3) => (r2_relset_1(X0,X1,X2,X3) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_2)).
% 0.22/0.50  fof(f225,plain,(
% 0.22/0.50    r2_relset_1(sK0,sK1,sK2,sK2) | k1_funct_1(sK3,sK4(sK0,sK3,sK2)) != k1_funct_1(sK2,sK4(sK0,sK3,sK2)) | ~spl5_4),
% 0.22/0.50    inference(forward_demodulation,[],[f224,f62])).
% 0.22/0.50  fof(f224,plain,(
% 0.22/0.50    r2_relset_1(sK0,sK1,sK3,sK2) | k1_funct_1(sK3,sK4(sK0,sK3,sK2)) != k1_funct_1(sK2,sK4(sK0,sK3,sK2))),
% 0.22/0.50    inference(subsumption_resolution,[],[f223,f22])).
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    v1_funct_1(sK3)),
% 0.22/0.50    inference(cnf_transformation,[],[f16])).
% 0.22/0.50  fof(f223,plain,(
% 0.22/0.50    r2_relset_1(sK0,sK1,sK3,sK2) | k1_funct_1(sK3,sK4(sK0,sK3,sK2)) != k1_funct_1(sK2,sK4(sK0,sK3,sK2)) | ~v1_funct_1(sK3)),
% 0.22/0.50    inference(subsumption_resolution,[],[f213,f23])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    v1_funct_2(sK3,sK0,sK1)),
% 0.22/0.50    inference(cnf_transformation,[],[f16])).
% 0.22/0.50  fof(f213,plain,(
% 0.22/0.50    r2_relset_1(sK0,sK1,sK3,sK2) | k1_funct_1(sK3,sK4(sK0,sK3,sK2)) != k1_funct_1(sK2,sK4(sK0,sK3,sK2)) | ~v1_funct_2(sK3,sK0,sK1) | ~v1_funct_1(sK3)),
% 0.22/0.50    inference(resolution,[],[f73,f24])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.50    inference(cnf_transformation,[],[f16])).
% 0.22/0.50  fof(f73,plain,(
% 0.22/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | r2_relset_1(sK0,sK1,X0,sK2) | k1_funct_1(X0,sK4(sK0,X0,sK2)) != k1_funct_1(sK2,sK4(sK0,X0,sK2)) | ~v1_funct_2(X0,sK0,sK1) | ~v1_funct_1(X0)) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f72,f19])).
% 0.22/0.50  fof(f19,plain,(
% 0.22/0.50    v1_funct_1(sK2)),
% 0.22/0.50    inference(cnf_transformation,[],[f16])).
% 0.22/0.50  fof(f72,plain,(
% 0.22/0.50    ( ! [X0] : (k1_funct_1(X0,sK4(sK0,X0,sK2)) != k1_funct_1(sK2,sK4(sK0,X0,sK2)) | r2_relset_1(sK0,sK1,X0,sK2) | ~v1_funct_1(sK2) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(X0,sK0,sK1) | ~v1_funct_1(X0)) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f70,f20])).
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    v1_funct_2(sK2,sK0,sK1)),
% 0.22/0.50    inference(cnf_transformation,[],[f16])).
% 0.22/0.50  fof(f70,plain,(
% 0.22/0.50    ( ! [X0] : (k1_funct_1(X0,sK4(sK0,X0,sK2)) != k1_funct_1(sK2,sK4(sK0,X0,sK2)) | r2_relset_1(sK0,sK1,X0,sK2) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(X0,sK0,sK1) | ~v1_funct_1(X0)) )),
% 0.22/0.50    inference(resolution,[],[f29,f21])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.50    inference(cnf_transformation,[],[f16])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_funct_1(X2,sK4(X0,X2,X3)) != k1_funct_1(X3,sK4(X0,X2,X3)) | r2_relset_1(X0,X1,X2,X3) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f18])).
% 0.22/0.50  fof(f18,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (! [X3] : (r2_relset_1(X0,X1,X2,X3) | (k1_funct_1(X2,sK4(X0,X2,X3)) != k1_funct_1(X3,sK4(X0,X2,X3)) & m1_subset_1(sK4(X0,X2,X3),X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f9,f17])).
% 0.22/0.50  fof(f17,plain,(
% 0.22/0.50    ! [X3,X2,X0] : (? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & m1_subset_1(X4,X0)) => (k1_funct_1(X2,sK4(X0,X2,X3)) != k1_funct_1(X3,sK4(X0,X2,X3)) & m1_subset_1(sK4(X0,X2,X3),X0)))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f9,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (! [X3] : (r2_relset_1(X0,X1,X2,X3) | ? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & m1_subset_1(X4,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.22/0.50    inference(flattening,[],[f8])).
% 0.22/0.50  fof(f8,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (! [X3] : ((r2_relset_1(X0,X1,X2,X3) | ? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & m1_subset_1(X4,X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.22/0.50    inference(ennf_transformation,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_funct_2)).
% 0.22/0.50  fof(f141,plain,(
% 0.22/0.50    ~spl5_1 | ~spl5_2 | spl5_5),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f140])).
% 0.22/0.50  fof(f140,plain,(
% 0.22/0.50    $false | (~spl5_1 | ~spl5_2 | spl5_5)),
% 0.22/0.50    inference(subsumption_resolution,[],[f139,f19])).
% 0.22/0.50  fof(f139,plain,(
% 0.22/0.50    ~v1_funct_1(sK2) | (~spl5_1 | ~spl5_2 | spl5_5)),
% 0.22/0.50    inference(subsumption_resolution,[],[f138,f107])).
% 0.22/0.50  fof(f107,plain,(
% 0.22/0.50    v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | (~spl5_1 | ~spl5_2)),
% 0.22/0.50    inference(forward_demodulation,[],[f102,f43])).
% 0.22/0.50  fof(f43,plain,(
% 0.22/0.50    k1_xboole_0 = sK0 | ~spl5_2),
% 0.22/0.50    inference(avatar_component_clause,[],[f41])).
% 0.22/0.50  fof(f41,plain,(
% 0.22/0.50    spl5_2 <=> k1_xboole_0 = sK0),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.22/0.50  fof(f102,plain,(
% 0.22/0.50    v1_funct_2(sK2,sK0,k1_xboole_0) | ~spl5_1),
% 0.22/0.50    inference(superposition,[],[f20,f38])).
% 0.22/0.50  fof(f38,plain,(
% 0.22/0.50    k1_xboole_0 = sK1 | ~spl5_1),
% 0.22/0.50    inference(avatar_component_clause,[],[f37])).
% 0.22/0.50  fof(f37,plain,(
% 0.22/0.50    spl5_1 <=> k1_xboole_0 = sK1),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.22/0.50  fof(f138,plain,(
% 0.22/0.50    ~v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | ~v1_funct_1(sK2) | (~spl5_1 | ~spl5_2 | spl5_5)),
% 0.22/0.50    inference(subsumption_resolution,[],[f134,f97])).
% 0.22/0.50  fof(f97,plain,(
% 0.22/0.50    ~v1_partfun1(sK2,k1_xboole_0) | (~spl5_2 | spl5_5)),
% 0.22/0.50    inference(forward_demodulation,[],[f84,f43])).
% 0.22/0.50  fof(f84,plain,(
% 0.22/0.50    ~v1_partfun1(sK2,sK0) | spl5_5),
% 0.22/0.50    inference(avatar_component_clause,[],[f82])).
% 0.22/0.50  fof(f82,plain,(
% 0.22/0.50    spl5_5 <=> v1_partfun1(sK2,sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.22/0.50  fof(f134,plain,(
% 0.22/0.50    v1_partfun1(sK2,k1_xboole_0) | ~v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | ~v1_funct_1(sK2) | (~spl5_1 | ~spl5_2)),
% 0.22/0.50    inference(resolution,[],[f104,f35])).
% 0.22/0.50  fof(f35,plain,(
% 0.22/0.50    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | v1_partfun1(X2,k1_xboole_0) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~v1_funct_1(X2)) )),
% 0.22/0.50    inference(duplicate_literal_removal,[],[f33])).
% 0.22/0.50  fof(f33,plain,(
% 0.22/0.50    ( ! [X2,X1] : (v1_partfun1(X2,k1_xboole_0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_1(X2)) )),
% 0.22/0.50    inference(equality_resolution,[],[f31])).
% 0.22/0.50  fof(f31,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f11])).
% 0.22/0.50  fof(f11,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.22/0.50    inference(flattening,[],[f10])).
% 0.22/0.50  fof(f10,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (((v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.22/0.50    inference(ennf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_funct_2)).
% 0.22/0.50  fof(f104,plain,(
% 0.22/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl5_1 | ~spl5_2)),
% 0.22/0.50    inference(forward_demodulation,[],[f99,f43])).
% 0.22/0.50  fof(f99,plain,(
% 0.22/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | ~spl5_1),
% 0.22/0.50    inference(superposition,[],[f21,f38])).
% 0.22/0.50  fof(f126,plain,(
% 0.22/0.50    ~spl5_1 | ~spl5_2 | spl5_6),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f125])).
% 0.22/0.50  fof(f125,plain,(
% 0.22/0.50    $false | (~spl5_1 | ~spl5_2 | spl5_6)),
% 0.22/0.50    inference(subsumption_resolution,[],[f124,f22])).
% 0.22/0.50  fof(f124,plain,(
% 0.22/0.50    ~v1_funct_1(sK3) | (~spl5_1 | ~spl5_2 | spl5_6)),
% 0.22/0.50    inference(subsumption_resolution,[],[f123,f106])).
% 0.22/0.50  fof(f106,plain,(
% 0.22/0.50    v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | (~spl5_1 | ~spl5_2)),
% 0.22/0.50    inference(forward_demodulation,[],[f101,f43])).
% 0.22/0.50  fof(f101,plain,(
% 0.22/0.50    v1_funct_2(sK3,sK0,k1_xboole_0) | ~spl5_1),
% 0.22/0.50    inference(superposition,[],[f23,f38])).
% 0.22/0.50  fof(f123,plain,(
% 0.22/0.50    ~v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | ~v1_funct_1(sK3) | (~spl5_1 | ~spl5_2 | spl5_6)),
% 0.22/0.50    inference(subsumption_resolution,[],[f119,f96])).
% 0.22/0.50  fof(f96,plain,(
% 0.22/0.50    ~v1_partfun1(sK3,k1_xboole_0) | (~spl5_2 | spl5_6)),
% 0.22/0.50    inference(forward_demodulation,[],[f88,f43])).
% 0.22/0.50  fof(f88,plain,(
% 0.22/0.50    ~v1_partfun1(sK3,sK0) | spl5_6),
% 0.22/0.50    inference(avatar_component_clause,[],[f86])).
% 0.22/0.50  fof(f86,plain,(
% 0.22/0.50    spl5_6 <=> v1_partfun1(sK3,sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.22/0.50  fof(f119,plain,(
% 0.22/0.50    v1_partfun1(sK3,k1_xboole_0) | ~v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | ~v1_funct_1(sK3) | (~spl5_1 | ~spl5_2)),
% 0.22/0.50    inference(resolution,[],[f103,f35])).
% 0.22/0.50  fof(f103,plain,(
% 0.22/0.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl5_1 | ~spl5_2)),
% 0.22/0.50    inference(forward_demodulation,[],[f98,f43])).
% 0.22/0.50  fof(f98,plain,(
% 0.22/0.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | ~spl5_1),
% 0.22/0.50    inference(superposition,[],[f24,f38])).
% 0.22/0.50  fof(f89,plain,(
% 0.22/0.50    ~spl5_5 | ~spl5_6 | ~spl5_3),
% 0.22/0.50    inference(avatar_split_clause,[],[f77,f57,f86,f82])).
% 0.22/0.50  fof(f57,plain,(
% 0.22/0.50    spl5_3 <=> ! [X1,X0] : (~v1_partfun1(sK3,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_partfun1(sK2,X0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.22/0.50  fof(f77,plain,(
% 0.22/0.50    ~v1_partfun1(sK3,sK0) | ~v1_partfun1(sK2,sK0) | ~spl5_3),
% 0.22/0.50    inference(subsumption_resolution,[],[f76,f21])).
% 0.22/0.50  fof(f76,plain,(
% 0.22/0.50    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_partfun1(sK3,sK0) | ~v1_partfun1(sK2,sK0) | ~spl5_3),
% 0.22/0.50    inference(resolution,[],[f58,f24])).
% 0.22/0.50  fof(f58,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_partfun1(sK3,X0) | ~v1_partfun1(sK2,X0)) ) | ~spl5_3),
% 0.22/0.50    inference(avatar_component_clause,[],[f57])).
% 0.22/0.50  fof(f80,plain,(
% 0.22/0.50    spl5_1 | ~spl5_3),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f79])).
% 0.22/0.50  fof(f79,plain,(
% 0.22/0.50    $false | (spl5_1 | ~spl5_3)),
% 0.22/0.50    inference(subsumption_resolution,[],[f78,f49])).
% 0.22/0.50  fof(f49,plain,(
% 0.22/0.50    v1_partfun1(sK2,sK0) | spl5_1),
% 0.22/0.50    inference(subsumption_resolution,[],[f48,f19])).
% 0.22/0.50  fof(f48,plain,(
% 0.22/0.50    v1_partfun1(sK2,sK0) | ~v1_funct_1(sK2) | spl5_1),
% 0.22/0.50    inference(subsumption_resolution,[],[f47,f20])).
% 0.22/0.50  fof(f47,plain,(
% 0.22/0.50    v1_partfun1(sK2,sK0) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | spl5_1),
% 0.22/0.50    inference(subsumption_resolution,[],[f45,f39])).
% 0.22/0.50  fof(f39,plain,(
% 0.22/0.50    k1_xboole_0 != sK1 | spl5_1),
% 0.22/0.50    inference(avatar_component_clause,[],[f37])).
% 0.22/0.50  fof(f45,plain,(
% 0.22/0.50    k1_xboole_0 = sK1 | v1_partfun1(sK2,sK0) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 0.22/0.50    inference(resolution,[],[f34,f21])).
% 0.22/0.50  fof(f34,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.22/0.50    inference(duplicate_literal_removal,[],[f30])).
% 0.22/0.50  fof(f30,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f11])).
% 0.22/0.50  fof(f78,plain,(
% 0.22/0.50    ~v1_partfun1(sK2,sK0) | (spl5_1 | ~spl5_3)),
% 0.22/0.50    inference(subsumption_resolution,[],[f77,f52])).
% 0.22/0.50  fof(f52,plain,(
% 0.22/0.50    v1_partfun1(sK3,sK0) | spl5_1),
% 0.22/0.50    inference(subsumption_resolution,[],[f51,f22])).
% 0.22/0.50  fof(f51,plain,(
% 0.22/0.50    v1_partfun1(sK3,sK0) | ~v1_funct_1(sK3) | spl5_1),
% 0.22/0.50    inference(subsumption_resolution,[],[f50,f23])).
% 0.22/0.50  fof(f50,plain,(
% 0.22/0.50    v1_partfun1(sK3,sK0) | ~v1_funct_2(sK3,sK0,sK1) | ~v1_funct_1(sK3) | spl5_1),
% 0.22/0.50    inference(subsumption_resolution,[],[f46,f39])).
% 0.22/0.50  fof(f46,plain,(
% 0.22/0.50    k1_xboole_0 = sK1 | v1_partfun1(sK3,sK0) | ~v1_funct_2(sK3,sK0,sK1) | ~v1_funct_1(sK3)),
% 0.22/0.50    inference(resolution,[],[f34,f24])).
% 0.22/0.50  fof(f63,plain,(
% 0.22/0.50    spl5_3 | spl5_4),
% 0.22/0.50    inference(avatar_split_clause,[],[f55,f60,f57])).
% 0.22/0.50  fof(f55,plain,(
% 0.22/0.50    ( ! [X0,X1] : (sK2 = sK3 | ~v1_partfun1(sK3,X0) | ~v1_partfun1(sK2,X0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f54,f19])).
% 0.22/0.50  fof(f54,plain,(
% 0.22/0.50    ( ! [X0,X1] : (sK2 = sK3 | ~v1_partfun1(sK3,X0) | ~v1_partfun1(sK2,X0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(sK2)) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f53,f22])).
% 0.22/0.50  fof(f53,plain,(
% 0.22/0.50    ( ! [X0,X1] : (sK2 = sK3 | ~v1_partfun1(sK3,X0) | ~v1_partfun1(sK2,X0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(sK2)) )),
% 0.22/0.50    inference(resolution,[],[f32,f25])).
% 0.22/0.50  fof(f25,plain,(
% 0.22/0.50    r1_partfun1(sK2,sK3)),
% 0.22/0.50    inference(cnf_transformation,[],[f16])).
% 0.22/0.50  fof(f32,plain,(
% 0.22/0.50    ( ! [X2,X0,X3,X1] : (~r1_partfun1(X2,X3) | X2 = X3 | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f13])).
% 0.22/0.50  fof(f13,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (! [X3] : (X2 = X3 | ~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.22/0.50    inference(flattening,[],[f12])).
% 0.22/0.50  fof(f12,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (! [X3] : ((X2 = X3 | (~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.22/0.50    inference(ennf_transformation,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ((r1_partfun1(X2,X3) & v1_partfun1(X3,X0) & v1_partfun1(X2,X0)) => X2 = X3)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_partfun1)).
% 0.22/0.50  fof(f44,plain,(
% 0.22/0.50    ~spl5_1 | spl5_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f26,f41,f37])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 0.22/0.50    inference(cnf_transformation,[],[f16])).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (10317)------------------------------
% 0.22/0.50  % (10317)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (10317)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (10317)Memory used [KB]: 10746
% 0.22/0.50  % (10317)Time elapsed: 0.067 s
% 0.22/0.50  % (10317)------------------------------
% 0.22/0.50  % (10317)------------------------------
% 0.22/0.51  % (10306)Success in time 0.141 s
%------------------------------------------------------------------------------
