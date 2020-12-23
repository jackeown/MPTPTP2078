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
% DateTime   : Thu Dec  3 13:05:42 EST 2020

% Result     : Theorem 2.02s
% Output     : Refutation 2.02s
% Verified   : 
% Statistics : Number of formulae       :  164 ( 772 expanded)
%              Number of leaves         :   25 ( 242 expanded)
%              Depth                    :   24
%              Number of atoms          :  631 (6272 expanded)
%              Number of equality atoms :   96 ( 289 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f562,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f105,f110,f150,f243,f377,f393,f455,f558])).

fof(f558,plain,
    ( ~ spl3_2
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_6
    | spl3_7 ),
    inference(avatar_contradiction_clause,[],[f557])).

fof(f557,plain,
    ( $false
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_6
    | spl3_7 ),
    inference(subsumption_resolution,[],[f556,f533])).

fof(f533,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl3_2
    | ~ spl3_5
    | ~ spl3_6
    | spl3_7 ),
    inference(forward_demodulation,[],[f505,f402])).

fof(f402,plain,
    ( k1_xboole_0 = sK0
    | ~ spl3_5
    | ~ spl3_6
    | spl3_7 ),
    inference(global_subsumption,[],[f212,f219,f215])).

fof(f215,plain,
    ( sK0 = k2_relset_1(sK0,sK0,sK1)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f214])).

fof(f214,plain,
    ( spl3_6
  <=> sK0 = k2_relset_1(sK0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f219,plain,
    ( sK2 != k2_funct_1(sK1)
    | spl3_7 ),
    inference(avatar_component_clause,[],[f218])).

fof(f218,plain,
    ( spl3_7
  <=> sK2 = k2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f212,plain,
    ( k1_xboole_0 = sK0
    | sK2 = k2_funct_1(sK1)
    | sK0 != k2_relset_1(sK0,sK0,sK1) ),
    inference(subsumption_resolution,[],[f211,f48])).

fof(f48,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f44,f43])).

fof(f43,plain,
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

fof(f44,plain,
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

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
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
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_funct_2)).

fof(f211,plain,
    ( k1_xboole_0 = sK0
    | sK2 = k2_funct_1(sK1)
    | sK0 != k2_relset_1(sK0,sK0,sK1)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f210,f49])).

fof(f49,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f210,plain,
    ( k1_xboole_0 = sK0
    | sK2 = k2_funct_1(sK1)
    | sK0 != k2_relset_1(sK0,sK0,sK1)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f209,f51])).

fof(f51,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f45])).

fof(f209,plain,
    ( k1_xboole_0 = sK0
    | sK2 = k2_funct_1(sK1)
    | sK0 != k2_relset_1(sK0,sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f208,f52])).

fof(f52,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f208,plain,
    ( k1_xboole_0 = sK0
    | sK2 = k2_funct_1(sK1)
    | sK0 != k2_relset_1(sK0,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f207,f53])).

fof(f53,plain,(
    v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f207,plain,
    ( k1_xboole_0 = sK0
    | sK2 = k2_funct_1(sK1)
    | sK0 != k2_relset_1(sK0,sK0,sK1)
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f206,f55])).

fof(f55,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f45])).

fof(f206,plain,
    ( k1_xboole_0 = sK0
    | sK2 = k2_funct_1(sK1)
    | sK0 != k2_relset_1(sK0,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(duplicate_literal_removal,[],[f205])).

fof(f205,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK0
    | sK2 = k2_funct_1(sK1)
    | sK0 != k2_relset_1(sK0,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(resolution,[],[f85,f56])).

fof(f56,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f45])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k2_funct_1(X2) = X3
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(subsumption_resolution,[],[f77,f75])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
      | v2_funct_1(X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_funct_2)).

fof(f77,plain,(
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
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f37,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
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

fof(f505,plain,
    ( r2_relset_1(sK0,sK0,k1_xboole_0,k1_xboole_0)
    | ~ spl3_2 ),
    inference(superposition,[],[f111,f468])).

fof(f468,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_2 ),
    inference(resolution,[],[f104,f86])).

fof(f86,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f68,f58])).

fof(f58,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

fof(f104,plain,
    ( v1_xboole_0(sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl3_2
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f111,plain,(
    r2_relset_1(sK0,sK0,sK1,sK1) ),
    inference(resolution,[],[f84,f51])).

fof(f84,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f83])).

fof(f83,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f40])).

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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f556,plain,
    ( ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_6
    | spl3_7 ),
    inference(forward_demodulation,[],[f555,f402])).

fof(f555,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_xboole_0,k1_xboole_0)
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_6
    | spl3_7 ),
    inference(forward_demodulation,[],[f554,f472])).

fof(f472,plain,
    ( k1_xboole_0 = sK2
    | ~ spl3_3 ),
    inference(resolution,[],[f109,f86])).

fof(f109,plain,
    ( v1_xboole_0(sK2)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl3_3
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f554,plain,
    ( ~ r2_relset_1(sK0,sK0,sK2,k1_xboole_0)
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_6
    | spl3_7 ),
    inference(forward_demodulation,[],[f519,f479])).

fof(f479,plain,
    ( k1_xboole_0 = k2_funct_1(k1_xboole_0)
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_6
    | spl3_7 ),
    inference(forward_demodulation,[],[f476,f472])).

fof(f476,plain,
    ( k1_xboole_0 = k2_funct_1(sK2)
    | ~ spl3_5
    | ~ spl3_6
    | spl3_7 ),
    inference(resolution,[],[f461,f86])).

fof(f461,plain,
    ( v1_xboole_0(k2_funct_1(sK2))
    | ~ spl3_5
    | ~ spl3_6
    | spl3_7 ),
    inference(subsumption_resolution,[],[f460,f58])).

fof(f460,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0(k2_funct_1(sK2))
    | ~ spl3_5
    | ~ spl3_6
    | spl3_7 ),
    inference(forward_demodulation,[],[f301,f402])).

fof(f301,plain,
    ( v1_xboole_0(k2_funct_1(sK2))
    | ~ v1_xboole_0(sK0) ),
    inference(resolution,[],[f192,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | v1_xboole_0(X2)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

fof(f192,plain,(
    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(forward_demodulation,[],[f191,f159])).

fof(f159,plain,(
    k2_funct_2(sK0,sK2) = k2_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f158,f52])).

fof(f158,plain,
    ( k2_funct_2(sK0,sK2) = k2_funct_1(sK2)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f157,f53])).

fof(f157,plain,
    ( k2_funct_2(sK0,sK2) = k2_funct_1(sK2)
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f152,f54])).

fof(f54,plain,(
    v3_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f152,plain,
    ( k2_funct_2(sK0,sK2) = k2_funct_1(sK2)
    | ~ v3_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f63,f55])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_2(X0,X1) = k2_funct_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

fof(f191,plain,(
    m1_subset_1(k2_funct_2(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f190,f52])).

fof(f190,plain,
    ( m1_subset_1(k2_funct_2(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f189,f53])).

fof(f189,plain,
    ( m1_subset_1(k2_funct_2(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f183,f54])).

fof(f183,plain,
    ( m1_subset_1(k2_funct_2(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v3_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f67,f55])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_2)).

fof(f519,plain,
    ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_1(k1_xboole_0))
    | ~ spl3_2 ),
    inference(superposition,[],[f239,f468])).

fof(f239,plain,(
    ~ r2_relset_1(sK0,sK0,sK2,k2_funct_1(sK1)) ),
    inference(superposition,[],[f57,f156])).

fof(f156,plain,(
    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f155,f48])).

fof(f155,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f154,f49])).

fof(f154,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f151,f50])).

fof(f50,plain,(
    v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f151,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(resolution,[],[f63,f51])).

fof(f57,plain,(
    ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f45])).

fof(f455,plain,
    ( spl3_1
    | ~ spl3_5
    | ~ spl3_6
    | spl3_7 ),
    inference(avatar_contradiction_clause,[],[f454])).

fof(f454,plain,
    ( $false
    | spl3_1
    | ~ spl3_5
    | ~ spl3_6
    | spl3_7 ),
    inference(subsumption_resolution,[],[f432,f58])).

fof(f432,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl3_1
    | ~ spl3_5
    | ~ spl3_6
    | spl3_7 ),
    inference(superposition,[],[f100,f402])).

fof(f100,plain,
    ( ~ v1_xboole_0(sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl3_1
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f393,plain,(
    ~ spl3_7 ),
    inference(avatar_contradiction_clause,[],[f392])).

fof(f392,plain,
    ( $false
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f391,f112])).

fof(f112,plain,(
    r2_relset_1(sK0,sK0,sK2,sK2) ),
    inference(resolution,[],[f84,f55])).

fof(f391,plain,
    ( ~ r2_relset_1(sK0,sK0,sK2,sK2)
    | ~ spl3_7 ),
    inference(superposition,[],[f239,f220])).

fof(f220,plain,
    ( sK2 = k2_funct_1(sK1)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f218])).

fof(f377,plain,(
    spl3_4 ),
    inference(avatar_contradiction_clause,[],[f376])).

fof(f376,plain,
    ( $false
    | spl3_4 ),
    inference(subsumption_resolution,[],[f375,f48])).

fof(f375,plain,
    ( ~ v1_funct_1(sK1)
    | spl3_4 ),
    inference(subsumption_resolution,[],[f370,f145])).

fof(f145,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl3_4 ),
    inference(avatar_component_clause,[],[f143])).

fof(f143,plain,
    ( spl3_4
  <=> m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f370,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1) ),
    inference(resolution,[],[f202,f51])).

fof(f202,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | m1_subset_1(k1_partfun1(X3,X4,sK0,sK0,X5,sK2),k1_zfmisc_1(k2_zfmisc_1(X3,sK0)))
      | ~ v1_funct_1(X5) ) ),
    inference(subsumption_resolution,[],[f199,f52])).

fof(f199,plain,(
    ! [X4,X5,X3] :
      ( m1_subset_1(k1_partfun1(X3,X4,sK0,sK0,X5,sK2),k1_zfmisc_1(k2_zfmisc_1(X3,sK0)))
      | ~ v1_funct_1(sK2)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_1(X5) ) ),
    inference(resolution,[],[f81,f55])).

fof(f81,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f243,plain,(
    spl3_6 ),
    inference(avatar_contradiction_clause,[],[f242])).

fof(f242,plain,
    ( $false
    | spl3_6 ),
    inference(subsumption_resolution,[],[f241,f228])).

fof(f228,plain,(
    sK0 = k2_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f227,f88])).

fof(f88,plain,(
    v1_relat_1(sK1) ),
    inference(resolution,[],[f69,f51])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f227,plain,
    ( sK0 = k2_relat_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f226,f91])).

fof(f91,plain,(
    v5_relat_1(sK1,sK0) ),
    inference(resolution,[],[f71,f51])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f226,plain,
    ( sK0 = k2_relat_1(sK1)
    | ~ v5_relat_1(sK1,sK0)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f128,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_2(X1,X0)
      | k2_relat_1(X1) = X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

fof(f128,plain,(
    v2_funct_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f127,f48])).

fof(f127,plain,
    ( ~ v1_funct_1(sK1)
    | v2_funct_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f124,f50])).

fof(f124,plain,
    ( ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | v2_funct_2(sK1,sK0) ),
    inference(resolution,[],[f74,f51])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v2_funct_2(X2,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

fof(f241,plain,
    ( sK0 != k2_relat_1(sK1)
    | spl3_6 ),
    inference(superposition,[],[f216,f114])).

fof(f114,plain,(
    k2_relset_1(sK0,sK0,sK1) = k2_relat_1(sK1) ),
    inference(resolution,[],[f70,f51])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f216,plain,
    ( sK0 != k2_relset_1(sK0,sK0,sK1)
    | spl3_6 ),
    inference(avatar_component_clause,[],[f214])).

fof(f150,plain,
    ( ~ spl3_4
    | spl3_5 ),
    inference(avatar_split_clause,[],[f141,f147,f143])).

fof(f147,plain,
    ( spl3_5
  <=> k6_partfun1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f141,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2)
    | ~ m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f140,f59])).

fof(f59,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f140,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2)
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f78,f56])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f110,plain,
    ( ~ spl3_1
    | spl3_3 ),
    inference(avatar_split_clause,[],[f95,f107,f98])).

fof(f95,plain,
    ( v1_xboole_0(sK2)
    | ~ v1_xboole_0(sK0) ),
    inference(resolution,[],[f60,f55])).

fof(f105,plain,
    ( ~ spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f94,f102,f98])).

fof(f94,plain,
    ( v1_xboole_0(sK1)
    | ~ v1_xboole_0(sK0) ),
    inference(resolution,[],[f60,f51])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n010.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 15:10:14 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.53  % (20918)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.53  % (20934)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.54  % (20926)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.54  % (20917)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.54  % (20916)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.55  % (20914)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.55  % (20935)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.56  % (20931)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.56  % (20913)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.56  % (20932)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.56  % (20925)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.56  % (20915)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.57  % (20919)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.57  % (20924)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.58  % (20923)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.58  % (20937)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.58  % (20927)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.59  % (20922)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.59  % (20933)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.59  % (20912)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.61  % (20930)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.61  % (20929)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.61  % (20928)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.62  % (20921)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.62  % (20936)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.63  % (20920)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 2.02/0.65  % (20922)Refutation found. Thanks to Tanya!
% 2.02/0.65  % SZS status Theorem for theBenchmark
% 2.02/0.65  % SZS output start Proof for theBenchmark
% 2.02/0.65  fof(f562,plain,(
% 2.02/0.65    $false),
% 2.02/0.65    inference(avatar_sat_refutation,[],[f105,f110,f150,f243,f377,f393,f455,f558])).
% 2.02/0.65  fof(f558,plain,(
% 2.02/0.65    ~spl3_2 | ~spl3_3 | ~spl3_5 | ~spl3_6 | spl3_7),
% 2.02/0.65    inference(avatar_contradiction_clause,[],[f557])).
% 2.02/0.65  fof(f557,plain,(
% 2.02/0.65    $false | (~spl3_2 | ~spl3_3 | ~spl3_5 | ~spl3_6 | spl3_7)),
% 2.02/0.65    inference(subsumption_resolution,[],[f556,f533])).
% 2.02/0.65  fof(f533,plain,(
% 2.02/0.65    r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl3_2 | ~spl3_5 | ~spl3_6 | spl3_7)),
% 2.02/0.65    inference(forward_demodulation,[],[f505,f402])).
% 2.02/0.65  fof(f402,plain,(
% 2.02/0.65    k1_xboole_0 = sK0 | (~spl3_5 | ~spl3_6 | spl3_7)),
% 2.02/0.65    inference(global_subsumption,[],[f212,f219,f215])).
% 2.02/0.65  fof(f215,plain,(
% 2.02/0.65    sK0 = k2_relset_1(sK0,sK0,sK1) | ~spl3_6),
% 2.02/0.65    inference(avatar_component_clause,[],[f214])).
% 2.02/0.65  fof(f214,plain,(
% 2.02/0.65    spl3_6 <=> sK0 = k2_relset_1(sK0,sK0,sK1)),
% 2.02/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 2.02/0.65  fof(f219,plain,(
% 2.02/0.65    sK2 != k2_funct_1(sK1) | spl3_7),
% 2.02/0.65    inference(avatar_component_clause,[],[f218])).
% 2.02/0.65  fof(f218,plain,(
% 2.02/0.65    spl3_7 <=> sK2 = k2_funct_1(sK1)),
% 2.02/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 2.02/0.65  fof(f212,plain,(
% 2.02/0.65    k1_xboole_0 = sK0 | sK2 = k2_funct_1(sK1) | sK0 != k2_relset_1(sK0,sK0,sK1)),
% 2.02/0.65    inference(subsumption_resolution,[],[f211,f48])).
% 2.02/0.65  fof(f48,plain,(
% 2.02/0.65    v1_funct_1(sK1)),
% 2.02/0.65    inference(cnf_transformation,[],[f45])).
% 2.02/0.65  fof(f45,plain,(
% 2.02/0.65    (~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK2,sK0,sK0) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 2.02/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f44,f43])).
% 2.02/0.65  fof(f43,plain,(
% 2.02/0.65    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (? [X2] : (~r2_relset_1(sK0,sK0,X2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(X2,sK0,sK0) & v1_funct_2(X2,sK0,sK0) & v1_funct_1(X2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 2.02/0.65    introduced(choice_axiom,[])).
% 2.02/0.65  fof(f44,plain,(
% 2.02/0.65    ? [X2] : (~r2_relset_1(sK0,sK0,X2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(X2,sK0,sK0) & v1_funct_2(X2,sK0,sK0) & v1_funct_1(X2)) => (~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK2,sK0,sK0) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2))),
% 2.02/0.65    introduced(choice_axiom,[])).
% 2.02/0.65  fof(f21,plain,(
% 2.02/0.65    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 2.02/0.65    inference(flattening,[],[f20])).
% 2.02/0.65  fof(f20,plain,(
% 2.02/0.65    ? [X0,X1] : (? [X2] : ((~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 2.02/0.65    inference(ennf_transformation,[],[f17])).
% 2.02/0.65  fof(f17,negated_conjecture,(
% 2.02/0.65    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 2.02/0.65    inference(negated_conjecture,[],[f16])).
% 2.02/0.65  fof(f16,conjecture,(
% 2.02/0.65    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 2.02/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_funct_2)).
% 2.02/0.65  fof(f211,plain,(
% 2.02/0.65    k1_xboole_0 = sK0 | sK2 = k2_funct_1(sK1) | sK0 != k2_relset_1(sK0,sK0,sK1) | ~v1_funct_1(sK1)),
% 2.02/0.65    inference(subsumption_resolution,[],[f210,f49])).
% 2.02/0.65  fof(f49,plain,(
% 2.02/0.65    v1_funct_2(sK1,sK0,sK0)),
% 2.02/0.65    inference(cnf_transformation,[],[f45])).
% 2.02/0.65  fof(f210,plain,(
% 2.02/0.65    k1_xboole_0 = sK0 | sK2 = k2_funct_1(sK1) | sK0 != k2_relset_1(sK0,sK0,sK1) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 2.02/0.65    inference(subsumption_resolution,[],[f209,f51])).
% 2.02/0.65  fof(f51,plain,(
% 2.02/0.65    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.02/0.65    inference(cnf_transformation,[],[f45])).
% 2.02/0.65  fof(f209,plain,(
% 2.02/0.65    k1_xboole_0 = sK0 | sK2 = k2_funct_1(sK1) | sK0 != k2_relset_1(sK0,sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 2.02/0.65    inference(subsumption_resolution,[],[f208,f52])).
% 2.02/0.65  fof(f52,plain,(
% 2.02/0.65    v1_funct_1(sK2)),
% 2.02/0.65    inference(cnf_transformation,[],[f45])).
% 2.02/0.65  fof(f208,plain,(
% 2.02/0.65    k1_xboole_0 = sK0 | sK2 = k2_funct_1(sK1) | sK0 != k2_relset_1(sK0,sK0,sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 2.02/0.65    inference(subsumption_resolution,[],[f207,f53])).
% 2.02/0.65  fof(f53,plain,(
% 2.02/0.65    v1_funct_2(sK2,sK0,sK0)),
% 2.02/0.65    inference(cnf_transformation,[],[f45])).
% 2.02/0.65  fof(f207,plain,(
% 2.02/0.65    k1_xboole_0 = sK0 | sK2 = k2_funct_1(sK1) | sK0 != k2_relset_1(sK0,sK0,sK1) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 2.02/0.65    inference(subsumption_resolution,[],[f206,f55])).
% 2.02/0.65  fof(f55,plain,(
% 2.02/0.65    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.02/0.65    inference(cnf_transformation,[],[f45])).
% 2.02/0.65  fof(f206,plain,(
% 2.02/0.65    k1_xboole_0 = sK0 | sK2 = k2_funct_1(sK1) | sK0 != k2_relset_1(sK0,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 2.02/0.65    inference(duplicate_literal_removal,[],[f205])).
% 2.02/0.65  fof(f205,plain,(
% 2.02/0.65    k1_xboole_0 = sK0 | k1_xboole_0 = sK0 | sK2 = k2_funct_1(sK1) | sK0 != k2_relset_1(sK0,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 2.02/0.65    inference(resolution,[],[f85,f56])).
% 2.02/0.65  fof(f56,plain,(
% 2.02/0.65    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0))),
% 2.02/0.65    inference(cnf_transformation,[],[f45])).
% 2.02/0.65  fof(f85,plain,(
% 2.02/0.65    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_funct_1(X2) = X3 | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.02/0.65    inference(subsumption_resolution,[],[f77,f75])).
% 2.02/0.65  fof(f75,plain,(
% 2.02/0.65    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | v2_funct_1(X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.02/0.65    inference(cnf_transformation,[],[f36])).
% 2.02/0.65  fof(f36,plain,(
% 2.02/0.65    ! [X0,X1,X2] : (! [X3] : ((v2_funct_2(X3,X0) & v2_funct_1(X2)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.02/0.65    inference(flattening,[],[f35])).
% 2.02/0.65  fof(f35,plain,(
% 2.02/0.65    ! [X0,X1,X2] : (! [X3] : (((v2_funct_2(X3,X0) & v2_funct_1(X2)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.02/0.65    inference(ennf_transformation,[],[f14])).
% 2.02/0.65  fof(f14,axiom,(
% 2.02/0.65    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 2.02/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_funct_2)).
% 2.02/0.65  fof(f77,plain,(
% 2.02/0.65    ( ! [X2,X0,X3,X1] : (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.02/0.65    inference(cnf_transformation,[],[f38])).
% 2.02/0.65  fof(f38,plain,(
% 2.02/0.65    ! [X0,X1,X2] : (! [X3] : (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.02/0.65    inference(flattening,[],[f37])).
% 2.02/0.65  fof(f37,plain,(
% 2.02/0.65    ! [X0,X1,X2] : (! [X3] : (((k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0) | (~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.02/0.65    inference(ennf_transformation,[],[f15])).
% 2.02/0.65  fof(f15,axiom,(
% 2.02/0.65    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 2.02/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).
% 2.02/0.65  fof(f505,plain,(
% 2.02/0.65    r2_relset_1(sK0,sK0,k1_xboole_0,k1_xboole_0) | ~spl3_2),
% 2.02/0.65    inference(superposition,[],[f111,f468])).
% 2.02/0.65  fof(f468,plain,(
% 2.02/0.65    k1_xboole_0 = sK1 | ~spl3_2),
% 2.02/0.65    inference(resolution,[],[f104,f86])).
% 2.02/0.65  fof(f86,plain,(
% 2.02/0.65    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 2.02/0.65    inference(resolution,[],[f68,f58])).
% 2.02/0.65  fof(f58,plain,(
% 2.02/0.65    v1_xboole_0(k1_xboole_0)),
% 2.02/0.65    inference(cnf_transformation,[],[f1])).
% 2.02/0.65  fof(f1,axiom,(
% 2.02/0.65    v1_xboole_0(k1_xboole_0)),
% 2.02/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 2.02/0.65  fof(f68,plain,(
% 2.02/0.65    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 2.02/0.65    inference(cnf_transformation,[],[f29])).
% 2.02/0.65  fof(f29,plain,(
% 2.02/0.65    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 2.02/0.65    inference(ennf_transformation,[],[f2])).
% 2.02/0.65  fof(f2,axiom,(
% 2.02/0.65    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 2.02/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).
% 2.02/0.65  fof(f104,plain,(
% 2.02/0.65    v1_xboole_0(sK1) | ~spl3_2),
% 2.02/0.65    inference(avatar_component_clause,[],[f102])).
% 2.02/0.65  fof(f102,plain,(
% 2.02/0.65    spl3_2 <=> v1_xboole_0(sK1)),
% 2.02/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 2.02/0.65  fof(f111,plain,(
% 2.02/0.65    r2_relset_1(sK0,sK0,sK1,sK1)),
% 2.02/0.65    inference(resolution,[],[f84,f51])).
% 2.02/0.65  fof(f84,plain,(
% 2.02/0.65    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 2.02/0.65    inference(duplicate_literal_removal,[],[f83])).
% 2.02/0.65  fof(f83,plain,(
% 2.02/0.65    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.02/0.65    inference(equality_resolution,[],[f79])).
% 2.02/0.65  fof(f79,plain,(
% 2.02/0.65    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.02/0.65    inference(cnf_transformation,[],[f47])).
% 2.02/0.65  fof(f47,plain,(
% 2.02/0.65    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.02/0.65    inference(nnf_transformation,[],[f40])).
% 2.02/0.65  fof(f40,plain,(
% 2.02/0.65    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.02/0.65    inference(flattening,[],[f39])).
% 2.02/0.65  fof(f39,plain,(
% 2.02/0.65    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.02/0.65    inference(ennf_transformation,[],[f7])).
% 2.02/0.65  fof(f7,axiom,(
% 2.02/0.65    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 2.02/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 2.02/0.65  fof(f556,plain,(
% 2.02/0.65    ~r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl3_2 | ~spl3_3 | ~spl3_5 | ~spl3_6 | spl3_7)),
% 2.02/0.65    inference(forward_demodulation,[],[f555,f402])).
% 2.02/0.65  fof(f555,plain,(
% 2.02/0.65    ~r2_relset_1(sK0,sK0,k1_xboole_0,k1_xboole_0) | (~spl3_2 | ~spl3_3 | ~spl3_5 | ~spl3_6 | spl3_7)),
% 2.02/0.65    inference(forward_demodulation,[],[f554,f472])).
% 2.02/0.65  fof(f472,plain,(
% 2.02/0.65    k1_xboole_0 = sK2 | ~spl3_3),
% 2.02/0.65    inference(resolution,[],[f109,f86])).
% 2.02/0.65  fof(f109,plain,(
% 2.02/0.65    v1_xboole_0(sK2) | ~spl3_3),
% 2.02/0.65    inference(avatar_component_clause,[],[f107])).
% 2.02/0.65  fof(f107,plain,(
% 2.02/0.65    spl3_3 <=> v1_xboole_0(sK2)),
% 2.02/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 2.02/0.65  fof(f554,plain,(
% 2.02/0.65    ~r2_relset_1(sK0,sK0,sK2,k1_xboole_0) | (~spl3_2 | ~spl3_3 | ~spl3_5 | ~spl3_6 | spl3_7)),
% 2.02/0.65    inference(forward_demodulation,[],[f519,f479])).
% 2.02/0.65  fof(f479,plain,(
% 2.02/0.65    k1_xboole_0 = k2_funct_1(k1_xboole_0) | (~spl3_3 | ~spl3_5 | ~spl3_6 | spl3_7)),
% 2.02/0.65    inference(forward_demodulation,[],[f476,f472])).
% 2.02/0.65  fof(f476,plain,(
% 2.02/0.65    k1_xboole_0 = k2_funct_1(sK2) | (~spl3_5 | ~spl3_6 | spl3_7)),
% 2.02/0.65    inference(resolution,[],[f461,f86])).
% 2.02/0.65  fof(f461,plain,(
% 2.02/0.65    v1_xboole_0(k2_funct_1(sK2)) | (~spl3_5 | ~spl3_6 | spl3_7)),
% 2.02/0.65    inference(subsumption_resolution,[],[f460,f58])).
% 2.02/0.65  fof(f460,plain,(
% 2.02/0.65    ~v1_xboole_0(k1_xboole_0) | v1_xboole_0(k2_funct_1(sK2)) | (~spl3_5 | ~spl3_6 | spl3_7)),
% 2.02/0.65    inference(forward_demodulation,[],[f301,f402])).
% 2.02/0.65  fof(f301,plain,(
% 2.02/0.65    v1_xboole_0(k2_funct_1(sK2)) | ~v1_xboole_0(sK0)),
% 2.02/0.65    inference(resolution,[],[f192,f60])).
% 2.02/0.65  fof(f60,plain,(
% 2.02/0.65    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | v1_xboole_0(X2) | ~v1_xboole_0(X0)) )),
% 2.02/0.65    inference(cnf_transformation,[],[f22])).
% 2.02/0.65  fof(f22,plain,(
% 2.02/0.65    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 2.02/0.65    inference(ennf_transformation,[],[f5])).
% 2.02/0.65  fof(f5,axiom,(
% 2.02/0.65    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 2.02/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).
% 2.02/0.65  fof(f192,plain,(
% 2.02/0.65    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.02/0.65    inference(forward_demodulation,[],[f191,f159])).
% 2.02/0.65  fof(f159,plain,(
% 2.02/0.65    k2_funct_2(sK0,sK2) = k2_funct_1(sK2)),
% 2.02/0.65    inference(subsumption_resolution,[],[f158,f52])).
% 2.02/0.65  fof(f158,plain,(
% 2.02/0.65    k2_funct_2(sK0,sK2) = k2_funct_1(sK2) | ~v1_funct_1(sK2)),
% 2.02/0.65    inference(subsumption_resolution,[],[f157,f53])).
% 2.02/0.65  fof(f157,plain,(
% 2.02/0.65    k2_funct_2(sK0,sK2) = k2_funct_1(sK2) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2)),
% 2.02/0.65    inference(subsumption_resolution,[],[f152,f54])).
% 2.02/0.65  fof(f54,plain,(
% 2.02/0.65    v3_funct_2(sK2,sK0,sK0)),
% 2.02/0.65    inference(cnf_transformation,[],[f45])).
% 2.02/0.65  fof(f152,plain,(
% 2.02/0.65    k2_funct_2(sK0,sK2) = k2_funct_1(sK2) | ~v3_funct_2(sK2,sK0,sK0) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2)),
% 2.02/0.65    inference(resolution,[],[f63,f55])).
% 2.02/0.65  fof(f63,plain,(
% 2.02/0.65    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | k2_funct_2(X0,X1) = k2_funct_1(X1) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 2.02/0.65    inference(cnf_transformation,[],[f26])).
% 2.02/0.65  fof(f26,plain,(
% 2.02/0.65    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 2.02/0.65    inference(flattening,[],[f25])).
% 2.02/0.65  fof(f25,plain,(
% 2.02/0.65    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 2.02/0.65    inference(ennf_transformation,[],[f13])).
% 2.02/0.65  fof(f13,axiom,(
% 2.02/0.65    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_2(X0,X1) = k2_funct_1(X1))),
% 2.02/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).
% 2.02/0.65  fof(f191,plain,(
% 2.02/0.65    m1_subset_1(k2_funct_2(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.02/0.65    inference(subsumption_resolution,[],[f190,f52])).
% 2.02/0.65  fof(f190,plain,(
% 2.02/0.65    m1_subset_1(k2_funct_2(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK2)),
% 2.02/0.65    inference(subsumption_resolution,[],[f189,f53])).
% 2.02/0.65  fof(f189,plain,(
% 2.02/0.65    m1_subset_1(k2_funct_2(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2)),
% 2.02/0.65    inference(subsumption_resolution,[],[f183,f54])).
% 2.02/0.65  fof(f183,plain,(
% 2.02/0.65    m1_subset_1(k2_funct_2(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v3_funct_2(sK2,sK0,sK0) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2)),
% 2.02/0.65    inference(resolution,[],[f67,f55])).
% 2.02/0.65  fof(f67,plain,(
% 2.02/0.65    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 2.02/0.65    inference(cnf_transformation,[],[f28])).
% 2.02/0.65  fof(f28,plain,(
% 2.02/0.65    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 2.02/0.65    inference(flattening,[],[f27])).
% 2.02/0.65  fof(f27,plain,(
% 2.02/0.65    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 2.02/0.65    inference(ennf_transformation,[],[f11])).
% 2.02/0.65  fof(f11,axiom,(
% 2.02/0.65    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))))),
% 2.02/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_2)).
% 2.02/0.65  fof(f519,plain,(
% 2.02/0.65    ~r2_relset_1(sK0,sK0,sK2,k2_funct_1(k1_xboole_0)) | ~spl3_2),
% 2.02/0.65    inference(superposition,[],[f239,f468])).
% 2.02/0.65  fof(f239,plain,(
% 2.02/0.65    ~r2_relset_1(sK0,sK0,sK2,k2_funct_1(sK1))),
% 2.02/0.65    inference(superposition,[],[f57,f156])).
% 2.02/0.65  fof(f156,plain,(
% 2.02/0.65    k2_funct_2(sK0,sK1) = k2_funct_1(sK1)),
% 2.02/0.65    inference(subsumption_resolution,[],[f155,f48])).
% 2.02/0.65  fof(f155,plain,(
% 2.02/0.65    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | ~v1_funct_1(sK1)),
% 2.02/0.65    inference(subsumption_resolution,[],[f154,f49])).
% 2.02/0.65  fof(f154,plain,(
% 2.02/0.65    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 2.02/0.65    inference(subsumption_resolution,[],[f151,f50])).
% 2.02/0.65  fof(f50,plain,(
% 2.02/0.65    v3_funct_2(sK1,sK0,sK0)),
% 2.02/0.65    inference(cnf_transformation,[],[f45])).
% 2.02/0.65  fof(f151,plain,(
% 2.02/0.65    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 2.02/0.65    inference(resolution,[],[f63,f51])).
% 2.02/0.65  fof(f57,plain,(
% 2.02/0.65    ~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1))),
% 2.02/0.65    inference(cnf_transformation,[],[f45])).
% 2.02/0.65  fof(f455,plain,(
% 2.02/0.65    spl3_1 | ~spl3_5 | ~spl3_6 | spl3_7),
% 2.02/0.65    inference(avatar_contradiction_clause,[],[f454])).
% 2.02/0.65  fof(f454,plain,(
% 2.02/0.65    $false | (spl3_1 | ~spl3_5 | ~spl3_6 | spl3_7)),
% 2.02/0.65    inference(subsumption_resolution,[],[f432,f58])).
% 2.02/0.65  fof(f432,plain,(
% 2.02/0.65    ~v1_xboole_0(k1_xboole_0) | (spl3_1 | ~spl3_5 | ~spl3_6 | spl3_7)),
% 2.02/0.65    inference(superposition,[],[f100,f402])).
% 2.02/0.65  fof(f100,plain,(
% 2.02/0.65    ~v1_xboole_0(sK0) | spl3_1),
% 2.02/0.65    inference(avatar_component_clause,[],[f98])).
% 2.02/0.65  fof(f98,plain,(
% 2.02/0.65    spl3_1 <=> v1_xboole_0(sK0)),
% 2.02/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 2.02/0.65  fof(f393,plain,(
% 2.02/0.65    ~spl3_7),
% 2.02/0.65    inference(avatar_contradiction_clause,[],[f392])).
% 2.02/0.65  fof(f392,plain,(
% 2.02/0.65    $false | ~spl3_7),
% 2.02/0.65    inference(subsumption_resolution,[],[f391,f112])).
% 2.02/0.65  fof(f112,plain,(
% 2.02/0.65    r2_relset_1(sK0,sK0,sK2,sK2)),
% 2.02/0.65    inference(resolution,[],[f84,f55])).
% 2.02/0.65  fof(f391,plain,(
% 2.02/0.65    ~r2_relset_1(sK0,sK0,sK2,sK2) | ~spl3_7),
% 2.02/0.65    inference(superposition,[],[f239,f220])).
% 2.02/0.65  fof(f220,plain,(
% 2.02/0.65    sK2 = k2_funct_1(sK1) | ~spl3_7),
% 2.02/0.65    inference(avatar_component_clause,[],[f218])).
% 2.02/0.65  fof(f377,plain,(
% 2.02/0.65    spl3_4),
% 2.02/0.65    inference(avatar_contradiction_clause,[],[f376])).
% 2.02/0.65  fof(f376,plain,(
% 2.02/0.65    $false | spl3_4),
% 2.02/0.65    inference(subsumption_resolution,[],[f375,f48])).
% 2.02/0.65  fof(f375,plain,(
% 2.02/0.65    ~v1_funct_1(sK1) | spl3_4),
% 2.02/0.65    inference(subsumption_resolution,[],[f370,f145])).
% 2.02/0.65  fof(f145,plain,(
% 2.02/0.65    ~m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl3_4),
% 2.02/0.65    inference(avatar_component_clause,[],[f143])).
% 2.02/0.65  fof(f143,plain,(
% 2.02/0.65    spl3_4 <=> m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.02/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 2.02/0.65  fof(f370,plain,(
% 2.02/0.65    m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1)),
% 2.02/0.65    inference(resolution,[],[f202,f51])).
% 2.02/0.65  fof(f202,plain,(
% 2.02/0.65    ( ! [X4,X5,X3] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | m1_subset_1(k1_partfun1(X3,X4,sK0,sK0,X5,sK2),k1_zfmisc_1(k2_zfmisc_1(X3,sK0))) | ~v1_funct_1(X5)) )),
% 2.02/0.65    inference(subsumption_resolution,[],[f199,f52])).
% 2.02/0.65  fof(f199,plain,(
% 2.02/0.65    ( ! [X4,X5,X3] : (m1_subset_1(k1_partfun1(X3,X4,sK0,sK0,X5,sK2),k1_zfmisc_1(k2_zfmisc_1(X3,sK0))) | ~v1_funct_1(sK2) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_1(X5)) )),
% 2.02/0.65    inference(resolution,[],[f81,f55])).
% 2.02/0.65  fof(f81,plain,(
% 2.02/0.65    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.02/0.65    inference(cnf_transformation,[],[f42])).
% 2.02/0.65  fof(f42,plain,(
% 2.02/0.65    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.02/0.65    inference(flattening,[],[f41])).
% 2.02/0.65  fof(f41,plain,(
% 2.02/0.65    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.02/0.65    inference(ennf_transformation,[],[f10])).
% 2.02/0.65  fof(f10,axiom,(
% 2.02/0.65    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 2.02/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 2.02/0.65  fof(f243,plain,(
% 2.02/0.65    spl3_6),
% 2.02/0.65    inference(avatar_contradiction_clause,[],[f242])).
% 2.02/0.65  fof(f242,plain,(
% 2.02/0.65    $false | spl3_6),
% 2.02/0.65    inference(subsumption_resolution,[],[f241,f228])).
% 2.02/0.65  fof(f228,plain,(
% 2.02/0.65    sK0 = k2_relat_1(sK1)),
% 2.02/0.65    inference(subsumption_resolution,[],[f227,f88])).
% 2.02/0.65  fof(f88,plain,(
% 2.02/0.65    v1_relat_1(sK1)),
% 2.02/0.65    inference(resolution,[],[f69,f51])).
% 2.02/0.65  fof(f69,plain,(
% 2.02/0.65    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 2.02/0.65    inference(cnf_transformation,[],[f30])).
% 2.02/0.65  fof(f30,plain,(
% 2.02/0.65    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.02/0.65    inference(ennf_transformation,[],[f3])).
% 2.02/0.65  fof(f3,axiom,(
% 2.02/0.65    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.02/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 2.02/0.65  fof(f227,plain,(
% 2.02/0.65    sK0 = k2_relat_1(sK1) | ~v1_relat_1(sK1)),
% 2.02/0.65    inference(subsumption_resolution,[],[f226,f91])).
% 2.02/0.65  fof(f91,plain,(
% 2.02/0.65    v5_relat_1(sK1,sK0)),
% 2.02/0.65    inference(resolution,[],[f71,f51])).
% 2.02/0.65  fof(f71,plain,(
% 2.02/0.65    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 2.02/0.65    inference(cnf_transformation,[],[f32])).
% 2.02/0.65  fof(f32,plain,(
% 2.02/0.65    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.02/0.65    inference(ennf_transformation,[],[f19])).
% 2.02/0.65  fof(f19,plain,(
% 2.02/0.65    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 2.02/0.65    inference(pure_predicate_removal,[],[f4])).
% 2.02/0.65  fof(f4,axiom,(
% 2.02/0.65    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.02/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 2.02/0.65  fof(f226,plain,(
% 2.02/0.65    sK0 = k2_relat_1(sK1) | ~v5_relat_1(sK1,sK0) | ~v1_relat_1(sK1)),
% 2.02/0.65    inference(resolution,[],[f128,f61])).
% 2.02/0.65  fof(f61,plain,(
% 2.02/0.65    ( ! [X0,X1] : (~v2_funct_2(X1,X0) | k2_relat_1(X1) = X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.02/0.65    inference(cnf_transformation,[],[f46])).
% 2.02/0.65  fof(f46,plain,(
% 2.02/0.65    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.02/0.65    inference(nnf_transformation,[],[f24])).
% 2.02/0.65  fof(f24,plain,(
% 2.02/0.65    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.02/0.65    inference(flattening,[],[f23])).
% 2.02/0.65  fof(f23,plain,(
% 2.02/0.65    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.02/0.65    inference(ennf_transformation,[],[f9])).
% 2.02/0.65  fof(f9,axiom,(
% 2.02/0.65    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 2.02/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).
% 2.02/0.65  fof(f128,plain,(
% 2.02/0.65    v2_funct_2(sK1,sK0)),
% 2.02/0.65    inference(subsumption_resolution,[],[f127,f48])).
% 2.02/0.65  fof(f127,plain,(
% 2.02/0.65    ~v1_funct_1(sK1) | v2_funct_2(sK1,sK0)),
% 2.02/0.65    inference(subsumption_resolution,[],[f124,f50])).
% 2.02/0.65  fof(f124,plain,(
% 2.02/0.65    ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | v2_funct_2(sK1,sK0)),
% 2.02/0.65    inference(resolution,[],[f74,f51])).
% 2.02/0.65  fof(f74,plain,(
% 2.02/0.65    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v2_funct_2(X2,X1)) )),
% 2.02/0.65    inference(cnf_transformation,[],[f34])).
% 2.02/0.65  fof(f34,plain,(
% 2.02/0.65    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.02/0.65    inference(flattening,[],[f33])).
% 2.02/0.65  fof(f33,plain,(
% 2.02/0.65    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.02/0.65    inference(ennf_transformation,[],[f8])).
% 2.02/0.65  fof(f8,axiom,(
% 2.02/0.65    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 2.02/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).
% 2.02/0.65  fof(f241,plain,(
% 2.02/0.65    sK0 != k2_relat_1(sK1) | spl3_6),
% 2.02/0.65    inference(superposition,[],[f216,f114])).
% 2.02/0.65  fof(f114,plain,(
% 2.02/0.65    k2_relset_1(sK0,sK0,sK1) = k2_relat_1(sK1)),
% 2.02/0.65    inference(resolution,[],[f70,f51])).
% 2.02/0.65  fof(f70,plain,(
% 2.02/0.65    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 2.02/0.65    inference(cnf_transformation,[],[f31])).
% 2.02/0.65  fof(f31,plain,(
% 2.02/0.65    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.02/0.65    inference(ennf_transformation,[],[f6])).
% 2.02/0.65  fof(f6,axiom,(
% 2.02/0.65    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 2.02/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 2.02/0.65  fof(f216,plain,(
% 2.02/0.65    sK0 != k2_relset_1(sK0,sK0,sK1) | spl3_6),
% 2.02/0.65    inference(avatar_component_clause,[],[f214])).
% 2.02/0.65  fof(f150,plain,(
% 2.02/0.65    ~spl3_4 | spl3_5),
% 2.02/0.65    inference(avatar_split_clause,[],[f141,f147,f143])).
% 2.02/0.65  fof(f147,plain,(
% 2.02/0.65    spl3_5 <=> k6_partfun1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2)),
% 2.02/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 2.02/0.65  fof(f141,plain,(
% 2.02/0.65    k6_partfun1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) | ~m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.02/0.65    inference(subsumption_resolution,[],[f140,f59])).
% 2.02/0.65  fof(f59,plain,(
% 2.02/0.65    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.02/0.65    inference(cnf_transformation,[],[f18])).
% 2.02/0.65  fof(f18,plain,(
% 2.02/0.65    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 2.02/0.65    inference(pure_predicate_removal,[],[f12])).
% 2.02/0.65  fof(f12,axiom,(
% 2.02/0.65    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 2.02/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 2.02/0.65  fof(f140,plain,(
% 2.02/0.65    k6_partfun1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) | ~m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.02/0.65    inference(resolution,[],[f78,f56])).
% 2.02/0.65  fof(f78,plain,(
% 2.02/0.65    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.02/0.65    inference(cnf_transformation,[],[f47])).
% 2.02/0.65  fof(f110,plain,(
% 2.02/0.65    ~spl3_1 | spl3_3),
% 2.02/0.65    inference(avatar_split_clause,[],[f95,f107,f98])).
% 2.02/0.65  fof(f95,plain,(
% 2.02/0.65    v1_xboole_0(sK2) | ~v1_xboole_0(sK0)),
% 2.02/0.65    inference(resolution,[],[f60,f55])).
% 2.02/0.65  fof(f105,plain,(
% 2.02/0.65    ~spl3_1 | spl3_2),
% 2.02/0.65    inference(avatar_split_clause,[],[f94,f102,f98])).
% 2.02/0.65  fof(f94,plain,(
% 2.02/0.65    v1_xboole_0(sK1) | ~v1_xboole_0(sK0)),
% 2.02/0.65    inference(resolution,[],[f60,f51])).
% 2.02/0.65  % SZS output end Proof for theBenchmark
% 2.02/0.65  % (20922)------------------------------
% 2.02/0.65  % (20922)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.02/0.65  % (20922)Termination reason: Refutation
% 2.02/0.65  
% 2.02/0.65  % (20922)Memory used [KB]: 11001
% 2.02/0.65  % (20922)Time elapsed: 0.212 s
% 2.02/0.65  % (20922)------------------------------
% 2.02/0.65  % (20922)------------------------------
% 2.38/0.67  % (20911)Success in time 0.304 s
%------------------------------------------------------------------------------
