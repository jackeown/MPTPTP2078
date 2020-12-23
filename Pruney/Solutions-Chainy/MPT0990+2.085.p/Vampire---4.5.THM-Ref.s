%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:43 EST 2020

% Result     : Theorem 2.82s
% Output     : Refutation 3.15s
% Verified   : 
% Statistics : Number of formulae       :  206 (1298 expanded)
%              Number of leaves         :   23 ( 407 expanded)
%              Depth                    :   24
%              Number of atoms          :  785 (12548 expanded)
%              Number of equality atoms :  228 (4304 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1530,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f338,f347,f633,f1529])).

fof(f1529,plain,
    ( ~ spl4_11
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(avatar_contradiction_clause,[],[f1528])).

fof(f1528,plain,
    ( $false
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f1527,f62])).

fof(f62,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f22,f48,f47])).

fof(f47,plain,
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

fof(f48,plain,
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).

fof(f1527,plain,
    ( k2_funct_1(sK2) = sK3
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(backward_demodulation,[],[f404,f1485])).

fof(f1485,plain,
    ( sK3 = k5_relat_1(k6_partfun1(sK1),k2_funct_1(sK2))
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(backward_demodulation,[],[f1418,f1454])).

fof(f1454,plain,
    ( k5_relat_1(sK3,sK2) = k6_partfun1(sK1)
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(backward_demodulation,[],[f346,f1452])).

fof(f1452,plain,
    ( sK2 = k2_funct_1(sK3)
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(forward_demodulation,[],[f1451,f271])).

fof(f271,plain,(
    sK2 = k5_relat_1(sK2,k6_partfun1(sK1)) ),
    inference(backward_demodulation,[],[f111,f270])).

fof(f270,plain,(
    k6_partfun1(k2_relat_1(sK2)) = k6_partfun1(sK1) ),
    inference(backward_demodulation,[],[f149,f265])).

fof(f265,plain,(
    k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
    inference(subsumption_resolution,[],[f264,f51])).

fof(f51,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f264,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f263,f52])).

fof(f52,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f263,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f262,f53])).

fof(f53,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f49])).

fof(f262,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f261,f59])).

fof(f59,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f261,plain,
    ( ~ v2_funct_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f260,f61])).

fof(f61,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f49])).

fof(f260,plain,
    ( k1_xboole_0 = sK1
    | ~ v2_funct_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(trivial_inequality_removal,[],[f259])).

fof(f259,plain,
    ( sK1 != sK1
    | k1_xboole_0 = sK1
    | ~ v2_funct_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(superposition,[],[f82,f57])).

fof(f57,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
            & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_2)).

fof(f149,plain,(
    k6_partfun1(k2_relat_1(sK2)) = k5_relat_1(k2_funct_1(sK2),sK2) ),
    inference(subsumption_resolution,[],[f148,f106])).

fof(f106,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f80,f53])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f148,plain,
    ( k6_partfun1(k2_relat_1(sK2)) = k5_relat_1(k2_funct_1(sK2),sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f146,f51])).

fof(f146,plain,
    ( k6_partfun1(k2_relat_1(sK2)) = k5_relat_1(k2_funct_1(sK2),sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f100,f59])).

fof(f100,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f79,f63])).

fof(f63,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f79,plain,(
    ! [X0] :
      ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
          & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

fof(f111,plain,(
    sK2 = k5_relat_1(sK2,k6_partfun1(k2_relat_1(sK2))) ),
    inference(resolution,[],[f98,f106])).

fof(f98,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 ) ),
    inference(definition_unfolding,[],[f69,f63])).

fof(f69,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

fof(f1451,plain,
    ( k5_relat_1(sK2,k6_partfun1(sK1)) = k2_funct_1(sK3)
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(forward_demodulation,[],[f1450,f834])).

fof(f834,plain,
    ( k2_funct_1(sK3) = k5_relat_1(k6_partfun1(sK0),k2_funct_1(sK3))
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(forward_demodulation,[],[f715,f814])).

fof(f814,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(forward_demodulation,[],[f793,f96])).

fof(f96,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f68,f63])).

fof(f68,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f793,plain,
    ( k2_relat_1(sK3) = k2_relat_1(k6_partfun1(sK0))
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(superposition,[],[f96,f781])).

fof(f781,plain,
    ( k6_partfun1(sK0) = k6_partfun1(k2_relat_1(sK3))
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(forward_demodulation,[],[f665,f333])).

fof(f333,plain,
    ( k6_partfun1(sK0) = k5_relat_1(k2_funct_1(sK3),sK3)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f331])).

fof(f331,plain,
    ( spl4_11
  <=> k6_partfun1(sK0) = k5_relat_1(k2_funct_1(sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f665,plain,
    ( k6_partfun1(k2_relat_1(sK3)) = k5_relat_1(k2_funct_1(sK3),sK3)
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f664,f107])).

fof(f107,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f80,f56])).

fof(f56,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f49])).

fof(f664,plain,
    ( k6_partfun1(k2_relat_1(sK3)) = k5_relat_1(k2_funct_1(sK3),sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f657,f54])).

fof(f54,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f49])).

fof(f657,plain,
    ( k6_partfun1(k2_relat_1(sK3)) = k5_relat_1(k2_funct_1(sK3),sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_12 ),
    inference(resolution,[],[f336,f100])).

fof(f336,plain,
    ( v2_funct_1(sK3)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f335])).

fof(f335,plain,
    ( spl4_12
  <=> v2_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f715,plain,
    ( k2_funct_1(sK3) = k5_relat_1(k6_partfun1(k2_relat_1(sK3)),k2_funct_1(sK3))
    | ~ spl4_12 ),
    inference(backward_demodulation,[],[f405,f673])).

fof(f673,plain,
    ( k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3))
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f672,f107])).

fof(f672,plain,
    ( k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f661,f54])).

fof(f661,plain,
    ( k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_12 ),
    inference(resolution,[],[f336,f74])).

fof(f74,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f405,plain,(
    k2_funct_1(sK3) = k5_relat_1(k6_partfun1(k1_relat_1(k2_funct_1(sK3))),k2_funct_1(sK3)) ),
    inference(subsumption_resolution,[],[f401,f107])).

fof(f401,plain,
    ( k2_funct_1(sK3) = k5_relat_1(k6_partfun1(k1_relat_1(k2_funct_1(sK3))),k2_funct_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f114,f54])).

fof(f114,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | k2_funct_1(X0) = k5_relat_1(k6_partfun1(k1_relat_1(k2_funct_1(X0))),k2_funct_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f99,f72])).

fof(f72,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f99,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0 ) ),
    inference(definition_unfolding,[],[f70,f63])).

fof(f70,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).

fof(f1450,plain,
    ( k5_relat_1(sK2,k6_partfun1(sK1)) = k5_relat_1(k6_partfun1(sK0),k2_funct_1(sK3))
    | ~ spl4_13 ),
    inference(forward_demodulation,[],[f1449,f617])).

fof(f617,plain,(
    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) ),
    inference(global_subsumption,[],[f590,f616])).

fof(f616,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f577,f180])).

fof(f180,plain,(
    ! [X2,X3] :
      ( ~ r2_relset_1(X2,X2,X3,k6_partfun1(X2))
      | k6_partfun1(X2) = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ) ),
    inference(resolution,[],[f88,f93])).

fof(f93,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f64,f63])).

fof(f64,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

fof(f88,plain,(
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
    inference(nnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f577,plain,(
    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0)) ),
    inference(backward_demodulation,[],[f58,f450])).

fof(f450,plain,(
    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f447,f51])).

fof(f447,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f190,f53])).

fof(f190,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | k5_relat_1(X5,sK3) = k1_partfun1(X3,X4,sK1,sK0,X5,sK3)
      | ~ v1_funct_1(X5) ) ),
    inference(subsumption_resolution,[],[f187,f54])).

fof(f187,plain,(
    ! [X4,X5,X3] :
      ( k5_relat_1(X5,sK3) = k1_partfun1(X3,X4,sK1,sK0,X5,sK3)
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_1(X5) ) ),
    inference(resolution,[],[f90,f56])).

fof(f90,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f58,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f49])).

fof(f590,plain,(
    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f589,f51])).

fof(f589,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f588,f53])).

fof(f588,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f587,f54])).

fof(f587,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f579,f56])).

fof(f579,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(superposition,[],[f92,f450])).

fof(f92,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
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
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f1449,plain,
    ( k5_relat_1(sK2,k6_partfun1(sK1)) = k5_relat_1(k5_relat_1(sK2,sK3),k2_funct_1(sK3))
    | ~ spl4_13 ),
    inference(forward_demodulation,[],[f1446,f346])).

fof(f1446,plain,(
    k5_relat_1(k5_relat_1(sK2,sK3),k2_funct_1(sK3)) = k5_relat_1(sK2,k5_relat_1(sK3,k2_funct_1(sK3))) ),
    inference(resolution,[],[f1081,f107])).

fof(f1081,plain,(
    ! [X15] :
      ( ~ v1_relat_1(X15)
      | k5_relat_1(k5_relat_1(sK2,X15),k2_funct_1(sK3)) = k5_relat_1(sK2,k5_relat_1(X15,k2_funct_1(sK3))) ) ),
    inference(resolution,[],[f576,f106])).

fof(f576,plain,(
    ! [X17,X18] :
      ( ~ v1_relat_1(X18)
      | ~ v1_relat_1(X17)
      | k5_relat_1(k5_relat_1(X18,X17),k2_funct_1(sK3)) = k5_relat_1(X18,k5_relat_1(X17,k2_funct_1(sK3))) ) ),
    inference(subsumption_resolution,[],[f571,f107])).

fof(f571,plain,(
    ! [X17,X18] :
      ( ~ v1_relat_1(X17)
      | ~ v1_relat_1(X18)
      | k5_relat_1(k5_relat_1(X18,X17),k2_funct_1(sK3)) = k5_relat_1(X18,k5_relat_1(X17,k2_funct_1(sK3)))
      | ~ v1_relat_1(sK3) ) ),
    inference(resolution,[],[f158,f54])).

fof(f158,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k5_relat_1(k5_relat_1(X0,X1),k2_funct_1(X2)) = k5_relat_1(X0,k5_relat_1(X1,k2_funct_1(X2)))
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f71,f72])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
      | ~ v1_relat_1(X1)
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
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

fof(f346,plain,
    ( k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f344])).

fof(f344,plain,
    ( spl4_13
  <=> k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f1418,plain,
    ( sK3 = k5_relat_1(k5_relat_1(sK3,sK2),k2_funct_1(sK2))
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(forward_demodulation,[],[f1417,f788])).

fof(f788,plain,
    ( sK3 = k5_relat_1(sK3,k6_partfun1(sK0))
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(backward_demodulation,[],[f112,f781])).

fof(f112,plain,(
    sK3 = k5_relat_1(sK3,k6_partfun1(k2_relat_1(sK3))) ),
    inference(resolution,[],[f98,f107])).

fof(f1417,plain,(
    k5_relat_1(sK3,k6_partfun1(sK0)) = k5_relat_1(k5_relat_1(sK3,sK2),k2_funct_1(sK2)) ),
    inference(forward_demodulation,[],[f1413,f213])).

fof(f213,plain,(
    k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f212,f51])).

fof(f212,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f211,f52])).

fof(f211,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f210,f53])).

fof(f210,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f209,f59])).

fof(f209,plain,
    ( ~ v2_funct_1(sK2)
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f208,f61])).

fof(f208,plain,
    ( k1_xboole_0 = sK1
    | ~ v2_funct_1(sK2)
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(trivial_inequality_removal,[],[f207])).

fof(f207,plain,
    ( sK1 != sK1
    | k1_xboole_0 = sK1
    | ~ v2_funct_1(sK2)
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(superposition,[],[f81,f57])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f1413,plain,(
    k5_relat_1(k5_relat_1(sK3,sK2),k2_funct_1(sK2)) = k5_relat_1(sK3,k5_relat_1(sK2,k2_funct_1(sK2))) ),
    inference(resolution,[],[f1025,f106])).

fof(f1025,plain,(
    ! [X15] :
      ( ~ v1_relat_1(X15)
      | k5_relat_1(k5_relat_1(sK3,X15),k2_funct_1(sK2)) = k5_relat_1(sK3,k5_relat_1(X15,k2_funct_1(sK2))) ) ),
    inference(resolution,[],[f575,f107])).

fof(f575,plain,(
    ! [X15,X16] :
      ( ~ v1_relat_1(X16)
      | ~ v1_relat_1(X15)
      | k5_relat_1(k5_relat_1(X16,X15),k2_funct_1(sK2)) = k5_relat_1(X16,k5_relat_1(X15,k2_funct_1(sK2))) ) ),
    inference(subsumption_resolution,[],[f570,f106])).

fof(f570,plain,(
    ! [X15,X16] :
      ( ~ v1_relat_1(X15)
      | ~ v1_relat_1(X16)
      | k5_relat_1(k5_relat_1(X16,X15),k2_funct_1(sK2)) = k5_relat_1(X16,k5_relat_1(X15,k2_funct_1(sK2)))
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f158,f51])).

fof(f404,plain,(
    k2_funct_1(sK2) = k5_relat_1(k6_partfun1(sK1),k2_funct_1(sK2)) ),
    inference(forward_demodulation,[],[f403,f314])).

fof(f314,plain,(
    sK1 = k1_relat_1(k2_funct_1(sK2)) ),
    inference(backward_demodulation,[],[f125,f286])).

fof(f286,plain,(
    sK1 = k2_relat_1(sK2) ),
    inference(forward_demodulation,[],[f275,f96])).

fof(f275,plain,(
    k2_relat_1(sK2) = k2_relat_1(k6_partfun1(sK1)) ),
    inference(superposition,[],[f96,f270])).

fof(f125,plain,(
    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f124,f106])).

fof(f124,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f122,f51])).

fof(f122,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f74,f59])).

fof(f403,plain,(
    k2_funct_1(sK2) = k5_relat_1(k6_partfun1(k1_relat_1(k2_funct_1(sK2))),k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f400,f106])).

fof(f400,plain,
    ( k2_funct_1(sK2) = k5_relat_1(k6_partfun1(k1_relat_1(k2_funct_1(sK2))),k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f114,f51])).

fof(f633,plain,(
    spl4_12 ),
    inference(avatar_contradiction_clause,[],[f632])).

fof(f632,plain,
    ( $false
    | spl4_12 ),
    inference(subsumption_resolution,[],[f628,f94])).

fof(f94,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f66,f63])).

fof(f66,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f628,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | spl4_12 ),
    inference(backward_demodulation,[],[f586,f617])).

fof(f586,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | spl4_12 ),
    inference(subsumption_resolution,[],[f585,f54])).

fof(f585,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | ~ v1_funct_1(sK3)
    | spl4_12 ),
    inference(subsumption_resolution,[],[f584,f55])).

fof(f55,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f584,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | spl4_12 ),
    inference(subsumption_resolution,[],[f583,f56])).

fof(f583,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | spl4_12 ),
    inference(subsumption_resolution,[],[f582,f60])).

fof(f60,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f49])).

fof(f582,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | k1_xboole_0 = sK0
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | spl4_12 ),
    inference(subsumption_resolution,[],[f578,f337])).

fof(f337,plain,
    ( ~ v2_funct_1(sK3)
    | spl4_12 ),
    inference(avatar_component_clause,[],[f335])).

fof(f578,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | v2_funct_1(sK3)
    | k1_xboole_0 = sK0
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(superposition,[],[f368,f450])).

fof(f368,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1))
      | v2_funct_1(X1)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
      | ~ v1_funct_2(X1,sK1,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(subsumption_resolution,[],[f367,f51])).

fof(f367,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | v2_funct_1(X1)
      | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
      | ~ v1_funct_2(X1,sK1,X0)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_1(sK2) ) ),
    inference(subsumption_resolution,[],[f366,f52])).

fof(f366,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | v2_funct_1(X1)
      | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
      | ~ v1_funct_2(X1,sK1,X0)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(sK2,sK0,sK1)
      | ~ v1_funct_1(sK2) ) ),
    inference(subsumption_resolution,[],[f365,f53])).

fof(f365,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | v2_funct_1(X1)
      | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
      | ~ v1_funct_2(X1,sK1,X0)
      | ~ v1_funct_1(X1)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_2(sK2,sK0,sK1)
      | ~ v1_funct_1(sK2) ) ),
    inference(trivial_inequality_removal,[],[f362])).

fof(f362,plain,(
    ! [X0,X1] :
      ( sK1 != sK1
      | k1_xboole_0 = X0
      | v2_funct_1(X1)
      | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
      | ~ v1_funct_2(X1,sK1,X0)
      | ~ v1_funct_1(X1)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_2(sK2,sK0,sK1)
      | ~ v1_funct_1(sK2) ) ),
    inference(superposition,[],[f86,f57])).

fof(f86,plain,(
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
    inference(cnf_transformation,[],[f40])).

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
    inference(flattening,[],[f39])).

fof(f39,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_funct_2)).

fof(f347,plain,
    ( spl4_13
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f342,f335,f344])).

fof(f342,plain,
    ( ~ v2_funct_1(sK3)
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) ),
    inference(subsumption_resolution,[],[f341,f54])).

fof(f341,plain,
    ( ~ v2_funct_1(sK3)
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f340,f55])).

fof(f340,plain,
    ( ~ v2_funct_1(sK3)
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f339,f56])).

fof(f339,plain,
    ( ~ v2_funct_1(sK3)
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f324,f60])).

fof(f324,plain,
    ( k1_xboole_0 = sK0
    | ~ v2_funct_1(sK3)
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(trivial_inequality_removal,[],[f323])).

fof(f323,plain,
    ( sK0 != sK0
    | k1_xboole_0 = sK0
    | ~ v2_funct_1(sK3)
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(superposition,[],[f81,f321])).

fof(f321,plain,(
    sK0 = k2_relset_1(sK1,sK0,sK3) ),
    inference(subsumption_resolution,[],[f320,f54])).

fof(f320,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f319,f55])).

fof(f319,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f318,f56])).

fof(f318,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f317,f51])).

fof(f317,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f316,f52])).

fof(f316,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f315,f53])).

fof(f315,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(resolution,[],[f83,f58])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | k2_relset_1(X0,X1,X2) = X1
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
          ( k2_relset_1(X0,X1,X2) = X1
          | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
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
          ( k2_relset_1(X0,X1,X2) = X1
          | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_funct_2)).

fof(f338,plain,
    ( spl4_11
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f329,f335,f331])).

fof(f329,plain,
    ( ~ v2_funct_1(sK3)
    | k6_partfun1(sK0) = k5_relat_1(k2_funct_1(sK3),sK3) ),
    inference(subsumption_resolution,[],[f328,f54])).

fof(f328,plain,
    ( ~ v2_funct_1(sK3)
    | k6_partfun1(sK0) = k5_relat_1(k2_funct_1(sK3),sK3)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f327,f55])).

fof(f327,plain,
    ( ~ v2_funct_1(sK3)
    | k6_partfun1(sK0) = k5_relat_1(k2_funct_1(sK3),sK3)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f326,f56])).

fof(f326,plain,
    ( ~ v2_funct_1(sK3)
    | k6_partfun1(sK0) = k5_relat_1(k2_funct_1(sK3),sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f325,f60])).

fof(f325,plain,
    ( k1_xboole_0 = sK0
    | ~ v2_funct_1(sK3)
    | k6_partfun1(sK0) = k5_relat_1(k2_funct_1(sK3),sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(trivial_inequality_removal,[],[f322])).

fof(f322,plain,
    ( sK0 != sK0
    | k1_xboole_0 = sK0
    | ~ v2_funct_1(sK3)
    | k6_partfun1(sK0) = k5_relat_1(k2_funct_1(sK3),sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(superposition,[],[f82,f321])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:17:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.57  % (26606)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.57  % (26602)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.57  % (26614)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.60  % (26607)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.91/0.61  % (26621)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.91/0.61  % (26626)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.91/0.61  % (26610)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.91/0.62  % (26604)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.91/0.62  % (26630)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 2.03/0.63  % (26603)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 2.03/0.63  % (26605)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 2.03/0.63  % (26632)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 2.03/0.63  % (26608)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 2.03/0.63  % (26613)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 2.03/0.63  % (26612)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 2.03/0.63  % (26625)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 2.03/0.64  % (26622)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 2.03/0.64  % (26617)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 2.03/0.64  % (26619)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 2.03/0.65  % (26629)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 2.03/0.65  % (26627)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 2.03/0.65  % (26620)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 2.03/0.65  % (26616)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 2.22/0.65  % (26609)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 2.22/0.66  % (26618)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 2.22/0.66  % (26611)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 2.22/0.66  % (26624)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 2.22/0.66  % (26615)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 2.22/0.67  % (26623)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 2.22/0.67  % (26618)Refutation not found, incomplete strategy% (26618)------------------------------
% 2.22/0.67  % (26618)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.22/0.67  % (26618)Termination reason: Refutation not found, incomplete strategy
% 2.22/0.67  
% 2.22/0.67  % (26618)Memory used [KB]: 10746
% 2.22/0.67  % (26618)Time elapsed: 0.176 s
% 2.22/0.67  % (26618)------------------------------
% 2.22/0.67  % (26618)------------------------------
% 2.22/0.67  % (26628)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 2.82/0.77  % (26608)Refutation found. Thanks to Tanya!
% 2.82/0.77  % SZS status Theorem for theBenchmark
% 3.15/0.79  % SZS output start Proof for theBenchmark
% 3.15/0.79  fof(f1530,plain,(
% 3.15/0.79    $false),
% 3.15/0.79    inference(avatar_sat_refutation,[],[f338,f347,f633,f1529])).
% 3.15/0.79  fof(f1529,plain,(
% 3.15/0.79    ~spl4_11 | ~spl4_12 | ~spl4_13),
% 3.15/0.79    inference(avatar_contradiction_clause,[],[f1528])).
% 3.15/0.79  fof(f1528,plain,(
% 3.15/0.79    $false | (~spl4_11 | ~spl4_12 | ~spl4_13)),
% 3.15/0.79    inference(subsumption_resolution,[],[f1527,f62])).
% 3.15/0.79  fof(f62,plain,(
% 3.15/0.79    k2_funct_1(sK2) != sK3),
% 3.15/0.79    inference(cnf_transformation,[],[f49])).
% 3.15/0.79  fof(f49,plain,(
% 3.15/0.79    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 3.15/0.79    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f22,f48,f47])).
% 3.15/0.79  fof(f47,plain,(
% 3.15/0.79    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 3.15/0.79    introduced(choice_axiom,[])).
% 3.15/0.79  fof(f48,plain,(
% 3.15/0.79    ? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) => (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3))),
% 3.15/0.79    introduced(choice_axiom,[])).
% 3.15/0.79  fof(f22,plain,(
% 3.15/0.79    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 3.15/0.79    inference(flattening,[],[f21])).
% 3.15/0.79  fof(f21,plain,(
% 3.15/0.79    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.15/0.79    inference(ennf_transformation,[],[f20])).
% 3.15/0.79  fof(f20,negated_conjecture,(
% 3.15/0.79    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 3.15/0.79    inference(negated_conjecture,[],[f19])).
% 3.15/0.79  fof(f19,conjecture,(
% 3.15/0.79    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 3.15/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).
% 3.15/0.79  fof(f1527,plain,(
% 3.15/0.79    k2_funct_1(sK2) = sK3 | (~spl4_11 | ~spl4_12 | ~spl4_13)),
% 3.15/0.79    inference(backward_demodulation,[],[f404,f1485])).
% 3.15/0.79  fof(f1485,plain,(
% 3.15/0.79    sK3 = k5_relat_1(k6_partfun1(sK1),k2_funct_1(sK2)) | (~spl4_11 | ~spl4_12 | ~spl4_13)),
% 3.15/0.79    inference(backward_demodulation,[],[f1418,f1454])).
% 3.15/0.79  fof(f1454,plain,(
% 3.15/0.79    k5_relat_1(sK3,sK2) = k6_partfun1(sK1) | (~spl4_11 | ~spl4_12 | ~spl4_13)),
% 3.15/0.79    inference(backward_demodulation,[],[f346,f1452])).
% 3.15/0.79  fof(f1452,plain,(
% 3.15/0.79    sK2 = k2_funct_1(sK3) | (~spl4_11 | ~spl4_12 | ~spl4_13)),
% 3.15/0.79    inference(forward_demodulation,[],[f1451,f271])).
% 3.15/0.79  fof(f271,plain,(
% 3.15/0.79    sK2 = k5_relat_1(sK2,k6_partfun1(sK1))),
% 3.15/0.79    inference(backward_demodulation,[],[f111,f270])).
% 3.15/0.79  fof(f270,plain,(
% 3.15/0.79    k6_partfun1(k2_relat_1(sK2)) = k6_partfun1(sK1)),
% 3.15/0.79    inference(backward_demodulation,[],[f149,f265])).
% 3.15/0.79  fof(f265,plain,(
% 3.15/0.79    k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)),
% 3.15/0.79    inference(subsumption_resolution,[],[f264,f51])).
% 3.15/0.79  fof(f51,plain,(
% 3.15/0.79    v1_funct_1(sK2)),
% 3.15/0.79    inference(cnf_transformation,[],[f49])).
% 3.15/0.79  fof(f264,plain,(
% 3.15/0.79    k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) | ~v1_funct_1(sK2)),
% 3.15/0.79    inference(subsumption_resolution,[],[f263,f52])).
% 3.15/0.79  fof(f52,plain,(
% 3.15/0.79    v1_funct_2(sK2,sK0,sK1)),
% 3.15/0.79    inference(cnf_transformation,[],[f49])).
% 3.15/0.79  fof(f263,plain,(
% 3.15/0.79    k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 3.15/0.79    inference(subsumption_resolution,[],[f262,f53])).
% 3.15/0.79  fof(f53,plain,(
% 3.15/0.79    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.15/0.79    inference(cnf_transformation,[],[f49])).
% 3.15/0.79  fof(f262,plain,(
% 3.15/0.79    k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 3.15/0.79    inference(subsumption_resolution,[],[f261,f59])).
% 3.15/0.79  fof(f59,plain,(
% 3.15/0.79    v2_funct_1(sK2)),
% 3.15/0.79    inference(cnf_transformation,[],[f49])).
% 3.15/0.79  fof(f261,plain,(
% 3.15/0.79    ~v2_funct_1(sK2) | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 3.15/0.79    inference(subsumption_resolution,[],[f260,f61])).
% 3.15/0.79  fof(f61,plain,(
% 3.15/0.79    k1_xboole_0 != sK1),
% 3.15/0.79    inference(cnf_transformation,[],[f49])).
% 3.15/0.79  fof(f260,plain,(
% 3.15/0.79    k1_xboole_0 = sK1 | ~v2_funct_1(sK2) | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 3.15/0.79    inference(trivial_inequality_removal,[],[f259])).
% 3.15/0.79  fof(f259,plain,(
% 3.15/0.79    sK1 != sK1 | k1_xboole_0 = sK1 | ~v2_funct_1(sK2) | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 3.15/0.79    inference(superposition,[],[f82,f57])).
% 3.15/0.79  fof(f57,plain,(
% 3.15/0.79    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 3.15/0.79    inference(cnf_transformation,[],[f49])).
% 3.15/0.79  fof(f82,plain,(
% 3.15/0.79    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.15/0.79    inference(cnf_transformation,[],[f36])).
% 3.15/0.79  fof(f36,plain,(
% 3.15/0.79    ! [X0,X1,X2] : ((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.15/0.79    inference(flattening,[],[f35])).
% 3.15/0.79  fof(f35,plain,(
% 3.15/0.79    ! [X0,X1,X2] : ((((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.15/0.79    inference(ennf_transformation,[],[f18])).
% 3.15/0.79  fof(f18,axiom,(
% 3.15/0.79    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1)))),
% 3.15/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_2)).
% 3.15/0.79  fof(f149,plain,(
% 3.15/0.79    k6_partfun1(k2_relat_1(sK2)) = k5_relat_1(k2_funct_1(sK2),sK2)),
% 3.15/0.79    inference(subsumption_resolution,[],[f148,f106])).
% 3.15/0.79  fof(f106,plain,(
% 3.15/0.79    v1_relat_1(sK2)),
% 3.15/0.79    inference(resolution,[],[f80,f53])).
% 3.15/0.79  fof(f80,plain,(
% 3.15/0.79    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 3.15/0.79    inference(cnf_transformation,[],[f34])).
% 3.15/0.79  fof(f34,plain,(
% 3.15/0.79    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.15/0.79    inference(ennf_transformation,[],[f10])).
% 3.15/0.79  fof(f10,axiom,(
% 3.15/0.79    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.15/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 3.15/0.79  fof(f148,plain,(
% 3.15/0.79    k6_partfun1(k2_relat_1(sK2)) = k5_relat_1(k2_funct_1(sK2),sK2) | ~v1_relat_1(sK2)),
% 3.15/0.79    inference(subsumption_resolution,[],[f146,f51])).
% 3.15/0.79  fof(f146,plain,(
% 3.15/0.79    k6_partfun1(k2_relat_1(sK2)) = k5_relat_1(k2_funct_1(sK2),sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 3.15/0.79    inference(resolution,[],[f100,f59])).
% 3.15/0.79  fof(f100,plain,(
% 3.15/0.79    ( ! [X0] : (~v2_funct_1(X0) | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.15/0.79    inference(definition_unfolding,[],[f79,f63])).
% 3.15/0.79  fof(f63,plain,(
% 3.15/0.79    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 3.15/0.79    inference(cnf_transformation,[],[f15])).
% 3.15/0.79  fof(f15,axiom,(
% 3.15/0.79    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 3.15/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 3.15/0.79  fof(f79,plain,(
% 3.15/0.79    ( ! [X0] : (k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.15/0.79    inference(cnf_transformation,[],[f33])).
% 3.15/0.79  fof(f33,plain,(
% 3.15/0.79    ! [X0] : ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.15/0.79    inference(flattening,[],[f32])).
% 3.15/0.79  fof(f32,plain,(
% 3.15/0.79    ! [X0] : (((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.15/0.79    inference(ennf_transformation,[],[f9])).
% 3.15/0.79  fof(f9,axiom,(
% 3.15/0.79    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)))))),
% 3.15/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).
% 3.15/0.79  fof(f111,plain,(
% 3.15/0.79    sK2 = k5_relat_1(sK2,k6_partfun1(k2_relat_1(sK2)))),
% 3.15/0.79    inference(resolution,[],[f98,f106])).
% 3.15/0.79  fof(f98,plain,(
% 3.15/0.79    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0) )),
% 3.15/0.79    inference(definition_unfolding,[],[f69,f63])).
% 3.15/0.79  fof(f69,plain,(
% 3.15/0.79    ( ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 3.15/0.79    inference(cnf_transformation,[],[f23])).
% 3.15/0.79  fof(f23,plain,(
% 3.15/0.79    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 3.15/0.79    inference(ennf_transformation,[],[f4])).
% 3.15/0.79  fof(f4,axiom,(
% 3.15/0.79    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 3.15/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).
% 3.15/0.79  fof(f1451,plain,(
% 3.15/0.79    k5_relat_1(sK2,k6_partfun1(sK1)) = k2_funct_1(sK3) | (~spl4_11 | ~spl4_12 | ~spl4_13)),
% 3.15/0.79    inference(forward_demodulation,[],[f1450,f834])).
% 3.15/0.79  fof(f834,plain,(
% 3.15/0.79    k2_funct_1(sK3) = k5_relat_1(k6_partfun1(sK0),k2_funct_1(sK3)) | (~spl4_11 | ~spl4_12)),
% 3.15/0.79    inference(forward_demodulation,[],[f715,f814])).
% 3.15/0.79  fof(f814,plain,(
% 3.15/0.79    sK0 = k2_relat_1(sK3) | (~spl4_11 | ~spl4_12)),
% 3.15/0.79    inference(forward_demodulation,[],[f793,f96])).
% 3.15/0.79  fof(f96,plain,(
% 3.15/0.79    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 3.15/0.79    inference(definition_unfolding,[],[f68,f63])).
% 3.15/0.79  fof(f68,plain,(
% 3.15/0.79    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 3.15/0.79    inference(cnf_transformation,[],[f2])).
% 3.15/0.79  fof(f2,axiom,(
% 3.15/0.79    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 3.15/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 3.15/0.79  fof(f793,plain,(
% 3.15/0.79    k2_relat_1(sK3) = k2_relat_1(k6_partfun1(sK0)) | (~spl4_11 | ~spl4_12)),
% 3.15/0.79    inference(superposition,[],[f96,f781])).
% 3.15/0.79  fof(f781,plain,(
% 3.15/0.79    k6_partfun1(sK0) = k6_partfun1(k2_relat_1(sK3)) | (~spl4_11 | ~spl4_12)),
% 3.15/0.79    inference(forward_demodulation,[],[f665,f333])).
% 3.15/0.79  fof(f333,plain,(
% 3.15/0.79    k6_partfun1(sK0) = k5_relat_1(k2_funct_1(sK3),sK3) | ~spl4_11),
% 3.15/0.79    inference(avatar_component_clause,[],[f331])).
% 3.15/0.79  fof(f331,plain,(
% 3.15/0.79    spl4_11 <=> k6_partfun1(sK0) = k5_relat_1(k2_funct_1(sK3),sK3)),
% 3.15/0.79    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 3.15/0.79  fof(f665,plain,(
% 3.15/0.79    k6_partfun1(k2_relat_1(sK3)) = k5_relat_1(k2_funct_1(sK3),sK3) | ~spl4_12),
% 3.15/0.79    inference(subsumption_resolution,[],[f664,f107])).
% 3.15/0.79  fof(f107,plain,(
% 3.15/0.79    v1_relat_1(sK3)),
% 3.15/0.79    inference(resolution,[],[f80,f56])).
% 3.15/0.79  fof(f56,plain,(
% 3.15/0.79    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 3.15/0.79    inference(cnf_transformation,[],[f49])).
% 3.15/0.79  fof(f664,plain,(
% 3.15/0.79    k6_partfun1(k2_relat_1(sK3)) = k5_relat_1(k2_funct_1(sK3),sK3) | ~v1_relat_1(sK3) | ~spl4_12),
% 3.15/0.79    inference(subsumption_resolution,[],[f657,f54])).
% 3.15/0.79  fof(f54,plain,(
% 3.15/0.79    v1_funct_1(sK3)),
% 3.15/0.79    inference(cnf_transformation,[],[f49])).
% 3.15/0.79  fof(f657,plain,(
% 3.15/0.79    k6_partfun1(k2_relat_1(sK3)) = k5_relat_1(k2_funct_1(sK3),sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl4_12),
% 3.15/0.79    inference(resolution,[],[f336,f100])).
% 3.15/0.79  fof(f336,plain,(
% 3.15/0.79    v2_funct_1(sK3) | ~spl4_12),
% 3.15/0.79    inference(avatar_component_clause,[],[f335])).
% 3.15/0.79  fof(f335,plain,(
% 3.15/0.79    spl4_12 <=> v2_funct_1(sK3)),
% 3.15/0.79    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 3.15/0.79  fof(f715,plain,(
% 3.15/0.79    k2_funct_1(sK3) = k5_relat_1(k6_partfun1(k2_relat_1(sK3)),k2_funct_1(sK3)) | ~spl4_12),
% 3.15/0.79    inference(backward_demodulation,[],[f405,f673])).
% 3.15/0.79  fof(f673,plain,(
% 3.15/0.79    k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3)) | ~spl4_12),
% 3.15/0.79    inference(subsumption_resolution,[],[f672,f107])).
% 3.15/0.79  fof(f672,plain,(
% 3.15/0.79    k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3)) | ~v1_relat_1(sK3) | ~spl4_12),
% 3.15/0.79    inference(subsumption_resolution,[],[f661,f54])).
% 3.15/0.79  fof(f661,plain,(
% 3.15/0.79    k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl4_12),
% 3.15/0.79    inference(resolution,[],[f336,f74])).
% 3.15/0.79  fof(f74,plain,(
% 3.15/0.79    ( ! [X0] : (~v2_funct_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.15/0.79    inference(cnf_transformation,[],[f29])).
% 3.15/0.79  fof(f29,plain,(
% 3.15/0.79    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.15/0.79    inference(flattening,[],[f28])).
% 3.15/0.79  fof(f28,plain,(
% 3.15/0.79    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.15/0.79    inference(ennf_transformation,[],[f7])).
% 3.15/0.79  fof(f7,axiom,(
% 3.15/0.79    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 3.15/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 3.15/0.79  fof(f405,plain,(
% 3.15/0.79    k2_funct_1(sK3) = k5_relat_1(k6_partfun1(k1_relat_1(k2_funct_1(sK3))),k2_funct_1(sK3))),
% 3.15/0.79    inference(subsumption_resolution,[],[f401,f107])).
% 3.15/0.79  fof(f401,plain,(
% 3.15/0.79    k2_funct_1(sK3) = k5_relat_1(k6_partfun1(k1_relat_1(k2_funct_1(sK3))),k2_funct_1(sK3)) | ~v1_relat_1(sK3)),
% 3.15/0.79    inference(resolution,[],[f114,f54])).
% 3.15/0.79  fof(f114,plain,(
% 3.15/0.79    ( ! [X0] : (~v1_funct_1(X0) | k2_funct_1(X0) = k5_relat_1(k6_partfun1(k1_relat_1(k2_funct_1(X0))),k2_funct_1(X0)) | ~v1_relat_1(X0)) )),
% 3.15/0.79    inference(resolution,[],[f99,f72])).
% 3.15/0.79  fof(f72,plain,(
% 3.15/0.79    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.15/0.79    inference(cnf_transformation,[],[f27])).
% 3.15/0.79  fof(f27,plain,(
% 3.15/0.79    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.15/0.79    inference(flattening,[],[f26])).
% 3.15/0.79  fof(f26,plain,(
% 3.15/0.79    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.15/0.79    inference(ennf_transformation,[],[f5])).
% 3.15/0.79  fof(f5,axiom,(
% 3.15/0.79    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 3.15/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 3.15/0.79  fof(f99,plain,(
% 3.15/0.79    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0) )),
% 3.15/0.79    inference(definition_unfolding,[],[f70,f63])).
% 3.15/0.79  fof(f70,plain,(
% 3.15/0.79    ( ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0)) )),
% 3.15/0.79    inference(cnf_transformation,[],[f24])).
% 3.15/0.79  fof(f24,plain,(
% 3.15/0.79    ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0))),
% 3.15/0.79    inference(ennf_transformation,[],[f3])).
% 3.15/0.79  fof(f3,axiom,(
% 3.15/0.79    ! [X0] : (v1_relat_1(X0) => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0)),
% 3.15/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).
% 3.15/0.79  fof(f1450,plain,(
% 3.15/0.79    k5_relat_1(sK2,k6_partfun1(sK1)) = k5_relat_1(k6_partfun1(sK0),k2_funct_1(sK3)) | ~spl4_13),
% 3.15/0.79    inference(forward_demodulation,[],[f1449,f617])).
% 3.15/0.79  fof(f617,plain,(
% 3.15/0.79    k6_partfun1(sK0) = k5_relat_1(sK2,sK3)),
% 3.15/0.79    inference(global_subsumption,[],[f590,f616])).
% 3.15/0.79  fof(f616,plain,(
% 3.15/0.79    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 3.15/0.79    inference(resolution,[],[f577,f180])).
% 3.15/0.79  fof(f180,plain,(
% 3.15/0.79    ( ! [X2,X3] : (~r2_relset_1(X2,X2,X3,k6_partfun1(X2)) | k6_partfun1(X2) = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))) )),
% 3.15/0.79    inference(resolution,[],[f88,f93])).
% 3.15/0.79  fof(f93,plain,(
% 3.15/0.79    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.15/0.79    inference(definition_unfolding,[],[f64,f63])).
% 3.15/0.79  fof(f64,plain,(
% 3.15/0.79    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.15/0.79    inference(cnf_transformation,[],[f12])).
% 3.15/0.79  fof(f12,axiom,(
% 3.15/0.79    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 3.15/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).
% 3.15/0.79  fof(f88,plain,(
% 3.15/0.79    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.15/0.79    inference(cnf_transformation,[],[f50])).
% 3.15/0.79  fof(f50,plain,(
% 3.15/0.79    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.15/0.79    inference(nnf_transformation,[],[f42])).
% 3.15/0.79  fof(f42,plain,(
% 3.15/0.79    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.15/0.79    inference(flattening,[],[f41])).
% 3.15/0.79  fof(f41,plain,(
% 3.15/0.79    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.15/0.79    inference(ennf_transformation,[],[f11])).
% 3.15/0.79  fof(f11,axiom,(
% 3.15/0.79    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 3.15/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 3.15/0.79  fof(f577,plain,(
% 3.15/0.79    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0))),
% 3.15/0.79    inference(backward_demodulation,[],[f58,f450])).
% 3.15/0.79  fof(f450,plain,(
% 3.15/0.79    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)),
% 3.15/0.79    inference(subsumption_resolution,[],[f447,f51])).
% 3.15/0.79  fof(f447,plain,(
% 3.15/0.79    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) | ~v1_funct_1(sK2)),
% 3.15/0.79    inference(resolution,[],[f190,f53])).
% 3.15/0.79  fof(f190,plain,(
% 3.15/0.79    ( ! [X4,X5,X3] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | k5_relat_1(X5,sK3) = k1_partfun1(X3,X4,sK1,sK0,X5,sK3) | ~v1_funct_1(X5)) )),
% 3.15/0.79    inference(subsumption_resolution,[],[f187,f54])).
% 3.15/0.79  fof(f187,plain,(
% 3.15/0.79    ( ! [X4,X5,X3] : (k5_relat_1(X5,sK3) = k1_partfun1(X3,X4,sK1,sK0,X5,sK3) | ~v1_funct_1(sK3) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_1(X5)) )),
% 3.15/0.79    inference(resolution,[],[f90,f56])).
% 3.15/0.79  fof(f90,plain,(
% 3.15/0.79    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.15/0.79    inference(cnf_transformation,[],[f44])).
% 3.15/0.79  fof(f44,plain,(
% 3.15/0.79    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.15/0.79    inference(flattening,[],[f43])).
% 3.15/0.79  fof(f43,plain,(
% 3.15/0.79    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.15/0.79    inference(ennf_transformation,[],[f14])).
% 3.15/0.79  fof(f14,axiom,(
% 3.15/0.79    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 3.15/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 3.15/0.79  fof(f58,plain,(
% 3.15/0.79    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 3.15/0.79    inference(cnf_transformation,[],[f49])).
% 3.15/0.79  fof(f590,plain,(
% 3.15/0.79    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 3.15/0.79    inference(subsumption_resolution,[],[f589,f51])).
% 3.15/0.79  fof(f589,plain,(
% 3.15/0.79    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK2)),
% 3.15/0.79    inference(subsumption_resolution,[],[f588,f53])).
% 3.15/0.79  fof(f588,plain,(
% 3.15/0.79    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2)),
% 3.15/0.79    inference(subsumption_resolution,[],[f587,f54])).
% 3.15/0.79  fof(f587,plain,(
% 3.15/0.79    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2)),
% 3.15/0.79    inference(subsumption_resolution,[],[f579,f56])).
% 3.15/0.79  fof(f579,plain,(
% 3.15/0.79    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2)),
% 3.15/0.79    inference(superposition,[],[f92,f450])).
% 3.15/0.79  fof(f92,plain,(
% 3.15/0.79    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.15/0.79    inference(cnf_transformation,[],[f46])).
% 3.15/0.79  fof(f46,plain,(
% 3.15/0.79    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.15/0.79    inference(flattening,[],[f45])).
% 3.15/0.79  fof(f45,plain,(
% 3.15/0.79    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.15/0.79    inference(ennf_transformation,[],[f13])).
% 3.15/0.79  fof(f13,axiom,(
% 3.15/0.79    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 3.15/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 3.15/0.79  fof(f1449,plain,(
% 3.15/0.79    k5_relat_1(sK2,k6_partfun1(sK1)) = k5_relat_1(k5_relat_1(sK2,sK3),k2_funct_1(sK3)) | ~spl4_13),
% 3.15/0.79    inference(forward_demodulation,[],[f1446,f346])).
% 3.15/0.79  fof(f1446,plain,(
% 3.15/0.79    k5_relat_1(k5_relat_1(sK2,sK3),k2_funct_1(sK3)) = k5_relat_1(sK2,k5_relat_1(sK3,k2_funct_1(sK3)))),
% 3.15/0.79    inference(resolution,[],[f1081,f107])).
% 3.15/0.79  fof(f1081,plain,(
% 3.15/0.79    ( ! [X15] : (~v1_relat_1(X15) | k5_relat_1(k5_relat_1(sK2,X15),k2_funct_1(sK3)) = k5_relat_1(sK2,k5_relat_1(X15,k2_funct_1(sK3)))) )),
% 3.15/0.79    inference(resolution,[],[f576,f106])).
% 3.15/0.79  fof(f576,plain,(
% 3.15/0.79    ( ! [X17,X18] : (~v1_relat_1(X18) | ~v1_relat_1(X17) | k5_relat_1(k5_relat_1(X18,X17),k2_funct_1(sK3)) = k5_relat_1(X18,k5_relat_1(X17,k2_funct_1(sK3)))) )),
% 3.15/0.79    inference(subsumption_resolution,[],[f571,f107])).
% 3.15/0.79  fof(f571,plain,(
% 3.15/0.79    ( ! [X17,X18] : (~v1_relat_1(X17) | ~v1_relat_1(X18) | k5_relat_1(k5_relat_1(X18,X17),k2_funct_1(sK3)) = k5_relat_1(X18,k5_relat_1(X17,k2_funct_1(sK3))) | ~v1_relat_1(sK3)) )),
% 3.15/0.79    inference(resolution,[],[f158,f54])).
% 3.15/0.79  fof(f158,plain,(
% 3.15/0.79    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0) | k5_relat_1(k5_relat_1(X0,X1),k2_funct_1(X2)) = k5_relat_1(X0,k5_relat_1(X1,k2_funct_1(X2))) | ~v1_relat_1(X2)) )),
% 3.15/0.79    inference(resolution,[],[f71,f72])).
% 3.15/0.79  fof(f71,plain,(
% 3.15/0.79    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.15/0.79    inference(cnf_transformation,[],[f25])).
% 3.15/0.79  fof(f25,plain,(
% 3.15/0.79    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.15/0.79    inference(ennf_transformation,[],[f1])).
% 3.15/0.79  fof(f1,axiom,(
% 3.15/0.79    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)))))),
% 3.15/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).
% 3.15/0.79  fof(f346,plain,(
% 3.15/0.79    k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~spl4_13),
% 3.15/0.79    inference(avatar_component_clause,[],[f344])).
% 3.15/0.79  fof(f344,plain,(
% 3.15/0.79    spl4_13 <=> k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))),
% 3.15/0.79    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 3.15/0.79  fof(f1418,plain,(
% 3.15/0.79    sK3 = k5_relat_1(k5_relat_1(sK3,sK2),k2_funct_1(sK2)) | (~spl4_11 | ~spl4_12)),
% 3.15/0.79    inference(forward_demodulation,[],[f1417,f788])).
% 3.15/0.79  fof(f788,plain,(
% 3.15/0.79    sK3 = k5_relat_1(sK3,k6_partfun1(sK0)) | (~spl4_11 | ~spl4_12)),
% 3.15/0.79    inference(backward_demodulation,[],[f112,f781])).
% 3.15/0.79  fof(f112,plain,(
% 3.15/0.79    sK3 = k5_relat_1(sK3,k6_partfun1(k2_relat_1(sK3)))),
% 3.15/0.79    inference(resolution,[],[f98,f107])).
% 3.15/0.79  fof(f1417,plain,(
% 3.15/0.79    k5_relat_1(sK3,k6_partfun1(sK0)) = k5_relat_1(k5_relat_1(sK3,sK2),k2_funct_1(sK2))),
% 3.15/0.79    inference(forward_demodulation,[],[f1413,f213])).
% 3.15/0.79  fof(f213,plain,(
% 3.15/0.79    k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 3.15/0.79    inference(subsumption_resolution,[],[f212,f51])).
% 3.15/0.79  fof(f212,plain,(
% 3.15/0.79    k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~v1_funct_1(sK2)),
% 3.15/0.79    inference(subsumption_resolution,[],[f211,f52])).
% 3.15/0.79  fof(f211,plain,(
% 3.15/0.79    k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 3.15/0.79    inference(subsumption_resolution,[],[f210,f53])).
% 3.15/0.79  fof(f210,plain,(
% 3.15/0.79    k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 3.15/0.79    inference(subsumption_resolution,[],[f209,f59])).
% 3.15/0.79  fof(f209,plain,(
% 3.15/0.79    ~v2_funct_1(sK2) | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 3.15/0.79    inference(subsumption_resolution,[],[f208,f61])).
% 3.15/0.79  fof(f208,plain,(
% 3.15/0.79    k1_xboole_0 = sK1 | ~v2_funct_1(sK2) | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 3.15/0.79    inference(trivial_inequality_removal,[],[f207])).
% 3.15/0.79  fof(f207,plain,(
% 3.15/0.79    sK1 != sK1 | k1_xboole_0 = sK1 | ~v2_funct_1(sK2) | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 3.15/0.79    inference(superposition,[],[f81,f57])).
% 3.15/0.79  fof(f81,plain,(
% 3.15/0.79    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.15/0.79    inference(cnf_transformation,[],[f36])).
% 3.15/0.79  fof(f1413,plain,(
% 3.15/0.79    k5_relat_1(k5_relat_1(sK3,sK2),k2_funct_1(sK2)) = k5_relat_1(sK3,k5_relat_1(sK2,k2_funct_1(sK2)))),
% 3.15/0.79    inference(resolution,[],[f1025,f106])).
% 3.15/0.79  fof(f1025,plain,(
% 3.15/0.79    ( ! [X15] : (~v1_relat_1(X15) | k5_relat_1(k5_relat_1(sK3,X15),k2_funct_1(sK2)) = k5_relat_1(sK3,k5_relat_1(X15,k2_funct_1(sK2)))) )),
% 3.15/0.79    inference(resolution,[],[f575,f107])).
% 3.15/0.79  fof(f575,plain,(
% 3.15/0.79    ( ! [X15,X16] : (~v1_relat_1(X16) | ~v1_relat_1(X15) | k5_relat_1(k5_relat_1(X16,X15),k2_funct_1(sK2)) = k5_relat_1(X16,k5_relat_1(X15,k2_funct_1(sK2)))) )),
% 3.15/0.79    inference(subsumption_resolution,[],[f570,f106])).
% 3.15/0.79  fof(f570,plain,(
% 3.15/0.79    ( ! [X15,X16] : (~v1_relat_1(X15) | ~v1_relat_1(X16) | k5_relat_1(k5_relat_1(X16,X15),k2_funct_1(sK2)) = k5_relat_1(X16,k5_relat_1(X15,k2_funct_1(sK2))) | ~v1_relat_1(sK2)) )),
% 3.15/0.79    inference(resolution,[],[f158,f51])).
% 3.15/0.79  fof(f404,plain,(
% 3.15/0.79    k2_funct_1(sK2) = k5_relat_1(k6_partfun1(sK1),k2_funct_1(sK2))),
% 3.15/0.79    inference(forward_demodulation,[],[f403,f314])).
% 3.15/0.79  fof(f314,plain,(
% 3.15/0.79    sK1 = k1_relat_1(k2_funct_1(sK2))),
% 3.15/0.79    inference(backward_demodulation,[],[f125,f286])).
% 3.15/0.79  fof(f286,plain,(
% 3.15/0.79    sK1 = k2_relat_1(sK2)),
% 3.15/0.79    inference(forward_demodulation,[],[f275,f96])).
% 3.15/0.79  fof(f275,plain,(
% 3.15/0.79    k2_relat_1(sK2) = k2_relat_1(k6_partfun1(sK1))),
% 3.15/0.79    inference(superposition,[],[f96,f270])).
% 3.15/0.79  fof(f125,plain,(
% 3.15/0.79    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))),
% 3.15/0.79    inference(subsumption_resolution,[],[f124,f106])).
% 3.15/0.79  fof(f124,plain,(
% 3.15/0.79    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 3.15/0.79    inference(subsumption_resolution,[],[f122,f51])).
% 3.15/0.79  fof(f122,plain,(
% 3.15/0.79    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 3.15/0.79    inference(resolution,[],[f74,f59])).
% 3.15/0.79  fof(f403,plain,(
% 3.15/0.79    k2_funct_1(sK2) = k5_relat_1(k6_partfun1(k1_relat_1(k2_funct_1(sK2))),k2_funct_1(sK2))),
% 3.15/0.79    inference(subsumption_resolution,[],[f400,f106])).
% 3.15/0.79  fof(f400,plain,(
% 3.15/0.79    k2_funct_1(sK2) = k5_relat_1(k6_partfun1(k1_relat_1(k2_funct_1(sK2))),k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 3.15/0.79    inference(resolution,[],[f114,f51])).
% 3.15/0.79  fof(f633,plain,(
% 3.15/0.79    spl4_12),
% 3.15/0.79    inference(avatar_contradiction_clause,[],[f632])).
% 3.15/0.79  fof(f632,plain,(
% 3.15/0.79    $false | spl4_12),
% 3.15/0.79    inference(subsumption_resolution,[],[f628,f94])).
% 3.15/0.79  fof(f94,plain,(
% 3.15/0.79    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 3.15/0.79    inference(definition_unfolding,[],[f66,f63])).
% 3.15/0.79  fof(f66,plain,(
% 3.15/0.79    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 3.15/0.79    inference(cnf_transformation,[],[f6])).
% 3.15/0.79  fof(f6,axiom,(
% 3.15/0.79    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 3.15/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).
% 3.15/0.79  fof(f628,plain,(
% 3.15/0.79    ~v2_funct_1(k6_partfun1(sK0)) | spl4_12),
% 3.15/0.79    inference(backward_demodulation,[],[f586,f617])).
% 3.15/0.79  fof(f586,plain,(
% 3.15/0.79    ~v2_funct_1(k5_relat_1(sK2,sK3)) | spl4_12),
% 3.15/0.79    inference(subsumption_resolution,[],[f585,f54])).
% 3.15/0.79  fof(f585,plain,(
% 3.15/0.79    ~v2_funct_1(k5_relat_1(sK2,sK3)) | ~v1_funct_1(sK3) | spl4_12),
% 3.15/0.79    inference(subsumption_resolution,[],[f584,f55])).
% 3.15/0.79  fof(f55,plain,(
% 3.15/0.79    v1_funct_2(sK3,sK1,sK0)),
% 3.15/0.79    inference(cnf_transformation,[],[f49])).
% 3.15/0.79  fof(f584,plain,(
% 3.15/0.79    ~v2_funct_1(k5_relat_1(sK2,sK3)) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | spl4_12),
% 3.15/0.79    inference(subsumption_resolution,[],[f583,f56])).
% 3.15/0.79  fof(f583,plain,(
% 3.15/0.79    ~v2_funct_1(k5_relat_1(sK2,sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | spl4_12),
% 3.15/0.79    inference(subsumption_resolution,[],[f582,f60])).
% 3.15/0.79  fof(f60,plain,(
% 3.15/0.79    k1_xboole_0 != sK0),
% 3.15/0.79    inference(cnf_transformation,[],[f49])).
% 3.15/0.79  fof(f582,plain,(
% 3.15/0.79    ~v2_funct_1(k5_relat_1(sK2,sK3)) | k1_xboole_0 = sK0 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | spl4_12),
% 3.15/0.79    inference(subsumption_resolution,[],[f578,f337])).
% 3.15/0.79  fof(f337,plain,(
% 3.15/0.79    ~v2_funct_1(sK3) | spl4_12),
% 3.15/0.79    inference(avatar_component_clause,[],[f335])).
% 3.15/0.79  fof(f578,plain,(
% 3.15/0.79    ~v2_funct_1(k5_relat_1(sK2,sK3)) | v2_funct_1(sK3) | k1_xboole_0 = sK0 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 3.15/0.79    inference(superposition,[],[f368,f450])).
% 3.15/0.79  fof(f368,plain,(
% 3.15/0.79    ( ! [X0,X1] : (~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) | v2_funct_1(X1) | k1_xboole_0 = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_2(X1,sK1,X0) | ~v1_funct_1(X1)) )),
% 3.15/0.79    inference(subsumption_resolution,[],[f367,f51])).
% 3.15/0.79  fof(f367,plain,(
% 3.15/0.79    ( ! [X0,X1] : (k1_xboole_0 = X0 | v2_funct_1(X1) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_2(X1,sK1,X0) | ~v1_funct_1(X1) | ~v1_funct_1(sK2)) )),
% 3.15/0.79    inference(subsumption_resolution,[],[f366,f52])).
% 3.15/0.79  fof(f366,plain,(
% 3.15/0.79    ( ! [X0,X1] : (k1_xboole_0 = X0 | v2_funct_1(X1) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_2(X1,sK1,X0) | ~v1_funct_1(X1) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) )),
% 3.15/0.79    inference(subsumption_resolution,[],[f365,f53])).
% 3.15/0.79  fof(f365,plain,(
% 3.15/0.79    ( ! [X0,X1] : (k1_xboole_0 = X0 | v2_funct_1(X1) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_2(X1,sK1,X0) | ~v1_funct_1(X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) )),
% 3.15/0.79    inference(trivial_inequality_removal,[],[f362])).
% 3.15/0.79  fof(f362,plain,(
% 3.15/0.79    ( ! [X0,X1] : (sK1 != sK1 | k1_xboole_0 = X0 | v2_funct_1(X1) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_2(X1,sK1,X0) | ~v1_funct_1(X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) )),
% 3.15/0.79    inference(superposition,[],[f86,f57])).
% 3.15/0.79  fof(f86,plain,(
% 3.15/0.79    ( ! [X4,X2,X0,X3,X1] : (k2_relset_1(X0,X1,X3) != X1 | k1_xboole_0 = X2 | v2_funct_1(X4) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 3.15/0.79    inference(cnf_transformation,[],[f40])).
% 3.15/0.79  fof(f40,plain,(
% 3.15/0.79    ! [X0,X1,X2,X3] : (! [X4] : ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 3.15/0.79    inference(flattening,[],[f39])).
% 3.15/0.79  fof(f39,plain,(
% 3.15/0.79    ! [X0,X1,X2,X3] : (! [X4] : ((((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | (k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 3.15/0.79    inference(ennf_transformation,[],[f17])).
% 3.15/0.79  fof(f17,axiom,(
% 3.15/0.79    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) => ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 3.15/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_funct_2)).
% 3.15/0.79  fof(f347,plain,(
% 3.15/0.79    spl4_13 | ~spl4_12),
% 3.15/0.79    inference(avatar_split_clause,[],[f342,f335,f344])).
% 3.15/0.79  fof(f342,plain,(
% 3.15/0.79    ~v2_funct_1(sK3) | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))),
% 3.15/0.79    inference(subsumption_resolution,[],[f341,f54])).
% 3.15/0.79  fof(f341,plain,(
% 3.15/0.79    ~v2_funct_1(sK3) | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~v1_funct_1(sK3)),
% 3.15/0.79    inference(subsumption_resolution,[],[f340,f55])).
% 3.15/0.79  fof(f340,plain,(
% 3.15/0.79    ~v2_funct_1(sK3) | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 3.15/0.79    inference(subsumption_resolution,[],[f339,f56])).
% 3.15/0.79  fof(f339,plain,(
% 3.15/0.79    ~v2_funct_1(sK3) | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 3.15/0.79    inference(subsumption_resolution,[],[f324,f60])).
% 3.15/0.79  fof(f324,plain,(
% 3.15/0.79    k1_xboole_0 = sK0 | ~v2_funct_1(sK3) | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 3.15/0.79    inference(trivial_inequality_removal,[],[f323])).
% 3.15/0.79  fof(f323,plain,(
% 3.15/0.79    sK0 != sK0 | k1_xboole_0 = sK0 | ~v2_funct_1(sK3) | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 3.15/0.79    inference(superposition,[],[f81,f321])).
% 3.15/0.79  fof(f321,plain,(
% 3.15/0.79    sK0 = k2_relset_1(sK1,sK0,sK3)),
% 3.15/0.79    inference(subsumption_resolution,[],[f320,f54])).
% 3.15/0.79  fof(f320,plain,(
% 3.15/0.79    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_1(sK3)),
% 3.15/0.79    inference(subsumption_resolution,[],[f319,f55])).
% 3.15/0.79  fof(f319,plain,(
% 3.15/0.79    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 3.15/0.79    inference(subsumption_resolution,[],[f318,f56])).
% 3.15/0.79  fof(f318,plain,(
% 3.15/0.79    sK0 = k2_relset_1(sK1,sK0,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 3.15/0.79    inference(subsumption_resolution,[],[f317,f51])).
% 3.15/0.79  fof(f317,plain,(
% 3.15/0.79    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 3.15/0.79    inference(subsumption_resolution,[],[f316,f52])).
% 3.15/0.79  fof(f316,plain,(
% 3.15/0.79    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 3.15/0.79    inference(subsumption_resolution,[],[f315,f53])).
% 3.15/0.79  fof(f315,plain,(
% 3.15/0.79    sK0 = k2_relset_1(sK1,sK0,sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 3.15/0.79    inference(resolution,[],[f83,f58])).
% 3.15/0.79  fof(f83,plain,(
% 3.15/0.79    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | k2_relset_1(X0,X1,X2) = X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.15/0.79    inference(cnf_transformation,[],[f38])).
% 3.15/0.79  fof(f38,plain,(
% 3.15/0.79    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.15/0.79    inference(flattening,[],[f37])).
% 3.15/0.79  fof(f37,plain,(
% 3.15/0.79    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.15/0.79    inference(ennf_transformation,[],[f16])).
% 3.15/0.79  fof(f16,axiom,(
% 3.15/0.79    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 3.15/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_funct_2)).
% 3.15/0.79  fof(f338,plain,(
% 3.15/0.79    spl4_11 | ~spl4_12),
% 3.15/0.79    inference(avatar_split_clause,[],[f329,f335,f331])).
% 3.15/0.79  fof(f329,plain,(
% 3.15/0.79    ~v2_funct_1(sK3) | k6_partfun1(sK0) = k5_relat_1(k2_funct_1(sK3),sK3)),
% 3.15/0.79    inference(subsumption_resolution,[],[f328,f54])).
% 3.15/0.79  fof(f328,plain,(
% 3.15/0.79    ~v2_funct_1(sK3) | k6_partfun1(sK0) = k5_relat_1(k2_funct_1(sK3),sK3) | ~v1_funct_1(sK3)),
% 3.15/0.79    inference(subsumption_resolution,[],[f327,f55])).
% 3.15/0.79  fof(f327,plain,(
% 3.15/0.79    ~v2_funct_1(sK3) | k6_partfun1(sK0) = k5_relat_1(k2_funct_1(sK3),sK3) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 3.15/0.79    inference(subsumption_resolution,[],[f326,f56])).
% 3.15/0.79  fof(f326,plain,(
% 3.15/0.79    ~v2_funct_1(sK3) | k6_partfun1(sK0) = k5_relat_1(k2_funct_1(sK3),sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 3.15/0.79    inference(subsumption_resolution,[],[f325,f60])).
% 3.15/0.79  fof(f325,plain,(
% 3.15/0.79    k1_xboole_0 = sK0 | ~v2_funct_1(sK3) | k6_partfun1(sK0) = k5_relat_1(k2_funct_1(sK3),sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 3.15/0.79    inference(trivial_inequality_removal,[],[f322])).
% 3.15/0.79  fof(f322,plain,(
% 3.15/0.79    sK0 != sK0 | k1_xboole_0 = sK0 | ~v2_funct_1(sK3) | k6_partfun1(sK0) = k5_relat_1(k2_funct_1(sK3),sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 3.15/0.79    inference(superposition,[],[f82,f321])).
% 3.15/0.79  % SZS output end Proof for theBenchmark
% 3.15/0.79  % (26608)------------------------------
% 3.15/0.79  % (26608)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.15/0.79  % (26608)Termination reason: Refutation
% 3.15/0.79  
% 3.15/0.79  % (26608)Memory used [KB]: 12025
% 3.15/0.79  % (26608)Time elapsed: 0.340 s
% 3.15/0.79  % (26608)------------------------------
% 3.15/0.79  % (26608)------------------------------
% 3.15/0.80  % (26601)Success in time 0.431 s
%------------------------------------------------------------------------------
